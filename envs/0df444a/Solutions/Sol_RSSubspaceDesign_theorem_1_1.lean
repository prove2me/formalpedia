-- Prove2me | solution 1 for RSSubspaceDesign.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:31:11.889152+00:00
-- url     : https://prove2.me/submissions/f51291bc-25e9-4b5a-8a1e-b8a5d2654707

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_decK
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField
import Definitions.Def_RSSubspaceDesign_IsEffective
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_RSSubspaceDesign_theorem_4_2
import Theorems.Thm_RSSubspaceDesign_lemma_4_5


-- ===================== Alg_defs.lean

/-!
# The explicit construction as concrete list functions

Input: a prime `p`, the coefficient list `fc` of a monic irreducible `f ∈ 𝔽_p[Y]`
(`fc = [f₀, …, f_{df}]`, `f_{df} = 1`), and `n`.

* `K = 𝔽_p[Y]/(f)` elements: lists of `df` residues `< p` (power basis `1, Y, …, Y^{df-1}`).
* `K[X]` polynomials: lists of `K` elements (coefficient of `X^0` first).
* `F = K[X]/(h)` elements: lists of `m` `K`-elements (`m = deg h`).

Parameters fixed before the input: `g`, prime lists `Ps`, `Qs` (length `g`), `r`, and
`R = 2^r`; the extension degree is `m = ∏ Ps[i] * Qs[i]`.
-/

namespace RSSDAlg

/-! ## Arithmetic in `𝔽_p[Y]` and `K = 𝔽_p[Y]/(f)` -/

/-- degree of `f` -/
def dg (fc : List ℕ) : ℕ := fc.length - 1

/-- truncate/pad a list to length `d` with zeros -/
def padTo {α : Type} (z : α) (d : ℕ) (l : List α) : List α :=
  (l ++ List.replicate (d - l.length) z).take d

def kZero (d : ℕ) : List ℕ := List.replicate d 0
def kOne (d : ℕ) : List ℕ := padTo 0 d [1]

def kAdd (p : ℕ) (a b : List ℕ) : List ℕ := List.zipWith (fun x y => (x + y) % p) a b
def kSub (p : ℕ) (a b : List ℕ) : List ℕ := List.zipWith (fun x y => (x + (p - y % p)) % p) a b

/-- schoolbook product of coefficient lists over `𝔽_p`, length `|a|+|b|-1` -/
def zMulRaw (p : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range (a.length + b.length - 1)).map fun k =>
    ((List.range (k + 1)).foldl (fun acc i => acc + a.getD i 0 * b.getD (k - i) 0) 0) % p

/-- one reduction step by the monic `fc`: drop the top coefficient `t` of `c` after
subtracting `t · Y^s · f` (`s = |c| - |fc|`). -/
def zRedStep (p : ℕ) (fc : List ℕ) (c : List ℕ) : List ℕ :=
  let t := c.getLastD 0
  let s := c.length - fc.length
  (c.dropLast).mapIdx fun i x =>
    if s ≤ i then (x + (p - (t * fc.getD (i - s) 0) % p)) % p else x

/-- reduce modulo the monic `fc` down to length `dg fc` -/
def zMod (p : ℕ) (fc : List ℕ) (c : List ℕ) : List ℕ :=
  padTo 0 (dg fc) (Nat.iterate (zRedStep p fc) (c.length - dg fc) c)

def kMul (p : ℕ) (fc : List ℕ) (a b : List ℕ) : List ℕ := zMod p fc (zMulRaw p a b)

/-! ## Polynomials over `K` and `F = K[X]/(h)` -/

def kpAdd (p : ℕ) (a b : List (List ℕ)) : List (List ℕ) := List.zipWith (kAdd p) a b

/-- schoolbook product over `K`, length `|a|+|b|-1` -/
def kpMulRaw (p : ℕ) (fc : List ℕ) (a b : List (List ℕ)) : List (List ℕ) :=
  (List.range (a.length + b.length - 1)).map fun k =>
    (List.range (k + 1)).foldl
      (fun acc i => kAdd p acc (kMul p fc (a.getD i (kZero (dg fc))) (b.getD (k - i) (kZero (dg fc)))))
      (kZero (dg fc))

/-- one reduction step by the monic `g ∈ K[X]` -/
def kpRedStep (p : ℕ) (fc : List ℕ) (g : List (List ℕ)) (c : List (List ℕ)) : List (List ℕ) :=
  let t := c.getLastD (kZero (dg fc))
  let s := c.length - g.length
  (c.dropLast).mapIdx fun i x =>
    if s ≤ i then kSub p x (kMul p fc t (g.getD (i - s) (kZero (dg fc)))) else x

/-- reduce modulo the monic `g` down to length `|g| - 1` -/
def kpMod (p : ℕ) (fc : List ℕ) (g : List (List ℕ)) (c : List (List ℕ)) : List (List ℕ) :=
  padTo (kZero (dg fc)) (g.length - 1) (Nat.iterate (kpRedStep p fc g) (c.length - (g.length - 1)) c)

def kpIsZero (c : List (List ℕ)) : Bool := c.all fun a => a.all fun x => x == 0

/-- multiplication in `F = K[X]/(h)` (`hc` monic of length `m+1`) -/
def fMul (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (x y : List (List ℕ)) : List (List ℕ) :=
  kpMod p fc hc (kpMulRaw p fc x y)

def fOne (fc : List ℕ) (hc : List (List ℕ)) : List (List ℕ) :=
  padTo (kZero (dg fc)) (hc.length - 1) [kOne (dg fc)]

def fZero (fc : List ℕ) (hc : List (List ℕ)) : List (List ℕ) :=
  List.replicate (hc.length - 1) (kZero (dg fc))

/-- the constant `c ∈ K` as an element of `F` -/
def fEmbed (fc : List ℕ) (hc : List (List ℕ)) (c : List ℕ) : List (List ℕ) :=
  padTo (kZero (dg fc)) (hc.length - 1) [c]

/-- `x^e` by square-and-multiply over the binary digits of `e` (most significant first) -/
def fPow (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (x : List (List ℕ)) (e : ℕ) :
    List (List ℕ) :=
  (Nat.bits e).reverse.foldl
    (fun acc b => let a2 := fMul p fc hc acc acc; if b then fMul p fc hc a2 x else a2)
    (fOne fc hc)

/-! ## Enumerations -/

/-- the `K`-element with base-`p` digits of `j` -/
def kOfIdx (p d j : ℕ) : List ℕ := (List.range d).map fun i => j / p ^ i % p

/-- the `K`-polynomial of length `len` whose coefficients have indices the base-`p^df` digits of `j` -/
def kpOfIdx (p d len j : ℕ) : List (List ℕ) :=
  (List.range len).map fun l => kOfIdx p d (j / (p ^ d) ^ l % p ^ d)

/-- the monic polynomial of degree `deg` with lower coefficients indexed by `j` -/
def monicOfIdx (p d deg j : ℕ) : List (List ℕ) := kpOfIdx p d deg j ++ [kOne d]

/-! ## Checks -/

/-- `J`-th trial divisor test for irreducibility of the monic `hc` of degree `m`:
for `d = J / Q^(m-1) + 1 < m`, the `J % Q^(m-1)`-th monic divisor candidate of degree `d`
must not divide `hc`. -/
def irredTest (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (J : ℕ) : Bool :=
  let df := dg fc
  let m := hc.length - 1
  let D := (p ^ df) ^ (m - 1)
  let d := J / D + 1
  if d < m then !(kpIsZero (kpMod p fc (monicOfIdx p df d (J % D % (p ^ df) ^ d)) hc)) else true

/-- number of trial divisors -/
def irredBound (p : ℕ) (fc : List ℕ) (m : ℕ) : ℕ := (m - 1) * (p ^ dg fc) ^ (m - 1)

def isIrred (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) : Bool :=
  (List.range (irredBound p fc (hc.length - 1))).all (irredTest p fc hc)

/-- `x` lies in the degree-`e` subfield and `x^e ∉ K` -/
def subfieldTest (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (e : ℕ) (x : List (List ℕ)) : Bool :=
  let Q := p ^ dg fc
  let y := fPow p fc hc x e
  (fPow p fc hc x (Q ^ e) == x) && !(fPow p fc hc y Q == y)

/-- base-`B` digits (least significant first), `len` of them -/
def digits (B len j : ℕ) : List ℕ := (List.range len).map fun i => j / B ^ i % B

def strictInc : List ℕ → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

/-- the `J`-th sparse polynomial test: exponents = `R` base-`E` digits of `J / Q^R`,
coefficients = `R` base-`Q` digits of `J % Q^R` (as `K`-indices); if the exponents are
strictly increasing and some coefficient is nonzero then `∑ c_t x^{e_t} ≠ 0`. -/
def sparseTest (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (R E : ℕ) (x : List (List ℕ))
    (J : ℕ) : Bool :=
  let Q := p ^ dg fc
  let es := digits E R (J / Q ^ R)
  let cs := digits Q R (J % Q ^ R)
  if strictInc es && cs.any (fun c => c != 0) then
    !(kpIsZero ((List.range R).foldl
      (fun acc t => kpAdd p acc (fMul p fc hc (fEmbed fc hc (kOfIdx p (dg fc) (cs.getD t 0)))
        (fPow p fc hc x (es.getD t 0)))) (fZero fc hc)))
  else true

def sparseBound (p : ℕ) (fc : List ℕ) (R E : ℕ) : ℕ := E ^ R * (p ^ dg fc) ^ R

def sparseOK (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (R E : ℕ) (x : List (List ℕ)) : Bool :=
  (List.range (sparseBound p fc R E)).all (sparseTest p fc hc R E x)

/-! ## Searches -/

/-- least `j < N` with `test j`, or `N` -/
def findBelow (test : ℕ → Bool) (N : ℕ) : ℕ := ((List.range N).find? test).getD N

/-- the field: first monic irreducible of degree `m` -/
def hSearch (p : ℕ) (fc : List ℕ) (m : ℕ) : List (List ℕ) :=
  monicOfIdx p (dg fc) m
    (findBelow (fun j => isIrred p fc (monicOfIdx p (dg fc) m j)) ((p ^ dg fc) ^ m))

def fOfIdx (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (j : ℕ) : List (List ℕ) :=
  kpOfIdx p (dg fc) (hc.length - 1) j

def gamSearch (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (e : ℕ) : List (List ℕ) :=
  fOfIdx p fc hc (findBelow (fun j => subfieldTest p fc hc e (fOfIdx p fc hc j))
    ((p ^ dg fc) ^ (hc.length - 1)))

def delSearch (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (e R E : ℕ) : List (List ℕ) :=
  fOfIdx p fc hc (findBelow (fun j => subfieldTest p fc hc e (fOfIdx p fc hc j) &&
      sparseOK p fc hc R E (fOfIdx p fc hc j))
    ((p ^ dg fc) ^ (hc.length - 1)))

/-! ## The construction -/

structure Params where
  g : ℕ
  r : ℕ
  Ps : List ℕ
  Qs : List ℕ

def Params.m (P : Params) : ℕ := (List.zipWith (· * ·) P.Ps P.Qs).prod

/-- block size `⌈n/g⌉` -/
def blk (g n : ℕ) : ℕ := (n + g - 1) / g

/-- the `k`-th point: `c_k · γ_i · δ_i` with `i = k / B`, `c_k` the `(k % B + 1)`-th element of `K` -/
def point (p : ℕ) (fc : List ℕ) (hc : List (List ℕ)) (B : ℕ)
    (gams dels : List (List (List ℕ))) (k : ℕ) : List (List ℕ) :=
  fMul p fc hc (fEmbed fc hc (kOfIdx p (dg fc) (k % B + 1)))
    (fMul p fc hc (gams.getD (k / B) []) (dels.getD (k / B) []))

/-- the output `(h, points)` -/
def construct (P : Params) (p : ℕ) (fc : List ℕ) (n : ℕ) :
    List (List ℕ) × List (List (List ℕ)) :=
  let hc := hSearch p fc P.m
  let gams := P.Ps.map fun e => gamSearch p fc hc e
  let dels := P.Qs.map fun e => delSearch p fc hc e (2 ^ P.r) (n * P.r)
  (hc, (List.range n).map (point p fc hc (blk P.g n) gams dels))

end RSSDAlg



-- ===================== Alg_prims.lean

open Polynomial RSSubspaceDesign

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace RSSDAlg

/-- the coefficient list of `f` -/
noncomputable def fcOf {p : ℕ} (f : (ZMod p)[X]) : List ℕ :=
  (List.range (f.natDegree + 1)).map fun i => (f.coeff i).val

def IsK (p d : ℕ) (a : List ℕ) : Prop := a.length = d ∧ ∀ x ∈ a, x < p

/-- decoding into `F = AdjoinRoot h`, `h = decPoly p f hc` -/
noncomputable abbrev decF (p : ℕ) (f : (ZMod p)[X]) (hc x : List (List ℕ)) :
    AdjoinRoot (decPoly p f hc) :=
  AdjoinRoot.mk (decPoly p f hc) (decPoly p f x)

/-! ## Helper lemmas (prefix `ap_`) -/

section APGeneric

theorem ap_zipWith_getD {α β γ : Type} (g : α → β → γ) (a : List α) (b : List β) (da : α) (db : β)
    (d : γ) (hd : g da db = d) (h : a.length = b.length) (k : ℕ) :
    (List.zipWith g a b).getD k d = g (a.getD k da) (b.getD k db) := by
  by_cases hk : k < a.length
  · rw [List.getD_eq_getElem _ _ (by simp [h]; omega), List.getD_eq_getElem _ _ hk,
      List.getD_eq_getElem _ _ (h ▸ hk)]
    simp
  · rw [List.getD_eq_default _ _ (by simp [h] at hk ⊢; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega), hd]

theorem ap_getD_mem {α : Type} (l : List α) (k : ℕ) (z : α) : l.getD k z ∈ l ∨ l.getD k z = z := by
  by_cases hk : k < l.length
  · left; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  · right; exact List.getD_eq_default _ _ (by omega)

theorem ap_padTo_length {α : Type} (z : α) (d : ℕ) (l : List α) : (padTo z d l).length = d := by
  unfold padTo; simp; omega

theorem ap_padTo_getD {α : Type} (z : α) (d : ℕ) (l : List α) (hl : l.length ≤ d) (k : ℕ) :
    (padTo z d l).getD k z = l.getD k z := by
  unfold padTo
  rw [List.take_of_length_le (by simp; omega)]
  by_cases hk : k < l.length
  · rw [List.getD_append _ _ _ _ hk]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default l _ (by omega)]
    by_cases hk' : k - l.length < d - l.length
    · rw [List.getD_replicate _ hk']
    · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem ap_padTo_mem {α : Type} (z : α) (d : ℕ) (l : List α) (x : α) (hx : x ∈ padTo z d l) :
    x ∈ l ∨ x = z := by
  unfold padTo at hx
  rcases List.mem_append.1 (List.mem_of_mem_take hx) with h | h
  · exact Or.inl h
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem ap_getD_map_range {α : Type} (g : ℕ → α) (n k : ℕ) (d : α) :
    ((List.range n).map g).getD k d = if k < n then g k else d := by
  split_ifs with hk
  · rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem ap_getLastD_eq {α : Type} (l : List α) (z : α) : l.getLastD z = l.getD (l.length - 1) z := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

theorem ap_sumFin_coeff {R : Type*} [Semiring R] {α : Type} (l : List α) (g : α → R) (d : α)
    (hd : g d = 0) (k : ℕ) :
    (∑ i : Fin l.length, C (g (l.get i)) * X ^ (i : ℕ)).coeff k = g (l.getD k d) := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hk : k < l.length
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · rw [List.getD_eq_getElem _ _ hk]; simp
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; ext; exact h.symm
    · simp
  · rw [List.getD_eq_default _ _ (by omega), hd]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h; have := i.2; omega

theorem ap_foldl_range_sum (g : ℕ → ℕ) (n a : ℕ) :
    (List.range n).foldl (fun acc i => acc + g i) a = a + ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp [add_assoc]

/-! base-`B` digits -/

theorem ap_digits_succ (B d j : ℕ) : digits B (d + 1) j = j % B :: digits B d (j / B) := by
  unfold digits
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, pow_zero, Nat.div_one, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  simp [Function.comp, pow_succ', Nat.div_div_eq_div_mul]

theorem ap_digits_inj (B : ℕ) (hB : 0 < B) :
    ∀ d j j', j < B ^ d → j' < B ^ d → digits B d j = digits B d j' → j = j' := by
  intro d
  induction d with
  | zero => intro j j' hj hj' _; simp at hj hj'; omega
  | succ d ih =>
    intro j j' hj hj' h
    rw [ap_digits_succ, ap_digits_succ, List.cons.injEq] at h
    have h1 : j / B = j' / B := ih _ _ (by rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]; exact hj)
      (by rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]; exact hj') h.2
    rw [← Nat.div_add_mod j B, ← Nat.div_add_mod j' B, h1, h.1]

theorem ap_digits_surj (B : ℕ) (hB : 0 < B) :
    ∀ w : List ℕ, (∀ x ∈ w, x < B) → ∃ j < B ^ w.length, digits B w.length j = w := by
  intro w
  induction w with
  | nil => intro _; exact ⟨0, by simp, by simp [digits]⟩
  | cons x w ih =>
    intro hw
    obtain ⟨j', hj', hd⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hx : x < B := hw x (by simp)
    refine ⟨x + B * j', ?_, ?_⟩
    · rw [List.length_cons, pow_succ']
      have : j' + 1 ≤ B ^ w.length := hj'
      calc x + B * j' < B + B * j' := by omega
        _ = B * (j' + 1) := by ring
        _ ≤ B * B ^ w.length := Nat.mul_le_mul_left _ this
    · rw [List.length_cons, ap_digits_succ, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx,
        zero_add, hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

end APGeneric

section APK

theorem ap_ppos (p : ℕ) [Fact p.Prime] : 0 < p := (Fact.out : p.Prime).pos

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}

noncomputable def ap_zP (p : ℕ) (c : List ℕ) : (ZMod p)[X] :=
  ∑ i : Fin c.length, C ((c.get i : ℕ) : ZMod p) * X ^ (i : ℕ)

theorem ap_decK_eq (c : List ℕ) : decK p f c = AdjoinRoot.mk f (ap_zP p c) := rfl

theorem ap_zP_coeff (c : List ℕ) (k : ℕ) : (ap_zP p c).coeff k = ((c.getD k 0 : ℕ) : ZMod p) :=
  ap_sumFin_coeff c (fun x : ℕ => (x : ZMod p)) 0 (by simp) k

theorem ap_zP_degree_lt (c : List ℕ) : (ap_zP p c).degree < c.length := by
  rw [degree_lt_iff_coeff_zero]; intro m hm
  rw [ap_zP_coeff, List.getD_eq_default _ _ hm]; simp

theorem ap_decK_nil : decK p f [] = 0 := by simp [decK]

theorem ap_fcOf_length : (fcOf f).length = f.natDegree + 1 := by simp [fcOf]

theorem ap_dg_fcOf : dg (fcOf f) = f.natDegree := by simp [dg, ap_fcOf_length]

theorem ap_fcOf_getD (k : ℕ) : (((fcOf f).getD k 0 : ℕ) : ZMod p) = f.coeff k := by
  unfold fcOf
  rw [ap_getD_map_range]
  split_ifs with hk
  · simp [ZMod.natCast_zmod_val]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp

theorem ap_zP_fcOf : ap_zP p (fcOf f) = f := by
  ext k; rw [ap_zP_coeff, ap_fcOf_getD]

theorem ap_cast_add (x y : ℕ) : (((x + y) % p : ℕ) : ZMod p) = x + y := by
  rw [ZMod.natCast_mod]; push_cast; ring

theorem ap_cast_sub (x y : ℕ) : (((x + (p - y % p)) % p : ℕ) : ZMod p) = x - y := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ (ap_ppos p)).le, ZMod.natCast_self,
    ZMod.natCast_mod]; ring

theorem ap_kAdd_spec {d : ℕ} {a b : List ℕ} (ha : IsK p d a) (hb : IsK p d b) :
    IsK p d (kAdd p a b) ∧ decK p f (kAdd p a b) = decK p f a + decK p f b := by
  have hl : a.length = b.length := ha.1.trans hb.1.symm
  refine ⟨⟨by simp [kAdd, ha.1, hb.1], ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [kAdd, List.getElem_zipWith]; exact Nat.mod_lt _ (ap_ppos p)
  · rw [ap_decK_eq, ap_decK_eq, ap_decK_eq, ← map_add]
    congr 1; ext k
    rw [coeff_add, ap_zP_coeff, ap_zP_coeff, ap_zP_coeff, kAdd,
      ap_zipWith_getD _ a b 0 0 0 (by simp) hl, ap_cast_add]

theorem ap_kSub_spec {d : ℕ} {a b : List ℕ} (ha : IsK p d a) (hb : IsK p d b) :
    IsK p d (kSub p a b) ∧ decK p f (kSub p a b) = decK p f a - decK p f b := by
  have hl : a.length = b.length := ha.1.trans hb.1.symm
  refine ⟨⟨by simp [kSub, ha.1, hb.1], ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [kSub, List.getElem_zipWith]; exact Nat.mod_lt _ (ap_ppos p)
  · rw [ap_decK_eq, ap_decK_eq, ap_decK_eq, ← map_sub]
    congr 1; ext k
    rw [coeff_sub, ap_zP_coeff, ap_zP_coeff, ap_zP_coeff, kSub,
      ap_zipWith_getD _ a b 0 0 0 (by simp) hl, ap_cast_sub]

theorem ap_zMulRaw_getD (a b : List ℕ) (k : ℕ) :
    (zMulRaw p a b).getD k 0 = (∑ i ∈ Finset.range (k+1), a.getD i 0 * b.getD (k - i) 0) % p := by
  unfold zMulRaw
  rw [ap_getD_map_range]
  split_ifs with hk
  · rw [ap_foldl_range_sum, zero_add]
  · rw [Finset.sum_eq_zero]
    · simp
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases hia : i < a.length
    · rw [List.getD_eq_default b _ (by omega)]; simp
    · rw [List.getD_eq_default a _ (by omega)]; simp

theorem ap_zP_zMulRaw (a b : List ℕ) : ap_zP p (zMulRaw p a b) = ap_zP p a * ap_zP p b := by
  ext k
  rw [ap_zP_coeff, ap_zMulRaw_getD, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [ap_zP_coeff]
  rw [ZMod.natCast_mod]; push_cast; rfl

theorem ap_zRedStep_length (fc c : List ℕ) : (zRedStep p fc c).length = c.length - 1 := by
  simp [zRedStep]

theorem ap_zRedStep_getD (fc c : List ℕ) (i : ℕ) (hi : i < c.length - 1) :
    (zRedStep p fc c).getD i 0 = if c.length - fc.length ≤ i then
      (c.getD i 0 + (p - (c.getLastD 0 * fc.getD (i - (c.length - fc.length)) 0) % p)) % p
      else c.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [ap_zRedStep_length]; exact hi),
    List.getD_eq_getElem _ _ (by omega : i < c.length)]
  simp only [zRedStep, List.getElem_mapIdx, List.getElem_dropLast]

theorem ap_zP_zRedStep (hf : f.Monic) (c : List ℕ) (hc : f.natDegree + 1 ≤ c.length) :
    ap_zP p (zRedStep p (fcOf f) c) = ap_zP p c -
      C ((c.getLastD 0 : ℕ) : ZMod p) * f * X ^ (c.length - (f.natDegree + 1)) := by
  ext i
  rw [coeff_sub, coeff_mul_X_pow', coeff_C_mul, ap_zP_coeff, ap_zP_coeff]
  by_cases hi : i < c.length - 1
  · rw [ap_zRedStep_getD _ _ _ hi]
    simp only [ap_fcOf_length]
    split_ifs with h1
    · rw [ap_cast_sub]; push_cast; rw [ap_fcOf_getD]
    · simp
  · rw [List.getD_eq_default _ _ (by rw [ap_zRedStep_length]; omega)]
    rw [if_pos (by omega), ap_getLastD_eq]
    by_cases hi' : i = c.length - 1
    · subst hi'
      rw [show c.length - 1 - (c.length - (f.natDegree+1)) = f.natDegree by omega,
        hf.coeff_natDegree]; simp
    · rw [List.getD_eq_default c _ (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]; simp

theorem ap_zRedStep_lt (fc c : List ℕ) (hc : ∀ x ∈ c, x < p) : ∀ x ∈ zRedStep p fc c, x < p := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [← List.getD_eq_getElem _ 0 hi, ap_zRedStep_getD _ _ _ (by rw [ap_zRedStep_length] at hi; omega)]
  split_ifs
  · exact Nat.mod_lt _ (ap_ppos p)
  · rcases ap_getD_mem c i 0 with h | h
    · exact hc _ h
    · rw [h]; exact ap_ppos p

theorem ap_zRed_iter (hf : f.Monic) (n : ℕ) : ∀ c : List ℕ, f.natDegree + n ≤ c.length →
    (∀ x ∈ c, x < p) →
    ((zRedStep p (fcOf f))^[n] c).length = c.length - n ∧
    (∀ x ∈ (zRedStep p (fcOf f))^[n] c, x < p) ∧
    AdjoinRoot.mk f (ap_zP p ((zRedStep p (fcOf f))^[n] c)) = AdjoinRoot.mk f (ap_zP p c) := by
  induction n with
  | zero => intro c _ hc; simpa using hc
  | succ n ih =>
    intro c hlen hc
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3⟩ := ih (zRedStep p (fcOf f) c) (by rw [ap_zRedStep_length]; omega)
      (ap_zRedStep_lt _ c hc)
    refine ⟨by rw [h1, ap_zRedStep_length]; omega, h2, ?_⟩
    rw [h3, ap_zP_zRedStep hf c (by omega), AdjoinRoot.mk_eq_mk]
    exact ⟨-(C ((c.getLastD 0 : ℕ) : ZMod p) * X ^ (c.length - (f.natDegree + 1))), by ring⟩

theorem ap_zP_padTo (d : ℕ) (l : List ℕ) (hl : l.length ≤ d) : ap_zP p (padTo 0 d l) = ap_zP p l := by
  ext k; rw [ap_zP_coeff, ap_zP_coeff, ap_padTo_getD _ _ _ hl]

theorem ap_isK_padTo (d : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < p) : IsK p d (padTo 0 d l) :=
  ⟨ap_padTo_length _ _ _, fun x hx =>
    (ap_padTo_mem _ _ _ _ hx).elim (hl x) (fun h => h ▸ ap_ppos p)⟩

theorem ap_zMod_spec (hf : f.Monic) (c : List ℕ) (hc : ∀ x ∈ c, x < p) :
    IsK p f.natDegree (zMod p (fcOf f) c) ∧
      AdjoinRoot.mk f (ap_zP p (zMod p (fcOf f) c)) = AdjoinRoot.mk f (ap_zP p c) := by
  unfold zMod
  rw [ap_dg_fcOf]
  have key : ((zRedStep p (fcOf f))^[c.length - f.natDegree] c).length ≤ f.natDegree ∧
      (∀ x ∈ (zRedStep p (fcOf f))^[c.length - f.natDegree] c, x < p) ∧
      AdjoinRoot.mk f (ap_zP p ((zRedStep p (fcOf f))^[c.length - f.natDegree] c)) =
        AdjoinRoot.mk f (ap_zP p c) := by
    by_cases hL : f.natDegree ≤ c.length
    · obtain ⟨h1, h2, h3⟩ := ap_zRed_iter hf (c.length - f.natDegree) c (by omega) hc
      exact ⟨by omega, h2, h3⟩
    · rw [show c.length - f.natDegree = 0 by omega, Function.iterate_zero, id]
      exact ⟨by omega, hc, rfl⟩
  obtain ⟨h1, h2, h3⟩ := key
  exact ⟨ap_isK_padTo _ _ h2, by rw [ap_zP_padTo _ _ h1, h3]⟩

theorem ap_kMul_spec (hf : f.Monic) (a b : List ℕ) :
    IsK p f.natDegree (kMul p (fcOf f) a b) ∧
      decK p f (kMul p (fcOf f) a b) = decK p f a * decK p f b := by
  have hlt : ∀ x ∈ zMulRaw p a b, x < p := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [zMulRaw, List.getElem_map]; exact Nat.mod_lt _ (ap_ppos p)
  obtain ⟨h1, h2⟩ := ap_zMod_spec hf _ hlt
  refine ⟨h1, ?_⟩
  rw [ap_decK_eq, kMul, h2, ap_zP_zMulRaw, map_mul]; rfl

theorem ap_kZero_spec (d : ℕ) : IsK p d (kZero d) ∧ decK p f (kZero d) = 0 := by
  refine ⟨⟨by simp [kZero], fun x hx => ?_⟩, ?_⟩
  · unfold kZero at hx; rw [List.eq_of_mem_replicate hx]; exact ap_ppos p
  · rw [ap_decK_eq]
    have h0 : ∀ k, (kZero d).getD k 0 = 0 := fun k => by
      unfold kZero
      by_cases hk : k < d
      · exact List.getD_replicate _ hk
      · exact List.getD_eq_default _ _ (by simp; omega)
    have : ap_zP p (kZero d) = 0 := by
      ext k; rw [ap_zP_coeff, coeff_zero, h0]; simp
    rw [this, map_zero]

theorem ap_kOne_spec (d : ℕ) (hd : 1 ≤ d) : IsK p d (kOne d) ∧ decK p f (kOne d) = 1 := by
  refine ⟨ap_isK_padTo _ _ (by simpa using (Fact.out : p.Prime).one_lt), ?_⟩
  rw [ap_decK_eq, kOne, ap_zP_padTo _ _ (by simpa using hd)]
  have : ap_zP p [1] = 1 := by
    ext k; rw [ap_zP_coeff, coeff_one]
    rcases k with _ | k
    · simp
    · simp
  rw [this, map_one]

theorem ap_decK_inj (hf : f.Monic) {a b : List ℕ} (ha : IsK p f.natDegree a)
    (hb : IsK p f.natDegree b) (h : decK p f a = decK p f b) : a = b := by
  rw [ap_decK_eq, ap_decK_eq, AdjoinRoot.mk_eq_mk] at h
  have h0 : ap_zP p a - ap_zP p b = 0 := by
    apply eq_zero_of_dvd_of_degree_lt h
    rw [degree_eq_natDegree hf.ne_zero]
    have h1 := ap_zP_degree_lt (p := p) a
    have h2 := ap_zP_degree_lt (p := p) b
    rw [ha.1] at h1; rw [hb.1] at h2
    calc (ap_zP p a - ap_zP p b).degree ≤ max _ _ := degree_sub_le _ _
      _ < _ := max_lt h1 h2
  apply List.ext_getElem (ha.1.trans hb.1.symm)
  intro i hia hib
  have := congrArg (fun q => q.coeff i) h0
  simp only [coeff_sub, coeff_zero, sub_eq_zero, ap_zP_coeff] at this
  rw [List.getD_eq_getElem _ _ hia, List.getD_eq_getElem _ _ hib] at this
  have := congrArg ZMod.val this
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (ha.2 _ (List.getElem_mem _)),
    Nat.mod_eq_of_lt (hb.2 _ (List.getElem_mem _))] at this

theorem ap_kOfIdx_eq (d j : ℕ) : kOfIdx p d j = digits p d j := rfl

theorem ap_kOfIdx_isK (d j : ℕ) : IsK p d (kOfIdx p d j) := by
  refine ⟨by simp [kOfIdx], ?_⟩
  intro x hx
  simp only [kOfIdx, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Nat.mod_lt _ (ap_ppos p)

theorem ap_mk_modByMonic {R : Type*} [CommRing R] (h q : R[X]) :
    AdjoinRoot.mk h (q %ₘ h) = AdjoinRoot.mk h q := by
  rw [AdjoinRoot.mk_eq_mk, modByMonic_eq_sub_mul_div]; exact ⟨-(q /ₘ h), by ring⟩

theorem ap_kOfIdx_surj (hf : f.Monic) (z : AdjoinRoot f) :
    ∃ j < p ^ f.natDegree, decK p f (kOfIdx p f.natDegree j) = z := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  have hrdeg : (q %ₘ f).degree < f.natDegree := by
    rw [← degree_eq_natDegree hf.ne_zero]; exact degree_modByMonic_lt q hf
  obtain ⟨j, hj, hdj⟩ := ap_digits_surj p (ap_ppos p)
    ((List.range f.natDegree).map fun i => ((q %ₘ f).coeff i).val) (by
      intro x hx; simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨i, _, rfl⟩ := hx; exact ZMod.val_lt _)
  simp only [List.length_map, List.length_range] at hj hdj
  refine ⟨j, hj, ?_⟩
  rw [ap_kOfIdx_eq, hdj, ap_decK_eq, ← ap_mk_modByMonic f q]
  congr 1
  ext k
  rw [ap_zP_coeff, ap_getD_map_range]
  split_ifs with hk
  · simp [ZMod.natCast_zmod_val]
  · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hrdeg (by exact_mod_cast (by omega : f.natDegree ≤ k)))]
    simp

theorem ap_kOfIdx_inj (hf : f.Monic) {j j' : ℕ} (hj : j < p ^ f.natDegree) (hj' : j' < p ^ f.natDegree)
    (h : decK p f (kOfIdx p f.natDegree j) = decK p f (kOfIdx p f.natDegree j')) : j = j' :=
  ap_digits_inj p (ap_ppos p) _ _ _ hj hj' (ap_decK_inj hf (ap_kOfIdx_isK _ _) (ap_kOfIdx_isK _ _) h)

theorem ap_kOfIdx_zero (d : ℕ) : decK p f (kOfIdx p d 0) = 0 := by
  rw [ap_decK_eq]
  have : ap_zP p (kOfIdx p d 0) = 0 := by
    ext k; rw [ap_zP_coeff, kOfIdx, ap_getD_map_range]; split_ifs <;> simp
  rw [this, map_zero]

end APK

section APKX

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}

abbrev ap_CL (p d L : ℕ) (c : List (List ℕ)) : Prop := c.length = L ∧ ∀ a ∈ c, IsK p d a

theorem ap_eq_zero_of_monic_dvd {R : Type*} [CommRing R] [Nontrivial R] {g q : R[X]}
    (hg : g.Monic) (h : g ∣ q) (hd : q.degree < g.degree) : q = 0 := by
  rw [← (modByMonic_eq_self_iff hg).2 hd]; exact (modByMonic_eq_zero_iff_dvd hg).2 h

theorem ap_decPoly_coeff (c : List (List ℕ)) (k : ℕ) :
    (decPoly p f c).coeff k = decK p f (c.getD k []) :=
  ap_sumFin_coeff c (decK p f) [] ap_decK_nil k

theorem ap_decK_getD_def {z : List ℕ} (hz : decK p f z = 0) (c : List (List ℕ)) (k : ℕ) :
    decK p f (c.getD k z) = decK p f (c.getD k []) := by
  by_cases hk : k < c.length
  · rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega), hz, ap_decK_nil]

theorem ap_decPoly_coeff' {z : List ℕ} (hz : decK p f z = 0) (c : List (List ℕ)) (k : ℕ) :
    (decPoly p f c).coeff k = decK p f (c.getD k z) := by
  rw [ap_decPoly_coeff, ap_decK_getD_def hz]

theorem ap_decPoly_degree_lt (c : List (List ℕ)) : (decPoly p f c).degree < c.length := by
  rw [degree_lt_iff_coeff_zero]; intro m hm
  rw [ap_decPoly_coeff, List.getD_eq_default _ _ hm, ap_decK_nil]

theorem ap_isK_getD {d : ℕ} {c : List (List ℕ)} (hc : ∀ a ∈ c, IsK p d a) (k : ℕ) {z : List ℕ}
    (hz : IsK p d z) : IsK p d (c.getD k z) :=
  (ap_getD_mem c k z).elim (hc _) (fun h => by rw [h]; exact hz)

theorem ap_isK_getD_lt {d : ℕ} {c : List (List ℕ)} (hc : ∀ a ∈ c, IsK p d a) {k : ℕ}
    (hk : k < c.length) (z : List ℕ) : IsK p d (c.getD k z) := by
  rw [List.getD_eq_getElem _ _ hk]; exact hc _ (List.getElem_mem _)

theorem ap_nontrivial (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) : Nontrivial (AdjoinRoot f) :=
  AdjoinRoot.nontrivial f (by
    rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast (by omega : f.natDegree ≠ 0))

theorem ap_decPoly_monic (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {d : ℕ} {g : List (List ℕ)}
    (hlen : g.length = d + 1) (hlast : g.getLastD [] = kOne f.natDegree) :
    (decPoly p f g).Monic ∧ (decPoly p f g).natDegree = d := by
  have := ap_nontrivial hf hf1
  have hcd : (decPoly p f g).coeff d = 1 := by
    rw [ap_decPoly_coeff, ← (ap_kOne_spec (p := p) (f := f) f.natDegree hf1).2, ← hlast,
      ap_getLastD_eq, hlen, Nat.add_sub_cancel]
  have hnd : (decPoly p f g).natDegree = d := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]; intro N hN
      rw [ap_decPoly_coeff, List.getD_eq_default _ _ (by omega), ap_decK_nil]
    · rw [hcd]; exact one_ne_zero
  exact ⟨by rw [Monic, leadingCoeff, hnd, hcd], hnd⟩

theorem ap_kpAdd_spec {L : ℕ} {a b : List (List ℕ)} (ha : ap_CL p f.natDegree L a)
    (hb : ap_CL p f.natDegree L b) :
    ap_CL p f.natDegree L (kpAdd p a b) ∧
      decPoly p f (kpAdd p a b) = decPoly p f a + decPoly p f b := by
  have hl : a.length = b.length := ha.1.trans hb.1.symm
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  refine ⟨⟨by simp [kpAdd, ha.1, hb.1], ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [kpAdd, List.getElem_zipWith]
    exact (ap_kAdd_spec (f := f) (ha.2 _ (List.getElem_mem _)) (hb.2 _ (List.getElem_mem _))).1
  · have hz' : decK p f (kAdd p (kZero f.natDegree) (kZero f.natDegree)) = 0 := by
      rw [(ap_kAdd_spec (f := f) hz.1 hz.1).2, hz.2, add_zero]
    ext k
    rw [coeff_add, ap_decPoly_coeff' hz', kpAdd,
      ap_zipWith_getD _ _ _ (kZero f.natDegree) (kZero f.natDegree) _ rfl hl,
      (ap_kAdd_spec (f := f) (ap_isK_getD ha.2 k hz.1) (ap_isK_getD hb.2 k hz.1)).2,
      ap_decPoly_coeff' hz.2, ap_decPoly_coeff' hz.2]

theorem ap_kfold (hf : f.Monic) (h : ℕ → List ℕ) (hh : ∀ i, IsK p f.natDegree (h i)) (n : ℕ) :
    IsK p f.natDegree ((List.range n).foldl (fun acc i => kAdd p acc (h i)) (kZero f.natDegree)) ∧
    decK p f ((List.range n).foldl (fun acc i => kAdd p acc (h i)) (kZero f.natDegree)) =
      ∑ i ∈ Finset.range n, decK p f (h i) := by
  induction n with
  | zero => simpa using ap_kZero_spec (p := p) (f := f) f.natDegree
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ]
    obtain ⟨h1, h2⟩ := ap_kAdd_spec (f := f) ih.1 (hh n)
    exact ⟨h1, by rw [h2, ih.2]⟩

theorem ap_kpMulRaw_length (fc : List ℕ) (a b : List (List ℕ)) :
    (kpMulRaw p fc a b).length = a.length + b.length - 1 := by
  simp [kpMulRaw]

theorem ap_kpMulRaw_getD (a b : List (List ℕ)) (k : ℕ) (hk : k < a.length + b.length - 1) :
    (kpMulRaw p (fcOf f) a b).getD k [] = (List.range (k + 1)).foldl
      (fun acc i => kAdd p acc (kMul p (fcOf f) (a.getD i (kZero f.natDegree))
        (b.getD (k - i) (kZero f.natDegree)))) (kZero f.natDegree) := by
  unfold kpMulRaw; rw [ap_getD_map_range, if_pos hk, ap_dg_fcOf]

theorem ap_kpMulRaw_spec (hf : f.Monic) {La Lb : ℕ} {a b : List (List ℕ)}
    (ha : ap_CL p f.natDegree La a) (hb : ap_CL p f.natDegree Lb b) :
    ap_CL p f.natDegree (La + Lb - 1) (kpMulRaw p (fcOf f) a b) ∧
      decPoly p f (kpMulRaw p (fcOf f) a b) = decPoly p f a * decPoly p f b := by
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  refine ⟨⟨by rw [ap_kpMulRaw_length, ha.1, hb.1], ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hk' : k < a.length + b.length - 1 := by rw [ap_kpMulRaw_length] at hk; exact hk
    rw [← List.getD_eq_getElem _ [] hk, ap_kpMulRaw_getD a b k hk']
    exact (ap_kfold hf _ (fun i => (ap_kMul_spec hf _ _).1) (k+1)).1
  · ext k
    rw [ap_decPoly_coeff, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    by_cases hk : k < a.length + b.length - 1
    · rw [ap_kpMulRaw_getD a b k hk, (ap_kfold hf _ (fun i => (ap_kMul_spec hf _ _).1) (k+1)).2]
      apply Finset.sum_congr rfl; intro i _
      rw [(ap_kMul_spec hf _ _).2, ap_decPoly_coeff' hz.2, ap_decPoly_coeff' hz.2]
    · rw [List.getD_eq_default _ _ (by rw [ap_kpMulRaw_length]; omega), ap_decK_nil]
      symm; apply Finset.sum_eq_zero; intro i hi
      simp only [Finset.mem_range] at hi
      by_cases hia : i < a.length
      · rw [ap_decPoly_coeff b, List.getD_eq_default _ _ (by omega), ap_decK_nil, mul_zero]
      · rw [ap_decPoly_coeff a, List.getD_eq_default _ _ (by omega), ap_decK_nil, zero_mul]

theorem ap_kpRedStep_length (fc : List ℕ) (g c : List (List ℕ)) :
    (kpRedStep p fc g c).length = c.length - 1 := by
  simp [kpRedStep]

theorem ap_kpRedStep_getD (g c : List (List ℕ)) (i : ℕ) (hi : i < c.length - 1) :
    (kpRedStep p (fcOf f) g c).getD i [] = if c.length - g.length ≤ i then
      kSub p (c.getD i []) (kMul p (fcOf f) (c.getLastD (kZero f.natDegree))
        (g.getD (i - (c.length - g.length)) (kZero f.natDegree)))
      else c.getD i [] := by
  rw [List.getD_eq_getElem _ _ (by rw [ap_kpRedStep_length]; exact hi),
    List.getD_eq_getElem _ _ (by omega : i < c.length)]
  simp only [kpRedStep, List.getElem_mapIdx, List.getElem_dropLast, ap_dg_fcOf]

theorem ap_kpRedStep_isK (hf : f.Monic) (g c : List (List ℕ)) (hc : ∀ a ∈ c, IsK p f.natDegree a) :
    ∀ a ∈ kpRedStep p (fcOf f) g c, IsK p f.natDegree a := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < c.length - 1 := by rw [ap_kpRedStep_length] at hi; exact hi
  rw [← List.getD_eq_getElem _ [] hi, ap_kpRedStep_getD _ _ _ hi']
  split_ifs
  · exact (ap_kSub_spec (f := f) (ap_isK_getD_lt hc (by omega) _) (ap_kMul_spec hf _ _).1).1
  · exact ap_isK_getD_lt hc (by omega) _

theorem ap_decPoly_kpRedStep (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {d : ℕ} {g c : List (List ℕ)}
    (hg : ap_CL p f.natDegree (d+1) g) (hgl : g.getLastD [] = kOne f.natDegree)
    (hc : ∀ a ∈ c, IsK p f.natDegree a) (hL : d + 1 ≤ c.length) :
    decPoly p f (kpRedStep p (fcOf f) g c) = decPoly p f c -
      C (decK p f (c.getLastD (kZero f.natDegree))) * decPoly p f g * X ^ (c.length - (d + 1)) := by
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  obtain ⟨hmon, hnd⟩ := ap_decPoly_monic hf hf1 hg.1 hgl
  ext i
  rw [coeff_sub, coeff_mul_X_pow', coeff_C_mul, ap_decPoly_coeff, ap_decPoly_coeff c]
  by_cases hi : i < c.length - 1
  · rw [ap_kpRedStep_getD _ _ _ hi, hg.1]
    split_ifs with h1
    · rw [(ap_kSub_spec (f := f) (ap_isK_getD_lt hc (by omega) _) (ap_kMul_spec hf _ _).1).2,
        (ap_kMul_spec hf _ _).2, ap_decPoly_coeff' hz.2 g]
    · simp
  · rw [List.getD_eq_default _ _ (by rw [ap_kpRedStep_length]; omega), ap_decK_nil]
    rw [if_pos (by omega), ap_getLastD_eq, ap_decK_getD_def hz.2]
    by_cases hi' : i = c.length - 1
    · subst hi'
      rw [show c.length - 1 - (c.length - (d+1)) = d by omega, ← hnd, hmon.coeff_natDegree]
      simp
    · rw [List.getD_eq_default c _ (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [ap_decK_nil]

theorem ap_kpRed_iter (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {d : ℕ} {g : List (List ℕ)}
    (hg : ap_CL p f.natDegree (d+1) g) (hgl : g.getLastD [] = kOne f.natDegree) (n : ℕ) :
    ∀ c : List (List ℕ), d + n ≤ c.length → (∀ a ∈ c, IsK p f.natDegree a) →
    ((kpRedStep p (fcOf f) g)^[n] c).length = c.length - n ∧
    (∀ a ∈ (kpRedStep p (fcOf f) g)^[n] c, IsK p f.natDegree a) ∧
    decPoly p f g ∣ decPoly p f c - decPoly p f ((kpRedStep p (fcOf f) g)^[n] c) := by
  induction n with
  | zero => intro c _ hc; simpa using hc
  | succ n ih =>
    intro c hlen hc
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3⟩ := ih (kpRedStep p (fcOf f) g c) (by rw [ap_kpRedStep_length]; omega)
      (ap_kpRedStep_isK hf g c hc)
    refine ⟨by rw [h1, ap_kpRedStep_length]; omega, h2, ?_⟩
    have e := ap_decPoly_kpRedStep hf hf1 hg hgl hc (by omega)
    have : decPoly p f c - decPoly p f ((kpRedStep p (fcOf f) g)^[n] (kpRedStep p (fcOf f) g c)) =
        (decPoly p f c - decPoly p f (kpRedStep p (fcOf f) g c)) +
        (decPoly p f (kpRedStep p (fcOf f) g c) -
          decPoly p f ((kpRedStep p (fcOf f) g)^[n] (kpRedStep p (fcOf f) g c))) := by ring
    rw [this]
    refine dvd_add ?_ h3
    rw [e]
    exact ⟨C (decK p f (c.getLastD (kZero f.natDegree))) * X ^ (c.length - (d + 1)), by ring⟩

theorem ap_decPoly_padTo {z : List ℕ} (hz : decK p f z = 0) (d : ℕ) (l : List (List ℕ))
    (hl : l.length ≤ d) : decPoly p f (padTo z d l) = decPoly p f l := by
  ext k; rw [ap_decPoly_coeff' hz, ap_decPoly_coeff' hz, ap_padTo_getD _ _ _ hl]

theorem ap_kpMod_spec (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {d L : ℕ} {g c : List (List ℕ)}
    (hg : ap_CL p f.natDegree (d+1) g) (hgl : g.getLastD [] = kOne f.natDegree)
    (hc : ap_CL p f.natDegree L c) :
    ap_CL p f.natDegree d (kpMod p (fcOf f) g c) ∧
      decPoly p f (kpMod p (fcOf f) g c) = decPoly p f c %ₘ decPoly p f g := by
  have := ap_nontrivial hf hf1
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  obtain ⟨hmon, hnd⟩ := ap_decPoly_monic hf hf1 hg.1 hgl
  unfold kpMod
  rw [ap_dg_fcOf, hg.1, Nat.add_sub_cancel]
  have key : ((kpRedStep p (fcOf f) g)^[c.length - d] c).length ≤ d ∧
      (∀ a ∈ (kpRedStep p (fcOf f) g)^[c.length - d] c, IsK p f.natDegree a) ∧
      decPoly p f g ∣ decPoly p f c - decPoly p f ((kpRedStep p (fcOf f) g)^[c.length - d] c) := by
    by_cases hL : d ≤ c.length
    · obtain ⟨h1, h2, h3⟩ := ap_kpRed_iter hf hf1 hg hgl (c.length - d) c (by omega) hc.2
      exact ⟨by omega, h2, h3⟩
    · rw [show c.length - d = 0 by omega, Function.iterate_zero, id]
      exact ⟨by omega, hc.2, by simp⟩
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨⟨ap_padTo_length _ _ _, fun a ha =>
    (ap_padTo_mem _ _ _ _ ha).elim (h2 a) (fun h => h ▸ hz.1)⟩, ?_⟩
  rw [ap_decPoly_padTo hz.2 _ _ h1, modByMonic_eq_of_dvd_sub hmon h3, eq_comm,
    modByMonic_eq_self_iff hmon, degree_eq_natDegree hmon.ne_zero, hnd]
  exact lt_of_lt_of_le (ap_decPoly_degree_lt _) (by exact_mod_cast h1)

theorem ap_kpIsZero_iff (hf : f.Monic) {c : List (List ℕ)} (hc : ∀ a ∈ c, IsK p f.natDegree a) :
    kpIsZero c = true ↔ decPoly p f c = 0 := by
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  have key : ∀ a, IsK p f.natDegree a → ((∀ x ∈ a, x = 0) ↔ decK p f a = 0) := by
    intro a ha
    constructor
    · intro h0
      have : a = kZero f.natDegree := List.eq_replicate_iff.2 ⟨ha.1, h0⟩
      rw [this, hz.2]
    · intro h0
      have : a = kZero f.natDegree := ap_decK_inj hf ha hz.1 (h0.trans hz.2.symm)
      intro x hx; rw [this] at hx; exact List.eq_of_mem_replicate hx
  simp only [kpIsZero, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h; ext k; rw [ap_decPoly_coeff, coeff_zero]
    rcases ap_getD_mem c k [] with hm | hm
    · exact (key _ (hc _ hm)).1 (h _ hm)
    · rw [hm, ap_decK_nil]
  · intro h a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ha
    apply (key _ (hc _ ha)).2
    have := congrArg (fun q => q.coeff k) h
    simp only [ap_decPoly_coeff, coeff_zero, List.getD_eq_getElem _ _ hk] at this
    exact this

theorem ap_decPoly_inj (hf : f.Monic) {L : ℕ} {c c' : List (List ℕ)} (hc : ap_CL p f.natDegree L c)
    (hc' : ap_CL p f.natDegree L c') (h : decPoly p f c = decPoly p f c') : c = c' := by
  apply List.ext_getElem (hc.1.trans hc'.1.symm)
  intro i h1 h2
  have := congrArg (fun q => q.coeff i) h
  simp only [ap_decPoly_coeff, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact ap_decK_inj hf (hc.2 _ (List.getElem_mem _)) (hc'.2 _ (List.getElem_mem _)) this

theorem ap_kpOfIdx_eq (d len j : ℕ) :
    kpOfIdx p d len j = (digits (p ^ d) len j).map (kOfIdx p d) := by
  unfold kpOfIdx digits; rw [List.map_map]; rfl

theorem ap_kpOfIdx_CL (d len j : ℕ) : ap_CL p d len (kpOfIdx p d len j) := by
  refine ⟨by simp [kpOfIdx], ?_⟩
  intro a ha
  simp only [kpOfIdx, List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact ap_kOfIdx_isK _ _

theorem ap_kpOfIdx_surj (hf : f.Monic) (len : ℕ) (G : (AdjoinRoot f)[X]) (hG : G.degree < len) :
    ∃ j < (p ^ f.natDegree) ^ len, decPoly p f (kpOfIdx p f.natDegree len j) = G := by
  choose J hJ hJd using fun l => ap_kOfIdx_surj hf (G.coeff l)
  obtain ⟨j, hj, hdj⟩ := ap_digits_surj (p ^ f.natDegree) (pow_pos (ap_ppos p) _)
    ((List.range len).map J) (by
      intro x hx; simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨l, _, rfl⟩ := hx; exact hJ l)
  simp only [List.length_map, List.length_range] at hj hdj
  refine ⟨j, hj, ?_⟩
  rw [ap_kpOfIdx_eq, hdj, List.map_map]
  ext l
  rw [ap_decPoly_coeff, ap_getD_map_range]
  split_ifs with hl
  · exact hJd l
  · rw [ap_decK_nil, coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hG (by exact_mod_cast (by omega : len ≤ l)))]

theorem ap_decPoly_append_kOne (hf1 : 1 ≤ f.natDegree) (l : List (List ℕ)) :
    decPoly p f (l ++ [kOne f.natDegree]) = decPoly p f l + X ^ l.length := by
  ext k
  rw [coeff_add, coeff_X_pow, ap_decPoly_coeff, ap_decPoly_coeff]
  by_cases hk : k < l.length
  · rw [List.getD_append _ _ _ _ hk, if_neg (by omega), add_zero]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default l _ (by omega),
      ap_decK_nil, zero_add]
    by_cases hk' : k = l.length
    · subst hk'
      rw [if_pos rfl, Nat.sub_self]
      exact (ap_kOne_spec (p := p) (f := f) f.natDegree hf1).2
    · rw [if_neg hk', List.getD_eq_default _ _ (by simp; omega), ap_decK_nil]

end APKX

section APF

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}

theorem ap_fMul_spec (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {m : ℕ} {hc : List (List ℕ)}
    (hhc : ap_CL p f.natDegree (m+1) hc) (hgl : hc.getLastD [] = kOne f.natDegree)
    {x y : List (List ℕ)} (hx : ap_CL p f.natDegree m x) (hy : ap_CL p f.natDegree m y) :
    ap_CL p f.natDegree m (fMul p (fcOf f) hc x y) ∧
      decF p f hc (fMul p (fcOf f) hc x y) = decF p f hc x * decF p f hc y := by
  obtain ⟨h1, h2⟩ := ap_kpMulRaw_spec hf hx hy
  obtain ⟨h3, h4⟩ := ap_kpMod_spec hf hf1 hhc hgl h1
  refine ⟨h3, ?_⟩
  simp only [decF]
  rw [fMul, h4, h2, ap_mk_modByMonic, map_mul]

theorem ap_fEmbed_spec {m : ℕ} (hm : 1 ≤ m) {hc : List (List ℕ)}
    (hlen : hc.length = m + 1) {c : List ℕ} (hcK : IsK p f.natDegree c) :
    ap_CL p f.natDegree m (fEmbed (fcOf f) hc c) ∧
      decF p f hc (fEmbed (fcOf f) hc c) = AdjoinRoot.of (decPoly p f hc) (decK p f c) := by
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  unfold fEmbed
  rw [ap_dg_fcOf, hlen, Nat.add_sub_cancel]
  refine ⟨⟨ap_padTo_length _ _ _, fun a ha => (ap_padTo_mem _ _ _ _ ha).elim
    (fun h => by rw [List.mem_singleton] at h; rw [h]; exact hcK)
    (fun h => by rw [h]; exact hz.1)⟩, ?_⟩
  simp only [decF]
  rw [ap_decPoly_padTo hz.2 _ _ (by simpa using hm)]
  have : decPoly p f [c] = C (decK p f c) := by
    ext k; rw [ap_decPoly_coeff, coeff_C]
    rcases k with _ | k
    · simp
    · simp [ap_decK_nil]
  rw [this, AdjoinRoot.mk_C]

theorem ap_fOne_spec (hf1 : 1 ≤ f.natDegree) {m : ℕ} (hm : 1 ≤ m)
    {hc : List (List ℕ)} (hlen : hc.length = m + 1) :
    ap_CL p f.natDegree m (fOne (fcOf f) hc) ∧ decF p f hc (fOne (fcOf f) hc) = 1 := by
  have e : fOne (fcOf f) hc = fEmbed (fcOf f) hc (kOne f.natDegree) := by
    unfold fOne fEmbed; rw [ap_dg_fcOf]
  have hk := ap_kOne_spec (p := p) (f := f) f.natDegree hf1
  obtain ⟨h1, h2⟩ := ap_fEmbed_spec (f := f) hm hlen hk.1
  rw [e]; exact ⟨h1, by rw [h2, hk.2, map_one]⟩

theorem ap_fZero_spec {m : ℕ} {hc : List (List ℕ)} (hlen : hc.length = m + 1) :
    ap_CL p f.natDegree m (fZero (fcOf f) hc) ∧ decF p f hc (fZero (fcOf f) hc) = 0 := by
  have hz := ap_kZero_spec (p := p) (f := f) f.natDegree
  unfold fZero; rw [ap_dg_fcOf, hlen, Nat.add_sub_cancel]
  refine ⟨⟨by simp, fun a ha => by rw [List.eq_of_mem_replicate ha]; exact hz.1⟩, ?_⟩
  simp only [decF]
  have : decPoly p f (List.replicate m (kZero f.natDegree)) = 0 := by
    ext k; rw [ap_decPoly_coeff' hz.2, coeff_zero]
    by_cases hk : k < m
    · rw [List.getD_replicate _ hk, hz.2]
    · rw [List.getD_eq_default _ _ (by simp; omega), hz.2]
  rw [this, map_zero]

theorem ap_fPow_spec (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {m : ℕ} (hm : 1 ≤ m)
    {hc : List (List ℕ)} (hhc : ap_CL p f.natDegree (m+1) hc)
    (hgl : hc.getLastD [] = kOne f.natDegree) {x : List (List ℕ)} (hx : ap_CL p f.natDegree m x)
    (e : ℕ) :
    ap_CL p f.natDegree m (fPow p (fcOf f) hc x e) ∧
      decF p f hc (fPow p (fcOf f) hc x e) = decF p f hc x ^ e := by
  unfold fPow
  induction e using Nat.binaryRec with
  | zero =>
    simp only [Nat.zero_bits, List.reverse_nil, List.foldl_nil, pow_zero]
    exact ap_fOne_spec hf1 hm hhc.1
  | bit b n ih =>
    by_cases h : n = 0 → b = true
    · rw [Nat.bits_append_bit n b h, List.reverse_cons, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := ap_fMul_spec hf hf1 hhc hgl h1 h1
      cases b
      · simp only [Bool.false_eq_true, if_false]
        refine ⟨h3, ?_⟩
        rw [h4, h2, Nat.bit_val]; simp only [Bool.toNat_false]; ring
      · simp only [if_true]
        obtain ⟨h5, h6⟩ := ap_fMul_spec hf hf1 hhc hgl h3 hx
        refine ⟨h5, ?_⟩
        rw [h6, h4, h2, Nat.bit_val]; simp only [Bool.toNat_true]; ring
    · have hb : n = 0 ∧ b = false := by
        constructor
        · by_contra hn; exact h (fun h' => absurd h' hn)
        · cases b
          · rfl
          · exact absurd (fun _ => rfl) h
      obtain ⟨rfl, rfl⟩ := hb
      exact ih

theorem ap_decF_inj (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {m : ℕ} {hc : List (List ℕ)}
    (hhc : ap_CL p f.natDegree (m+1) hc) (hgl : hc.getLastD [] = kOne f.natDegree)
    {x y : List (List ℕ)} (hx : ap_CL p f.natDegree m x) (hy : ap_CL p f.natDegree m y)
    (h : decF p f hc x = decF p f hc y) : x = y := by
  have := ap_nontrivial hf hf1
  obtain ⟨hmon, hnd⟩ := ap_decPoly_monic hf hf1 hhc.1 hgl
  simp only [decF] at h
  rw [AdjoinRoot.mk_eq_mk] at h
  apply ap_decPoly_inj hf hx hy
  rw [← sub_eq_zero]
  apply ap_eq_zero_of_monic_dvd hmon h
  rw [degree_eq_natDegree hmon.ne_zero, hnd]
  have h1 := ap_decPoly_degree_lt (p := p) (f := f) x
  have h2 := ap_decPoly_degree_lt (p := p) (f := f) y
  rw [hx.1] at h1; rw [hy.1] at h2
  calc _ ≤ max _ _ := degree_sub_le _ _
    _ < _ := max_lt h1 h2

theorem ap_fOfIdx_eq {m : ℕ} {hc : List (List ℕ)} (hlen : hc.length = m + 1) (j : ℕ) :
    fOfIdx p (fcOf f) hc j = kpOfIdx p f.natDegree m j := by
  unfold fOfIdx; rw [ap_dg_fcOf, hlen, Nat.add_sub_cancel]

theorem ap_fOfIdx_surj (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) {m : ℕ} {hc : List (List ℕ)}
    (hhc : ap_CL p f.natDegree (m+1) hc) (hgl : hc.getLastD [] = kOne f.natDegree)
    (z : AdjoinRoot (decPoly p f hc)) :
    ∃ j < (p ^ f.natDegree) ^ m, decF p f hc (fOfIdx p (fcOf f) hc j) = z := by
  have := ap_nontrivial hf hf1
  obtain ⟨hmon, hnd⟩ := ap_decPoly_monic hf hf1 hhc.1 hgl
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨j, hj, hdj⟩ := ap_kpOfIdx_surj hf m (q %ₘ decPoly p f hc) (by
    have := degree_modByMonic_lt q hmon; rwa [degree_eq_natDegree hmon.ne_zero, hnd] at this)
  refine ⟨j, hj, ?_⟩
  simp only [decF]
  rw [ap_fOfIdx_eq hhc.1, hdj, ap_mk_modByMonic]

end APF

section Spec

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} (hf : f.Monic) (hf1 : 1 ≤ f.natDegree)
include hf hf1

theorem dg_fcOf : dg (fcOf f) = f.natDegree := by
  exact ap_dg_fcOf

/-! ### `K` -/

theorem kAdd_spec {a b : List ℕ} (ha : IsK p f.natDegree a) (hb : IsK p f.natDegree b) :
    IsK p f.natDegree (kAdd p a b) ∧ decK p f (kAdd p a b) = decK p f a + decK p f b := by
  exact ap_kAdd_spec ha hb

theorem kSub_spec {a b : List ℕ} (ha : IsK p f.natDegree a) (hb : IsK p f.natDegree b) :
    IsK p f.natDegree (kSub p a b) ∧ decK p f (kSub p a b) = decK p f a - decK p f b := by
  exact ap_kSub_spec ha hb

theorem kMul_spec {a b : List ℕ} (ha : IsK p f.natDegree a) (hb : IsK p f.natDegree b) :
    IsK p f.natDegree (kMul p (fcOf f) a b) ∧
      decK p f (kMul p (fcOf f) a b) = decK p f a * decK p f b := by
  exact ap_kMul_spec hf a b

theorem kZero_spec : IsK p f.natDegree (kZero f.natDegree) ∧ decK p f (kZero f.natDegree) = 0 := by
  exact ap_kZero_spec _

theorem kOne_spec : IsK p f.natDegree (kOne f.natDegree) ∧ decK p f (kOne f.natDegree) = 1 := by
  exact ap_kOne_spec _ hf1

theorem decK_inj {a b : List ℕ} (ha : IsK p f.natDegree a) (hb : IsK p f.natDegree b)
    (h : decK p f a = decK p f b) : a = b := by
  exact ap_decK_inj hf ha hb h

theorem kOfIdx_isK (j : ℕ) : IsK p f.natDegree (kOfIdx p f.natDegree j) := by
  exact ap_kOfIdx_isK _ _

/-- every element of `K` is `decK` of some index `< p^df` -/
theorem kOfIdx_surj (z : AdjoinRoot f) : ∃ j < p ^ f.natDegree, decK p f (kOfIdx p f.natDegree j) = z := by
  exact ap_kOfIdx_surj hf z

theorem kOfIdx_inj {j j' : ℕ} (hj : j < p ^ f.natDegree) (hj' : j' < p ^ f.natDegree)
    (h : decK p f (kOfIdx p f.natDegree j) = decK p f (kOfIdx p f.natDegree j')) : j = j' := by
  exact ap_kOfIdx_inj hf hj hj' h

theorem kOfIdx_zero : decK p f (kOfIdx p f.natDegree 0) = 0 := by
  exact ap_kOfIdx_zero _

/-! ### `K[X]` -/

/-- a canonical monic polynomial of degree `d` (`d+1` canonical coefficients, top one `kOne`) -/
def IsMonicRep (p d len : ℕ) (g : List (List ℕ)) : Prop :=
  IsCoeffList' p d (len + 1) g ∧ g.getLastD [] = kOne d
where IsCoeffList' (p d L : ℕ) (c : List (List ℕ)) : Prop := c.length = L ∧ ∀ a ∈ c, IsK p d a

theorem isCoeffList_iff (L : ℕ) (c : List (List ℕ)) :
    IsCoeffList p f L c ↔ IsMonicRep.IsCoeffList' p f.natDegree L c := by
  exact Iff.rfl

theorem decPoly_monic {d : ℕ} {g : List (List ℕ)} (hg : IsMonicRep p f.natDegree d g) :
    (decPoly p f g).Monic ∧ (decPoly p f g).natDegree = d := by
  exact ap_decPoly_monic hf hf1 hg.1.1 hg.2

theorem kpAdd_spec {L : ℕ} {a b : List (List ℕ)} (ha : IsMonicRep.IsCoeffList' p f.natDegree L a)
    (hb : IsMonicRep.IsCoeffList' p f.natDegree L b) :
    IsMonicRep.IsCoeffList' p f.natDegree L (kpAdd p a b) ∧
      decPoly p f (kpAdd p a b) = decPoly p f a + decPoly p f b := by
  exact ap_kpAdd_spec ha hb

theorem kpMulRaw_spec {La Lb : ℕ} (hLa : 1 ≤ La) (hLb : 1 ≤ Lb) {a b : List (List ℕ)}
    (ha : IsMonicRep.IsCoeffList' p f.natDegree La a)
    (hb : IsMonicRep.IsCoeffList' p f.natDegree Lb b) :
    IsMonicRep.IsCoeffList' p f.natDegree (La + Lb - 1) (kpMulRaw p (fcOf f) a b) ∧
      decPoly p f (kpMulRaw p (fcOf f) a b) = decPoly p f a * decPoly p f b := by
  exact ap_kpMulRaw_spec hf ha hb

theorem kpMod_spec {d L : ℕ} {g c : List (List ℕ)} (hg : IsMonicRep p f.natDegree d g)
    (hc : IsMonicRep.IsCoeffList' p f.natDegree L c) :
    IsMonicRep.IsCoeffList' p f.natDegree d (kpMod p (fcOf f) g c) ∧
      decPoly p f (kpMod p (fcOf f) g c) = decPoly p f c %ₘ decPoly p f g := by
  exact ap_kpMod_spec hf hf1 hg.1 hg.2 hc

theorem kpIsZero_iff {L : ℕ} {c : List (List ℕ)} (hc : IsMonicRep.IsCoeffList' p f.natDegree L c) :
    kpIsZero c = true ↔ decPoly p f c = 0 := by
  exact ap_kpIsZero_iff hf hc.2

theorem decPoly_inj {L : ℕ} {c c' : List (List ℕ)} (hc : IsMonicRep.IsCoeffList' p f.natDegree L c)
    (hc' : IsMonicRep.IsCoeffList' p f.natDegree L c') (h : decPoly p f c = decPoly p f c') :
    c = c' := by
  exact ap_decPoly_inj hf hc hc' h

theorem decPoly_degree_lt {L : ℕ} {c : List (List ℕ)} (hc : IsMonicRep.IsCoeffList' p f.natDegree L c) :
    (decPoly p f c).degree < L := by
  rw [← hc.1]; exact ap_decPoly_degree_lt c

/-- `monicOfIdx` enumerates all monic polynomials of degree `d` over `K` -/
theorem monicOfIdx_spec (d j : ℕ) :
    IsMonicRep p f.natDegree d (monicOfIdx p f.natDegree d j) := by
  refine ⟨⟨by simp [monicOfIdx, kpOfIdx], fun a ha => ?_⟩, by simp [monicOfIdx]⟩
  rcases List.mem_append.1 ha with h | h
  · exact (ap_kpOfIdx_CL _ _ _).2 a h
  · rw [List.mem_singleton] at h; rw [h]; exact (ap_kOne_spec (f := f) _ hf1).1

theorem monicOfIdx_surj (d : ℕ) (G : (AdjoinRoot f)[X]) (hG : G.Monic) (hGd : G.natDegree = d) :
    ∃ j < (p ^ f.natDegree) ^ d, decPoly p f (monicOfIdx p f.natDegree d j) = G := by
  have hdeg : (G - X ^ d).degree < (d : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    rw [coeff_sub, coeff_X_pow]
    by_cases hkd : k = d
    · subst hkd; rw [if_pos rfl, ← hGd, hG.coeff_natDegree, sub_self]
    · rw [if_neg hkd, coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  obtain ⟨j, hj, hdj⟩ := ap_kpOfIdx_surj hf d (G - X ^ d) hdeg
  refine ⟨j, hj, ?_⟩
  rw [monicOfIdx, ap_decPoly_append_kOne hf1, hdj, (ap_kpOfIdx_CL _ _ _).1, sub_add_cancel]

/-- `kpOfIdx` enumerates all polynomials of degree `< len` over `K` -/
theorem kpOfIdx_spec (len j : ℕ) :
    IsMonicRep.IsCoeffList' p f.natDegree len (kpOfIdx p f.natDegree len j) := by
  exact ap_kpOfIdx_CL _ _ _

theorem kpOfIdx_surj (len : ℕ) (G : (AdjoinRoot f)[X]) (hG : G.degree < len) :
    ∃ j < (p ^ f.natDegree) ^ len, decPoly p f (kpOfIdx p f.natDegree len j) = G := by
  exact ap_kpOfIdx_surj hf len G hG

/-! ### `F = K[X]/(h)` -/

variable {m : ℕ} (hm : 1 ≤ m) {hc : List (List ℕ)} (hhc : IsMonicRep p f.natDegree m hc)
include hm hhc

theorem fMul_spec {x y : List (List ℕ)} (hx : IsMonicRep.IsCoeffList' p f.natDegree m x)
    (hy : IsMonicRep.IsCoeffList' p f.natDegree m y) :
    IsMonicRep.IsCoeffList' p f.natDegree m (fMul p (fcOf f) hc x y) ∧
      decF p f hc (fMul p (fcOf f) hc x y) = decF p f hc x * decF p f hc y := by
  exact ap_fMul_spec hf hf1 hhc.1 hhc.2 hx hy

theorem fOne_spec : IsMonicRep.IsCoeffList' p f.natDegree m (fOne (fcOf f) hc) ∧
    decF p f hc (fOne (fcOf f) hc) = 1 := by
  exact ap_fOne_spec hf1 hm hhc.1.1

theorem fZero_spec : IsMonicRep.IsCoeffList' p f.natDegree m (fZero (fcOf f) hc) ∧
    decF p f hc (fZero (fcOf f) hc) = 0 := by
  exact ap_fZero_spec hhc.1.1

theorem fPow_spec {x : List (List ℕ)} (hx : IsMonicRep.IsCoeffList' p f.natDegree m x) (e : ℕ) :
    IsMonicRep.IsCoeffList' p f.natDegree m (fPow p (fcOf f) hc x e) ∧
      decF p f hc (fPow p (fcOf f) hc x e) = decF p f hc x ^ e := by
  exact ap_fPow_spec hf hf1 hm hhc.1 hhc.2 hx e

theorem fEmbed_spec {c : List ℕ} (hcK : IsK p f.natDegree c) :
    IsMonicRep.IsCoeffList' p f.natDegree m (fEmbed (fcOf f) hc c) ∧
      decF p f hc (fEmbed (fcOf f) hc c) = AdjoinRoot.of (decPoly p f hc) (decK p f c) := by
  exact ap_fEmbed_spec hm hhc.1.1 hcK

theorem decF_inj {x y : List (List ℕ)} (hx : IsMonicRep.IsCoeffList' p f.natDegree m x)
    (hy : IsMonicRep.IsCoeffList' p f.natDegree m y)
    (h : decF p f hc x = decF p f hc y) : x = y := by
  exact ap_decF_inj hf hf1 hhc.1 hhc.2 hx hy h

theorem fOfIdx_spec (j : ℕ) : IsMonicRep.IsCoeffList' p f.natDegree m (fOfIdx p (fcOf f) hc j) := by
  rw [ap_fOfIdx_eq hhc.1.1]; exact ap_kpOfIdx_CL _ _ _

theorem fOfIdx_surj (z : AdjoinRoot (decPoly p f hc)) :
    ∃ j < (p ^ f.natDegree) ^ m, decF p f hc (fOfIdx p (fcOf f) hc j) = z := by
  exact ap_fOfIdx_surj hf hf1 hhc.1 hhc.2 z

end Spec

end RSSDAlg


-- ===================== Constr_lib.lean

open Polynomial

set_option linter.unusedSectionVars false

namespace RSSDC

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]

noncomputable abbrev frob (K F : Type*) [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F] :
    F ≃ₐ[K] F := FiniteField.frobeniusAlgEquivOfAlgebraic K F

theorem frob_pow_apply (a : ℕ) (x : F) : (frob K F ^ a) x = x ^ (Fintype.card K ^ a) := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

theorem fix_gcd (σ : F ≃ₐ[K] F) (x : F) (a b : ℕ) (ha : (σ ^ a) x = x) (hb : (σ ^ b) x = x) :
    (σ ^ Nat.gcd a b) x = x := by
  let H := MulAction.stabilizer (F ≃ₐ[K] F) x
  have ha' : σ ^ a ∈ H := ha
  have hb' : σ ^ b ∈ H := hb
  have : σ ^ ((Nat.gcd a b : ℕ) : ℤ) ∈ H := by
    rw [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    exact H.mul_mem (H.zpow_mem ha' _) (H.zpow_mem hb' _)
  rw [zpow_natCast] at this
  exact this

theorem fix_mod (σ : F ≃ₐ[K] F) (x : F) (q a : ℕ) (hq : (σ ^ q) x = x) :
    (σ ^ a) x = (σ ^ (a % q)) x := by
  conv_lhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul]
  rw [AlgEquiv.mul_apply]
  congr 1
  have : ∀ k : ℕ, ((σ ^ q) ^ k) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hq, ih]
  exact this _

theorem fix_mul (σ : F ≃ₐ[K] F) (x : F) (q a : ℕ) (hq : (σ ^ q) x = x) :
    (σ ^ (q * a)) x = x := by
  rw [fix_mod σ x q _ hq, Nat.mul_mod_right, pow_zero, AlgEquiv.one_apply]

theorem exists_frob_pow (τ : F ≃ₐ[K] F) : ∃ n : ℕ, frob K F ^ n = τ := by
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K F).2 τ
  exact ⟨n.1, hn⟩

theorem mem_range_of_frob_fix (x : F) (hx : frob K F x = x) : x ∈ Set.range (algebraMap K F) := by
  have : x ∈ (⊥ : IntermediateField K F) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    obtain ⟨n, rfl⟩ := exists_frob_pow (K := K) τ
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  rwa [IntermediateField.mem_bot] at this

theorem mem_range_of_fix_coprime (x : F) (a b : ℕ) (hab : Nat.Coprime a b)
    (ha : (frob K F ^ a) x = x) (hb : (frob K F ^ b) x = x) : x ∈ Set.range (algebraMap K F) := by
  have := fix_gcd _ x a b ha hb
  rw [hab, pow_one] at this
  exact mem_range_of_frob_fix x this

theorem fix_algebraMap (σ : F ≃ₐ[K] F) (c : K) : σ (algebraMap K F c) = algebraMap K F c :=
  σ.commutes c


-- PART B

theorem moore_det_ne_zero {h : ℕ} (y : Fin h → F) (hy : LinearIndependent K y) :
    Matrix.det (Matrix.of fun (u j : Fin h) => (frob K F ^ (u : ℕ)) (y j)) ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set qK := Fintype.card K with hqK
  have hq2 : 2 ≤ qK := Fintype.one_lt_card
  let L : F[X] := ∑ u : Fin h, C (v u) * X ^ (qK ^ (u : ℕ))
  have hinjE : Function.Injective (fun u : Fin h => qK ^ (u : ℕ)) :=
    (Nat.pow_right_injective hq2).comp Fin.val_injective
  obtain ⟨u0, hu0⟩ := Function.ne_iff.mp hv0
  have hcoeff : L.coeff (qK ^ (u0 : ℕ)) = v u0 := by
    simp only [L, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single u0]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h'
      exact hb (hinjE h'.symm)
    · simp
  have hL0 : L ≠ 0 := by
    intro h0
    rw [h0, coeff_zero] at hcoeff
    exact hu0 hcoeff.symm
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; exact absurd u0.2 (Nat.not_lt_zero _)
    · exact h0
  have hdeg : L.natDegree ≤ qK ^ (h - 1) := by
    apply natDegree_sum_le_of_forall_le
    intro u _
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  -- evaluation
  have heval : ∀ k : Fin h → K, L.eval (∑ j, k j • y j) = 0 := by
    intro k
    simp only [L, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    have : ∀ u : Fin h, (∑ j, k j • y j) ^ (qK ^ (u : ℕ)) = ∑ j, k j • (frob K F ^ (u : ℕ)) (y j) := by
      intro u
      rw [← frob_pow_apply, map_sum]
      simp [map_smul]
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have hj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hj
    rw [← smul_eq_zero_of_right (k j) hj, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [mul_smul_comm]
  have hinjS : Function.Injective (fun k : Fin h → K => ∑ j, k j • y j) := by
    intro k1 k2 hk
    have := (Fintype.linearIndependent_iff.mp hy) (k1 - k2) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hk)
    funext j
    exact sub_eq_zero.mp (this j)
  let Z : Finset F := Finset.univ.image (fun k : Fin h → K => ∑ j, k j • y j)
  have hZ : Z.card = qK ^ h := by
    rw [Finset.card_image_of_injective _ hinjS, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin]
  have hsub : Z.val ⊆ L.roots := by
    intro z hz
    have hz' : z ∈ Z := hz
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and] at hz'
    obtain ⟨k, rfl⟩ := hz'
    rw [mem_roots hL0]
    exact heval k
  have := card_le_degree_of_subset_roots hsub
  rw [hZ] at this
  have := this.trans hdeg
  have := Nat.pow_le_pow_iff_right (by omega : 2 ≤ qK) |>.mp this
  omega


-- PART C

theorem prod_natDegree_coeff {ι R : Type*} [CommRing R] (s : Finset ι) (f : ι → R[X]) (e : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ e i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨(natDegree_mul_le).trans (add_le_add hfa ih'.1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hfa ih'.1, ih'.2]

theorem det_natDegree_coeff {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R[X]) (e : n → ℕ) (hM : ∀ u j, (M u j).natDegree ≤ e j) :
    (M.det).natDegree ≤ ∑ j, e j ∧
      (M.det).coeff (∑ j, e j) = Matrix.det (Matrix.of fun u j => (M u j).coeff (e j)) := by
  rw [Matrix.det_apply, Matrix.det_apply]
  constructor
  · apply natDegree_sum_le_of_forall_le
    intro σ _
    refine (natDegree_smul_le _ _).trans ?_
    exact (prod_natDegree_coeff Finset.univ (fun i => M (σ i) i) e (fun i _ => hM _ _)).1
  · rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro σ _
    rw [coeff_smul, (prod_natDegree_coeff Finset.univ (fun i => M (σ i) i) e
      (fun i _ => hM _ _)).2]
    simp


-- PART D

theorem linIndep_of_natDegree {K : Type*} [Field K] {h : ℕ} (b : Fin h → K[X])
    (hmon : ∀ j, (b j).Monic) (hdeg : Function.Injective fun j => (b j).natDegree) :
    LinearIndependent K b := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro l hl
  by_contra hne
  push Not at hne
  set T := Finset.univ.filter fun j => l j ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨j, by simp [T, hj]⟩
  obtain ⟨j0, hj0T, hj0max⟩ := Finset.exists_max_image T (fun j => (b j).natDegree) hT
  have hc := congrArg (fun p => p.coeff (b j0).natDegree) hl
  simp only [finsetSum_coeff, coeff_smul, coeff_zero, smul_eq_mul] at hc
  rw [Finset.sum_eq_single j0] at hc
  · rw [(hmon j0).coeff_natDegree, mul_one] at hc
    simp [T] at hj0T
    exact hj0T hc
  · intro j _ hj
    by_cases hlj : l j = 0
    · simp [hlj]
    · have hjT : j ∈ T := by simp [T, hlj]
      have hle := hj0max j hjT
      have hlt : (b j).natDegree < (b j0).natDegree :=
        lt_of_le_of_ne hle (fun h' => hj (hdeg h'))
      rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  · simp

theorem echelon {K : Type*} [Field K] (B : ℕ) (Q : Submodule K K[X]) (hQB : Q ≤ degreeLT K B) :
    ∃ (h : ℕ) (b : Fin h → K[X]), (∀ j, b j ∈ Q) ∧ (∀ j, (b j).Monic) ∧
      Function.Injective (fun j => (b j).natDegree) ∧
      (∀ q ∈ Q, ∃ l : Fin h → K, ∑ j, l j • b j = q) := by
  classical
  let S : Finset ℕ := (Finset.range B).filter fun d => ∃ q ∈ Q, q.Monic ∧ q.natDegree = d
  have hS : ∀ d ∈ S, ∃ q ∈ Q, q.Monic ∧ q.natDegree = d := fun d hd => (Finset.mem_filter.mp hd).2
  choose! pick hpickQ hpickM hpickD using hS
  refine ⟨S.card, fun j => pick (S.orderEmbOfFin rfl j), fun j => hpickQ _ (S.orderEmbOfFin_mem rfl j),
    fun j => hpickM _ (S.orderEmbOfFin_mem rfl j), ?_, ?_⟩
  · intro i j hij
    simp only at hij
    rw [hpickD _ (S.orderEmbOfFin_mem rfl i), hpickD _ (S.orderEmbOfFin_mem rfl j)] at hij
    exact (S.orderEmbOfFin rfl).injective hij
  · intro q hq
    rw [← Submodule.mem_span_range_iff_exists_fun]
    -- strong induction on natDegree
    suffices H : ∀ N, ∀ q ∈ Q, q.natDegree ≤ N →
        q ∈ Submodule.span K (Set.range fun j => pick (S.orderEmbOfFin rfl j)) from
      H _ q hq le_rfl
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro q hq hqN
    by_cases hq0 : q = 0
    · rw [hq0]; exact Submodule.zero_mem _
    have hqB : q.natDegree < B := by
      have := hQB hq
      rw [mem_degreeLT] at this
      exact (natDegree_lt_iff_degree_lt hq0).mpr this
    have hdS : q.natDegree ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqB, ?_⟩
      refine ⟨C (q.leadingCoeff)⁻¹ * q, ?_, ?_, ?_⟩
      · rw [← smul_eq_C_mul]; exact Q.smul_mem _ hq
      · exact monic_C_mul_of_mul_leadingCoeff_eq_one
          (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hq0))
      · rw [natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0))]
    have hrange : q.natDegree ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hdS
    obtain ⟨j, hj⟩ := hrange
    set bj := pick (S.orderEmbOfFin rfl j) with hbj
    have hbjQ : bj ∈ Q := hpickQ _ (S.orderEmbOfFin_mem rfl j)
    have hbjM : bj.Monic := hpickM _ (S.orderEmbOfFin_mem rfl j)
    have hbjD : bj.natDegree = q.natDegree := by
      rw [hbj, hpickD _ (S.orderEmbOfFin_mem rfl j), hj]
    have hmem : bj ∈ Submodule.span K (Set.range fun j => pick (S.orderEmbOfFin rfl j)) :=
      Submodule.subset_span ⟨j, rfl⟩
    set q' := q - q.leadingCoeff • bj with hq'
    have hq'Q : q' ∈ Q := Q.sub_mem hq (Q.smul_mem _ hbjQ)
    have hqeq : q = q' + q.leadingCoeff • bj := by rw [hq']; ring
    rw [hqeq]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hmem)
    by_cases hq'0 : q' = 0
    · rw [hq'0]; exact Submodule.zero_mem _
    have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
    have hdeg : q'.degree < q.degree := by
      rw [hq']
      apply degree_sub_lt_left
      · rw [smul_eq_C_mul, degree_C_mul hlc, degree_eq_natDegree hq0,
          degree_eq_natDegree hbjM.ne_zero, hbjD]
      · exact hq0
      · rw [smul_eq_C_mul, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hlc), hbjM.leadingCoeff,
          mul_one]
    have hlt : q'.natDegree < q.natDegree := natDegree_lt_natDegree hq'0 hdeg
    exact ih q'.natDegree (lt_of_lt_of_le hlt hqN) q' hq'Q le_rfl


-- PART E

theorem pow_gcd_mem {G : Type*} [Group G] (H : Subgroup G) (x : G) (a b : ℕ)
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ^ Nat.gcd a b ∈ H := by
  have : x ^ ((Nat.gcd a b : ℕ) : ℤ) ∈ H := by
    rw [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)
  rwa [zpow_natCast] at this

theorem ne_zero_of_pow_not_mem (x : F) (p : ℕ) (hp : p ≠ 0)
    (hx : x ^ p ∉ Set.range (algebraMap K F)) : x ≠ 0 := by
  rintro rfl
  exact hx ⟨0, by rw [zero_pow hp, map_zero]⟩

theorem roots_distinct_aux (γ : F) (p : ℕ) (hp : p.Prime) (hγ : (frob K F ^ p) γ = γ)
    (hγ' : γ ^ p ∉ Set.range (algebraMap K F)) (c c' : K) (hc : c ≠ 0)
    (v v' : ℕ) (hv : v < p) (hvv : v' ≤ v)
    (heq : algebraMap K F c * (frob K F ^ v) γ = algebraMap K F c' * (frob K F ^ v') γ) :
    c = c' ∧ v = v' := by
  have hγ0 : γ ≠ 0 := ne_zero_of_pow_not_mem γ p hp.ne_zero hγ'
  set γ' := (frob K F ^ v') γ with hγ'def
  have hγ'0 : γ' ≠ 0 := by
    rw [hγ'def]; exact (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hγ0
  set e := v - v' with he
  have hve : v = e + v' := by omega
  have hfe : (frob K F ^ v) γ = (frob K F ^ e) γ' := by
    rw [hve, pow_add, AlgEquiv.mul_apply]
  rw [hfe] at heq
  by_cases he0 : e = 0
  · rw [he0, pow_zero, AlgEquiv.one_apply] at heq
    refine ⟨?_, by omega⟩
    have := mul_right_cancel₀ hγ'0 heq
    exact (algebraMap K F).injective this
  exfalso
  set lam : K := c' / c with hlam
  have hrel : (frob K F ^ e) γ' = algebraMap K F lam * γ' := by
    have hc' : algebraMap K F c ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc
    rw [hlam, map_div₀, div_mul_eq_mul_div, eq_div_iff hc', mul_comm _ (algebraMap K F c), heq]
  have hiter : ∀ m : ℕ, (frob K F ^ (e * m)) γ' = algebraMap K F (lam ^ m) * γ' := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, add_comm, pow_add, AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes,
        hrel, map_pow, map_pow, pow_succ]
      ring
  have hγ'p : (frob K F ^ p) γ' = γ' := by
    rw [hγ'def, ← AlgEquiv.mul_apply, ← pow_add, add_comm, pow_add, AlgEquiv.mul_apply, hγ]
  have hlamp : lam ^ p = 1 := by
    have h1 := hiter p
    rw [mul_comm, fix_mul _ _ _ _ hγ'p] at h1
    have h2 : algebraMap K F (lam ^ p) = algebraMap K F 1 := by
      rw [map_one]
      have := mul_right_cancel₀ hγ'0 (h1.symm.trans (one_mul γ').symm)
      exact this
    exact (algebraMap K F).injective h2
  have hfix1 : (frob K F ^ e) (γ' ^ p) = γ' ^ p := by
    rw [map_pow, hrel, mul_pow, ← map_pow, hlamp, map_one, one_mul]
  have hfix2 : (frob K F ^ p) (γ' ^ p) = γ' ^ p := by rw [map_pow, hγ'p]
  have hcop : Nat.Coprime e p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨κ, hκ⟩ := mem_range_of_fix_coprime (γ' ^ p) e p hcop hfix1 hfix2
  apply hγ'
  refine ⟨κ, ?_⟩
  have : γ ^ p = (frob K F ^ v').symm (γ' ^ p) := by
    rw [hγ'def, ← map_pow, AlgEquiv.symm_apply_apply]
  rw [this, ← hκ, AlgEquiv.commutes]

theorem roots_distinct (γ : F) (p : ℕ) (hp : p.Prime) (hγ : (frob K F ^ p) γ = γ)
    (hγ' : γ ^ p ∉ Set.range (algebraMap K F)) (c c' : K) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (v v' : ℕ) (hv : v < p) (hv' : v' < p)
    (heq : algebraMap K F c * (frob K F ^ v) γ = algebraMap K F c' * (frob K F ^ v') γ) :
    c = c' ∧ v = v' := by
  rcases le_total v' v with h | h
  · exact roots_distinct_aux γ p hp hγ hγ' c c' hc v v' hv h heq
  · have := roots_distinct_aux γ p hp hγ hγ' c' c hc' v' v hv' h heq.symm
    exact ⟨this.1.symm, this.2.symm⟩

theorem sum_le_natDegree_of_dvd {L : Type*} [Field L] (D : L[X]) (hD : D ≠ 0) {ι : Type*}
    (s : Finset ι) (a : ι → L) (ha : Set.InjOn a s) (m : ι → ℕ)
    (hdvd : ∀ i ∈ s, (X - C (a i)) ^ (m i) ∣ D) : ∑ i ∈ s, m i ≤ D.natDegree := by
  have hprod : ∏ i ∈ s, (X - C (a i)) ^ (m i) ∣ D := by
    apply Finset.prod_dvd_of_coprime _ hdvd
    intro i hi j hj hij
    apply IsCoprime.pow
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    exact fun h => hij (ha hi hj h)
  have := natDegree_le_of_dvd hprod hD
  rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))] at this
  simpa [natDegree_pow, natDegree_X_sub_C] using this

-- PART F

theorem comp_dvd_comp {L : Type*} [CommRing L] {A B : L[X]} (R : L[X]) (h : A ∣ B) :
    A.comp R ∣ B.comp R := by
  obtain ⟨w, rfl⟩ := h
  rw [mul_comp]
  exact dvd_mul_right _ _

theorem group_bound (γ δ : F) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hγ : (frob K F ^ p) γ = γ) (hγ' : γ ^ p ∉ Set.range (algebraMap K F))
    (hδ : (frob K F ^ q) δ = δ)
    {h : ℕ} (b : Fin h → K[X]) (hmon : ∀ j, (b j).Monic)
    (hli : LinearIndependent K (fun j => δ ^ (b j).natDegree))
    {ι : Type*} (T : Finset ι) (c : ι → K) (hc0 : ∀ k ∈ T, c k ≠ 0) (hcinj : Set.InjOn c T)
    (qs : ι → K[X]) (hqs0 : ∀ k ∈ T, qs k ≠ 0)
    (hqs : ∀ k ∈ T, ∃ l : Fin h → K, ∑ j, l j • b j = qs k) :
    p * ∑ k ∈ T, ((qs k).map (algebraMap K F)).rootMultiplicity (algebraMap K F (c k) * γ * δ)
      ≤ ∑ j, (b j).natDegree := by
  classical
  let M : Matrix (Fin h) (Fin h) F[X] := Matrix.of fun u j =>
    ((b j).map (algebraMap K F)).comp (C ((frob K F ^ (u : ℕ)) δ) * X)
  have hMdeg : ∀ u j, (M u j).natDegree ≤ (b j).natDegree := by
    intro u j
    refine natDegree_comp_le.trans ?_
    rw [natDegree_map]
    calc (b j).natDegree * (C ((frob K F ^ (u : ℕ)) δ) * X).natDegree
        ≤ (b j).natDegree * 1 :=
          Nat.mul_le_mul_left _ ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      _ = (b j).natDegree := mul_one _
  obtain ⟨hDdeg, hDcoeff⟩ := det_natDegree_coeff M (fun j => (b j).natDegree) hMdeg
  have hcoeffM : ∀ u j, (M u j).coeff ((b j).natDegree) =
      (frob K F ^ (u : ℕ)) (δ ^ (b j).natDegree) := by
    intro u j
    simp only [M, Matrix.of_apply, comp_C_mul_X_coeff, coeff_map, (hmon j).coeff_natDegree,
      map_one, one_mul, map_pow]
  have hD0 : M.det ≠ 0 := by
    intro h0
    apply moore_det_ne_zero (K := K) _ hli
    have : (Matrix.of fun u j => (M u j).coeff ((b j).natDegree)) =
        Matrix.of fun (u j : Fin h) => (frob K F ^ (u : ℕ)) (δ ^ (b j).natDegree) := by
      ext u j; exact hcoeffM u j
    rw [← this, ← hDcoeff, h0, coeff_zero]
  set t : ι → ℕ := fun k =>
    ((qs k).map (algebraMap K F)).rootMultiplicity (algebraMap K F (c k) * γ * δ) with ht
  have hdvd : ∀ k ∈ T, ∀ v < p,
      (X - C (algebraMap K F (c k) * (frob K F ^ v) γ)) ^ (t k) ∣ M.det := by
    intro k hk v hv
    obtain ⟨l, hl⟩ := hqs k hk
    have hl0 : ∃ j0, l j0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hqs0 k hk
      rw [← hl]
      simp [hcon]
    obtain ⟨j0, hj0⟩ := hl0
    set P := (qs k).map (algebraMap K F) with hPdef
    have hcol : ∀ u, ∑ j, C (algebraMap K F (l j)) • M u j =
        P.comp (C ((frob K F ^ (u : ℕ)) δ) * X) := by
      intro u
      simp only [M, Matrix.of_apply, hPdef, ← hl, Polynomial.map_sum, smul_eq_C_mul, sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.map_mul, map_C, mul_comp, C_comp, smul_eq_mul]
    set f := (X - C (algebraMap K F (c k) * (frob K F ^ v) γ)) ^ (t k) with hf
    have hentry : ∀ u : Fin h, f ∣ P.comp (C ((frob K F ^ (u : ℕ)) δ) * X) := by
      intro u
      have hco : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
      obtain ⟨s, hs1, hs2⟩ := Nat.chineseRemainder hco (u : ℕ) v
      set τ := frob K F ^ s with hτ
      have hτδ : τ δ = (frob K F ^ (u : ℕ)) δ := by
        rw [hτ, fix_mod _ δ q s hδ, hs1, ← fix_mod _ δ q _ hδ]
      have hτγ : τ γ = (frob K F ^ v) γ := by
        rw [hτ, fix_mod _ γ p s hγ, hs2, ← fix_mod _ γ p _ hγ]
      have h1 : (X - C (algebraMap K F (c k) * γ * δ)) ^ (t k) ∣ P := pow_rootMultiplicity_dvd P _
      have h2 := Polynomial.map_dvd (τ : F →+* F) h1
      have hPτ : P.map (τ : F →+* F) = P := by
        rw [hPdef, Polynomial.map_map]
        congr 1
        ext x
        simp
      rw [hPτ, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C] at h2
      have h3 := comp_dvd_comp (C ((frob K F ^ (u : ℕ)) δ) * X) h2
      refine dvd_trans ?_ h3
      have : (τ : F →+* F) (algebraMap K F (c k) * γ * δ) =
          algebraMap K F (c k) * (frob K F ^ v) γ * (frob K F ^ (u : ℕ)) δ := by
        show τ (algebraMap K F (c k) * γ * δ) = _
        rw [map_mul, map_mul, AlgEquiv.commutes, hτγ, hτδ]
      rw [this, pow_comp, sub_comp, X_comp, C_comp]
      have : C ((frob K F ^ (u : ℕ)) δ) * X -
          C (algebraMap K F (c k) * (frob K F ^ v) γ * (frob K F ^ (u : ℕ)) δ) =
          C ((frob K F ^ (u : ℕ)) δ) * (X - C (algebraMap K F (c k) * (frob K F ^ v) γ)) := by
        rw [C_mul, C_mul]; ring
      rw [this, mul_pow, hf]
      exact dvd_mul_left _ _
    choose w hw using hentry
    have hdet := Matrix.det_updateCol_sum M j0 (fun j => C (algebraMap K F (l j)))
    have hcolfun : (fun u => ∑ j, C (algebraMap K F (l j)) • M u j) = f • w := by
      funext u
      rw [hcol u, hw u, Pi.smul_apply, smul_eq_mul]
    rw [hcolfun, Matrix.det_updateCol_smul, smul_eq_mul] at hdet
    have hu : IsUnit (C (algebraMap K F (l j0))) := by
      apply isUnit_C.mpr
      rw [isUnit_iff_ne_zero]
      exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr hj0
    rw [← hu.dvd_mul_left, ← hdet]
    exact dvd_mul_right _ _
  have hinj : Set.InjOn (fun x : ι × ℕ => algebraMap K F (c x.1) * (frob K F ^ x.2) γ)
      (T ×ˢ Finset.range p : Finset (ι × ℕ)) := by
    rintro ⟨k, v⟩ hkv ⟨k', v'⟩ hkv' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hkv hkv'
    have := roots_distinct γ p hp hγ hγ' (c k) (c k') (hc0 k hkv.1) (hc0 k' hkv'.1) v v'
      hkv.2 hkv'.2 heq
    rw [hcinj hkv.1 hkv'.1 this.1, this.2]
  have hsum := sum_le_natDegree_of_dvd M.det hD0 (T ×ˢ Finset.range p) _ hinj (fun x => t x.1)
    (by
      rintro ⟨k, v⟩ hkv
      simp only [Finset.mem_product, Finset.mem_range] at hkv
      exact hdvd k hkv.1 v hkv.2)
  rw [Finset.sum_product] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  rw [Finset.mul_sum]
  exact hsum.trans hDdeg

-- PART G

theorem sparse_linIndep (δ : F) (B R : ℕ) {h : ℕ} (b : Fin h → K[X])
    (hdeg : Function.Injective fun j => (b j).natDegree)
    (hB : ∀ j, (b j).natDegree < B) (hh : h ≤ R)
    (hsparse : ∀ s : K[X], s ≠ 0 → s.natDegree < B → s.support.card ≤ R → aeval δ s ≠ 0) :
    LinearIndependent K (fun j => δ ^ (b j).natDegree) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro l hl j0
  by_contra hj0
  set d : Fin h → ℕ := fun j => (b j).natDegree with hd
  set s : K[X] := ∑ j, C (l j) * X ^ (d j) with hs
  have hcoeff : ∀ e, s.coeff e = ∑ j, if e = d j then l j else 0 := by
    intro e
    simp only [hs, finsetSum_coeff, coeff_C_mul_X_pow]
  have hs0 : s ≠ 0 := by
    intro h0
    have := hcoeff (d j0)
    rw [h0, coeff_zero, Finset.sum_eq_single j0] at this
    · simp at this; exact hj0 this.symm
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (hdeg h'.symm)
    · simp
  have hsdeg : s.natDegree < B := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0
      exact absurd j0.2 (Nat.not_lt_zero _)
    obtain ⟨jm, _, hjm⟩ := Finset.exists_max_image Finset.univ d ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
    refine lt_of_le_of_lt ?_ (hB jm)
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_X_pow_le _ _).trans (hjm j (Finset.mem_univ _))
  have hsupp : s.support ⊆ Finset.univ.image d := by
    intro e he
    rw [mem_support_iff, hcoeff] at he
    by_contra hne
    apply he
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro heq
    exact hne (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩)
  have hcard : s.support.card ≤ R :=
    (Finset.card_le_card hsupp).trans (Finset.card_image_le.trans (by simpa using hh))
  apply hsparse s hs0 hsdeg hcard
  rw [← hl]
  simp only [hs, hd, map_sum, map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]

theorem prime_coprime_mul {a b c d : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Nat.Coprime (a * b) (c * d) :=
  Nat.Coprime.mul_left (Nat.Coprime.mul_right ((Nat.coprime_primes ha hc).mpr hac)
      ((Nat.coprime_primes ha hd).mpr had))
    (Nat.Coprime.mul_right ((Nat.coprime_primes hb hc).mpr hbc)
      ((Nat.coprime_primes hb hd).mpr hbd))

end RSSDC

open RSSDC in
theorem RSSDConstr_isEffective_of_construction
    {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
    (n g r b : ℕ) (hn : 1 ≤ n) (hg : 1 ≤ g) (hr : 2 ≤ r) (hbn : b ≤ n)
    (P Q : Fin g → ℕ) (hP : ∀ i, (P i).Prime) (hQ : ∀ i, (Q i).Prime)
    (hdist : Function.Injective (Sum.elim P Q))
    (hPbig : ∀ i, g * 2 ^ r ≤ P i)
    (hdeg : Module.finrank K F = ∏ i, P i * Q i)
    (γ δ : Fin g → F)
    (hγ : ∀ i, γ i ^ (Fintype.card K ^ P i) = γ i)
    (hγ' : ∀ i, γ i ^ P i ∉ Set.range (algebraMap K F))
    (hδ : ∀ i, δ i ^ (Fintype.card K ^ Q i) = δ i)
    (hδ' : ∀ i, δ i ^ Q i ∉ Set.range (algebraMap K F))
    (hsparse : ∀ i, ∀ s : K[X], s ≠ 0 → s.natDegree < n * r → s.support.card ≤ 2 ^ r →
      aeval (δ i) s ≠ 0)
    (grp : Fin n → Fin g) (c : Fin n → K) (hc0 : ∀ k, c k ≠ 0)
    (hinj : ∀ k l, grp k = grp l → c k = c l → k = l)
    (hb : ∀ j, (Finset.univ.filter fun k => grp k = j).card ≤ b) :
    RSSubspaceDesign.IsEffective K n g b r
      (fun k => algebraMap K F (c k) * γ (grp k) * δ (grp k)) := by
  classical
  have hγF : ∀ i, (frob K F ^ P i) (γ i) = γ i := fun i => by rw [frob_pow_apply]; exact hγ i
  have hδF : ∀ i, (frob K F ^ Q i) (δ i) = δ i := fun i => by rw [frob_pow_apply]; exact hδ i
  have hγ0 : ∀ i, γ i ≠ 0 := fun i => ne_zero_of_pow_not_mem _ _ (hP i).ne_zero (hγ' i)
  have hδ0 : ∀ i, δ i ≠ 0 := fun i => ne_zero_of_pow_not_mem _ _ (hQ i).ne_zero (hδ' i)
  have hPQ : ∀ i j, P i ≠ Q j := fun i j h => by
    have := @hdist (Sum.inl i) (Sum.inr j) (by simpa using h)
    simp at this
  have hPP : ∀ i j, i ≠ j → P i ≠ P j := fun i j hij h => by
    have := @hdist (Sum.inl i) (Sum.inl j) (by simpa using h)
    simp at this; exact hij this
  have hQQ : ∀ i j, i ≠ j → Q i ≠ Q j := fun i j hij h => by
    have := @hdist (Sum.inr i) (Sum.inr j) (by simpa using h)
    simp at this; exact hij this
  have hcopd : ∀ i j, i ≠ j → Nat.Coprime (P i * Q i) (P j * Q j) := fun i j hij =>
    prime_coprime_mul (hP i) (hQ i) (hP j) (hQ j) (hPP i j hij) (hPQ i j)
      (fun h => hPQ j i h.symm) (hQQ i j hij)
  have hcopPQ : ∀ i, Nat.Coprime (P i) (Q i) := fun i => (Nat.coprime_primes (hP i) (hQ i)).mpr (hPQ i i)
  have hfixγ : ∀ i a, P i ∣ a → (frob K F ^ a) (γ i) = γ i := by
    rintro i a ⟨t, rfl⟩; exact fix_mul _ _ _ _ (hγF i)
  have hfixδ : ∀ i a, Q i ∣ a → (frob K F ^ a) (δ i) = δ i := by
    rintro i a ⟨t, rfl⟩; exact fix_mul _ _ _ _ (hδF i)
  have hfixα : ∀ k a, P (grp k) * Q (grp k) ∣ a →
      (frob K F ^ a) (algebraMap K F (c k) * γ (grp k) * δ (grp k)) =
        algebraMap K F (c k) * γ (grp k) * δ (grp k) := by
    intro k a ha
    rw [map_mul, map_mul, AlgEquiv.commutes, hfixγ _ _ (dvd_trans (dvd_mul_right _ _) ha),
      hfixδ _ _ (dvd_trans (dvd_mul_left _ _) ha)]
  refine ⟨hn, hg, hbn, hr, ?_, ?_, ?_⟩
  · -- injectivity
    intro k l hkl
    simp only at hkl
    by_cases hgl : grp k = grp l
    · rw [hgl, mul_assoc, mul_assoc] at hkl
      have h1 := mul_right_cancel₀ (mul_ne_zero (hγ0 _) (hδ0 _)) hkl
      exact hinj k l hgl ((algebraMap K F).injective h1)
    · exfalso
      have h1 := hfixα k _ (dvd_refl _)
      have h2 : (frob K F ^ (P (grp l) * Q (grp l)))
          (algebraMap K F (c k) * γ (grp k) * δ (grp k)) =
          algebraMap K F (c k) * γ (grp k) * δ (grp k) := by
        rw [hkl]; exact hfixα l _ (dvd_refl _)
      obtain ⟨κ, hκ⟩ := mem_range_of_fix_coprime _ _ _ (hcopd _ _ hgl) h1 h2
      have h3 : (frob K F ^ P (grp k)) (algebraMap K F (c k) * γ (grp k) * δ (grp k)) =
          algebraMap K F (c k) * γ (grp k) * δ (grp k) := by
        rw [← hκ, AlgEquiv.commutes]
      rw [map_mul, map_mul, AlgEquiv.commutes, hγF] at h3
      have h4 := mul_left_cancel₀ (mul_ne_zero
        ((map_ne_zero_iff _ (algebraMap K F).injective).mpr (hc0 k)) (hγ0 _)) h3
      obtain ⟨κ', hκ'⟩ := mem_range_of_fix_coprime _ _ _ (hcopPQ (grp k)) h4 (hδF _)
      exact hδ' (grp k) ⟨κ' ^ Q (grp k), by rw [map_pow, hκ']⟩
  · -- automorphisms
    set d : Fin g → ℕ := fun i => P i * Q i with hd
    set a : Fin g → ℕ := fun j => ∏ i ∈ Finset.univ.erase j, d i with ha
    refine ⟨fun j => frob K F ^ a j, ?_, ?_⟩
    · set H := Subgroup.closure (Set.range fun j => frob K F ^ a j) with hH
      have hd0 : ∀ i, 0 < d i := fun i => Nat.mul_pos (hP i).pos (hQ i).pos
      have key : ∀ s : Finset (Fin g), frob K F ^ (∏ i ∈ Finset.univ \ s, d i) ∈ H := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sdiff_empty]
          have : ∏ i, d i = Module.finrank K F := hdeg.symm
          rw [this, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, pow_orderOf_eq_one]
          exact H.one_mem
        | insert j s hj ih =>
          set A := ∏ i ∈ Finset.univ \ insert j s, d i with hA
          have hjmem : j ∈ Finset.univ \ s := by simp [hj]
          have e1 : ∏ i ∈ Finset.univ \ s, d i = d j * A := by
            rw [hA, Finset.sdiff_insert, Finset.mul_prod_erase _ _ hjmem]
          have e2 : a j = A * ∏ i ∈ s, d i := by
            have h1 : d j * a j = ∏ i, d i := Finset.mul_prod_erase _ _ (Finset.mem_univ j)
            have h2 := Finset.prod_sdiff (f := d) (Finset.subset_univ s)
            rw [e1] at h2
            have : d j * a j = d j * (A * ∏ i ∈ s, d i) := by rw [h1, ← h2]; ring
            exact Nat.eq_of_mul_eq_mul_left (hd0 j) this
          have hσ : frob K F ^ a j ∈ H := Subgroup.subset_closure ⟨j, rfl⟩
          rw [e1] at ih
          have := pow_gcd_mem H _ _ _ ih hσ
          have hcop : Nat.Coprime (d j) (∏ i ∈ s, d i) := by
            apply Nat.Coprime.prod_right
            intro i hi
            exact hcopd j i (fun h => hj (h ▸ hi))
          rwa [e2, mul_comm (d j), Nat.gcd_mul_left, hcop, mul_one] at this
      have hfrob : frob K F ∈ H := by
        have := key Finset.univ
        simpa using this
      rw [eq_top_iff]
      intro τ _
      obtain ⟨m, rfl⟩ := exists_frob_pow (K := K) τ
      exact H.pow_mem hfrob m
    · intro j
      refine (Finset.card_le_card ?_).trans (hb j)
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hne
      apply hk
      exact hfixα k _ (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩))
  · -- multiplicity bound
    intro Qs hQs hQs0 hdim qs hqs
    obtain ⟨h, bb, hbQ, hbmon, hbdeg, hspan⟩ := echelon (n * r) Qs hQs
    have hbB : ∀ j, (bb j).natDegree < n * r := by
      intro j
      have := hQs (hbQ j)
      rw [mem_degreeLT] at this
      exact (natDegree_lt_iff_degree_lt (hbmon j).ne_zero).mpr this
    have hh : h ≤ 2 ^ r := by
      have : FiniteDimensional K (degreeLT K (n * r)) :=
        LinearEquiv.finiteDimensional (degreeLTEquiv K (n * r)).symm
      have : FiniteDimensional K Qs := Submodule.finiteDimensional_of_le hQs
      have hli := linIndep_of_natDegree bb hbmon hbdeg
      have hli' : LinearIndependent K (fun j => (⟨bb j, hbQ j⟩ : Qs)) :=
        LinearIndependent.of_comp Qs.subtype hli
      have := hli'.fintype_card_le_finrank
      simp only [Fintype.card_fin] at this
      exact this.trans hdim
    have hh1 : 0 < h := by
      rcases Nat.eq_zero_or_pos h with h0 | hpos
      · exfalso
        subst h0
        obtain ⟨l, hl⟩ := hspan _ (hqs ⟨0, hn⟩).1
        apply (hqs ⟨0, hn⟩).2
        rw [← hl]
        simp
      · exact hpos
    obtain ⟨jm, _, hjm⟩ := Finset.exists_max_image Finset.univ (fun j => (bb j).natDegree)
      ⟨⟨0, hh1⟩, Finset.mem_univ _⟩
    refine ⟨bb jm, hbQ jm, (hbmon jm).ne_zero, ?_⟩
    set N := (bb jm).natDegree with hN
    have hsumdeg : ∑ j, (bb j).natDegree ≤ 2 ^ r * N := by
      calc ∑ j, (bb j).natDegree ≤ ∑ _j : Fin h, N :=
            Finset.sum_le_sum (fun j _ => hjm j (Finset.mem_univ _))
        _ = h * N := by simp
        _ ≤ 2 ^ r * N := Nat.mul_le_mul_right _ hh
    set t : Fin n → ℕ := fun k => ((qs k).map (algebraMap K F)).rootMultiplicity
      (algebraMap K F (c k) * γ (grp k) * δ (grp k)) with ht
    have hgroup : ∀ i, g * ∑ k ∈ Finset.univ.filter (fun k => grp k = i), t k ≤ N := by
      intro i
      have hli := sparse_linIndep (δ i) (n * r) (2 ^ r) bb hbdeg hbB hh (hsparse i)
      have := group_bound (γ i) (δ i) (P i) (Q i) (hP i) (hQ i) (hPQ i i) (hγF i) (hγ' i)
        (hδF i) bb hbmon hli (Finset.univ.filter (fun k => grp k = i)) c (fun k _ => hc0 k)
        (by
          intro k hk l hl hkl
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk hl
          exact hinj k l (hk.trans hl.symm) hkl)
        qs (fun k _ => (hqs k).2) (fun k _ => hspan _ (hqs k).1)
      have hEq : ∑ k ∈ Finset.univ.filter (fun k => grp k = i), t k =
          ∑ k ∈ Finset.univ.filter (fun k => grp k = i),
            ((qs k).map (algebraMap K F)).rootMultiplicity (algebraMap K F (c k) * γ i * δ i) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp only [ht, hk]
      rw [← hEq] at this
      have h2 := this.trans hsumdeg
      have h3 : g * 2 ^ r * ∑ k ∈ Finset.univ.filter (fun k => grp k = i), t k ≤ 2 ^ r * N :=
        (Nat.mul_le_mul_right _ (hPbig i)).trans h2
      have hpos : 0 < 2 ^ r := by positivity
      rw [mul_comm g, mul_assoc] at h3
      exact Nat.le_of_mul_le_mul_left h3 hpos
    have hfib : ∑ k, t k = ∑ i, ∑ k ∈ Finset.univ.filter (fun k => grp k = i), t k :=
      (Finset.sum_fiberwise Finset.univ grp t).symm
    have : g * ∑ k, t k ≤ g * N := by
      rw [hfib, Finset.mul_sum]
      calc ∑ i, g * ∑ k ∈ Finset.univ.filter (fun k => grp k = i), t k ≤ ∑ _i : Fin g, N :=
            Finset.sum_le_sum (fun i _ => hgroup i)
        _ = g * N := by simp
    exact Nat.le_of_mul_le_mul_left this (by omega)


-- ===================== Alg_correct.lean

open Polynomial RSSubspaceDesign

set_option linter.unusedSectionVars false

namespace RSSDAlg

section ACGeneric

theorem ac_findBelow_spec (test : ℕ → Bool) (N : ℕ) (h : ∃ j < N, test j = true) :
    test (findBelow test N) = true ∧ findBelow test N < N := by
  unfold findBelow
  cases hfind : (List.range N).find? test with
  | none =>
    exfalso
    obtain ⟨j, hj, hjt⟩ := h
    have := List.find?_eq_none.mp hfind j (List.mem_range.mpr hj)
    simp [hjt] at this
  | some x =>
    simp only [Option.getD_some]
    exact ⟨List.find?_some hfind, List.mem_range.mp (List.mem_of_find?_eq_some hfind)⟩

theorem ac_ofDigits_div_mod (B : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, x < B) (i : ℕ) :
    Nat.ofDigits B L / B ^ i % B = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp [Nat.ofDigits]
  | cons a L ih =>
    have ha : a < B := hL a (by simp)
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) ha
    rw [Nat.ofDigits_cons]
    cases i with
    | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    | succ i =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha,
        zero_add]
      simpa using ih (fun x hx => hL x (by simp [hx])) i

theorem ac_digits_ofDigits (B len : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, x < B) (hlen : L.length = len) :
    digits B len (Nat.ofDigits B L) = L := by
  unfold digits
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [ac_ofDigits_div_mod B L hL i, List.getD_eq_getElem _ _ h2]

theorem ac_digits_lt (B len j i : ℕ) (hB : 0 < B) : (digits B len j).getD i 0 < B := by
  unfold digits
  by_cases hi : i < len
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [Nat.mod_lt _ hB]
  · rw [List.getD_eq_default _ _ (by simpa using hi)]; exact hB

theorem ac_digits_length (B len j : ℕ) : (digits B len j).length = len := by
  simp [digits]

theorem ac_strictInc_iff (l : List ℕ) :
    strictInc l = true ↔ ∀ i, i + 1 < l.length → l.getD i 0 < l.getD (i + 1) 0 := by
  induction l with
  | nil => simp [strictInc]
  | cons a l ih =>
    cases l with
    | nil => simp [strictInc]
    | cons b l =>
      simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨hab, h⟩ i hi
        cases i with
        | zero => simpa using hab
        | succ i => simpa using h i (by simpa using hi)
      · intro h
        refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
        simpa using h (i + 1) (by simpa using hi)

theorem ac_strictInc_lt (l : List ℕ) (hl : strictInc l = true) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [ac_strictInc_iff] at hl
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact lt_trans (ih h (by omega)) (hl j hj)
    · subst h; exact hl i hj

theorem ac_strictInc_of (l : List ℕ) (h : ∀ i j, i < j → j < l.length → l.getD i 0 < l.getD j 0) :
    strictInc l = true := by
  rw [ac_strictInc_iff]
  intro i hi
  exact h i (i + 1) (by omega) hi

end ACGeneric

section ACField

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]

theorem ac_pow_card_eq_iff (x : F) :
    x ^ Fintype.card K = x ↔ x ∈ Set.range (algebraMap K F) := by
  constructor
  · intro h
    apply RSSDC.mem_range_of_frob_fix
    have := RSSDC.frob_pow_apply (K := K) 1 x
    rw [pow_one, pow_one] at this
    rw [this, h]
  · rintro ⟨c, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- elements of the degree-`e` subfield avoiding a small bad set -/
theorem ac_exists_sub (e : ℕ) (he : 0 < e) (hem : e ∣ Module.finrank K F) (bad : Finset F)
    (hbad : bad.card + e * Fintype.card K < Fintype.card K ^ e) :
    ∃ z : F, z ^ (Fintype.card K ^ e) = z ∧ z ^ e ∉ Set.range (algebraMap K F) ∧ z ∉ bad := by
  classical
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic K F
  set H : Subgroup (F ≃ₐ[K] F) := Subgroup.zpowers (σ ^ e)
  set L := IntermediateField.fixedField H
  have hm : 0 < Module.finrank K F := Module.finrank_pos
  have hord : orderOf σ = Module.finrank K F := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K F
  have hLF : Module.finrank L F = Module.finrank K F / e := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers,
      orderOf_pow_of_dvd he.ne' (hord ▸ hem), hord]
  have hKL : Module.finrank K L = e := by
    have h1 := Module.finrank_mul_finrank K L F
    rw [hLF] at h1
    obtain ⟨t, ht⟩ := hem
    rw [ht, Nat.mul_div_cancel_left _ he] at h1
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [ht, h] at hm; simp at hm
      · exact h
    exact Nat.eq_of_mul_eq_mul_right htpos h1
  have hcardL : Nat.card L = Fintype.card K ^ e := by
    rw [Module.natCard_eq_pow_finrank (K := K), hKL, Nat.card_eq_fintype_card]
  set Ls : Finset F := Finset.univ.filter (fun z => z ∈ L)
  have hLs : Ls.card = Fintype.card K ^ e := by
    rw [← hcardL, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun z => by simp [Ls]))
  set T : Finset F := Finset.univ.biUnion
    (fun c : K => (Polynomial.nthRoots e (algebraMap K F c)).toFinset)
  have hT : T.card ≤ e * Fintype.card K := by
    calc T.card ≤ ∑ c : K, (Polynomial.nthRoots e (algebraMap K F c)).toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _c : K, e := Finset.sum_le_sum fun c _ =>
          (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
      _ = e * Fintype.card K := by simp [mul_comm]
  have hlt : (bad ∪ T).card < Ls.card := by
    rw [hLs]
    exact lt_of_le_of_lt ((Finset.card_union_le _ _).trans (by omega)) hbad
  obtain ⟨z, hzL, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_union, not_or] at hz
  refine ⟨z, ?_, ?_, hz.1⟩
  · have hzL' : z ∈ L := by simpa [Ls] using hzL
    have := (IntermediateField.mem_fixedField_iff H z).mp hzL' (σ ^ e) (Subgroup.mem_zpowers _)
    rwa [RSSDC.frob_pow_apply] at this
  · rintro ⟨c, hc⟩
    apply hz.2
    simp only [T, Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset]
    exact ⟨c, (Polynomial.mem_nthRoots he).mpr hc.symm⟩

end ACField

section ACInst

variable {k : Type*} [Field k] (g : k[X]) [Fact (Irreducible g)]

instance acModFin : Module.Finite k (AdjoinRoot g) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero).finite

instance acFinite [Finite k] : Finite (AdjoinRoot g) := Module.finite_of_finite k

noncomputable instance acFintype [Finite k] : Fintype (AdjoinRoot g) := Fintype.ofFinite _

theorem ac_finrank : Module.finrank k (AdjoinRoot g) = g.natDegree := by
  rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero).finrank, AdjoinRoot.powerBasis_dim]

theorem ac_exists_irred [Finite k] (q : ℕ) [Fact q.Prime] [CharP k q] (m : ℕ) (hm : 1 ≤ m) :
    ∃ G : k[X], G.Monic ∧ Irreducible G ∧ G.natDegree = m := by
  have : NeZero m := ⟨by omega⟩
  set L := FiniteField.Extension k q m
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
    FiniteField.finrank_extension]

end ACInst

section ACK

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)]

theorem ac_df_pos : 1 ≤ f.natDegree :=
  Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_irreducible (Fact.out : Irreducible f))

theorem ac_cardK : Fintype.card (AdjoinRoot f) = p ^ f.natDegree := by
  rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, ac_finrank]

instance acCharP : CharP (AdjoinRoot f) p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) (AdjoinRoot f)).injective p

variable (hf : f.Monic)
include hf

theorem ac_isIrred_iff {m : ℕ} (hm : 1 ≤ m) {hc : List (List ℕ)}
    (hhc : IsMonicRep p f.natDegree m hc) :
    isIrred p (fcOf f) hc = true ↔ Irreducible (decPoly p f hc) := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  obtain ⟨hHm, hHd⟩ := decPoly_monic hf hf1 hhc
  have hlen : hc.length = m + 1 := hhc.1.1
  set Q := p ^ f.natDegree with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  set D := Q ^ (m - 1) with hD
  -- the semantics of one test
  have htest : ∀ J, J < (m - 1) * D → (irredTest p (fcOf f) hc J = true ↔
      ¬ decPoly p f (monicOfIdx p f.natDegree (J / D + 1) (J % D % Q ^ (J / D + 1))) ∣
        decPoly p f hc) := by
    intro J hJ
    have hJD : J / D < m - 1 := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hJ)
    have hG := monicOfIdx_spec hf hf1 (J / D + 1) (J % D % Q ^ (J / D + 1))
    obtain ⟨hk1, hk2⟩ := kpMod_spec hf hf1 hG hhc.1
    have hGm := (decPoly_monic hf hf1 hG).1
    unfold irredTest
    simp only [dg_fcOf hf hf1, hlen, Nat.add_sub_cancel, ← hQ, ← hD]
    rw [if_pos (by omega), Bool.not_eq_true', ← Bool.not_eq_true, kpIsZero_iff hf hf1 hk1, hk2,
      Polynomial.modByMonic_eq_zero_iff_dvd hGm]
  unfold isIrred irredBound
  rw [dg_fcOf hf hf1, hlen, Nat.add_sub_cancel, ← hQ, ← hD, List.all_eq_true]
  simp only [List.mem_range]
  constructor
  · intro hall
    rw [hHm.irreducible_iff_natDegree]
    refine ⟨fun h1 => ?_, fun a b ha hb hab => ?_⟩
    · rw [h1] at hHd; simp at hHd; omega
    · by_contra hne
      push Not at hne
      have hsum : a.natDegree + b.natDegree = m := by
        rw [← hHd, ← hab, ha.natDegree_mul hb]
      set d := a.natDegree with hd
      obtain ⟨j, hj, hjG⟩ := monicOfIdx_surj hf hf1 d a ha rfl
      have hjD : j < D := lt_of_lt_of_le hj (Nat.pow_le_pow_right hQ1 (by omega))
      set J := (d - 1) * D + j with hJ
      have hJdiv : J / D = d - 1 := by
        rw [hJ, mul_comm, Nat.mul_add_div (by omega : 0 < D), Nat.div_eq_of_lt hjD, add_zero]
      have hJmod : J % D = j := by
        rw [hJ, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hjD]
      have hJlt : J < (m - 1) * D := by
        calc J < (d - 1) * D + D := by omega
          _ = d * D := by
            obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
            rw [hd']; simp [add_mul]
          _ ≤ (m - 1) * D := Nat.mul_le_mul_right _ (by omega)
      have := (htest J hJlt).mp (hall J hJlt)
      rw [hJdiv, hJmod, Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.mod_eq_of_lt hj, hjG] at this
      exact this ⟨b, hab.symm⟩
  · intro hirr J hJ
    rw [htest J hJ]
    rintro ⟨u, hu⟩
    have hJD : J / D < m - 1 := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hJ)
    have hG := monicOfIdx_spec hf hf1 (J / D + 1) (J % D % Q ^ (J / D + 1))
    obtain ⟨hGm, hGd⟩ := decPoly_monic hf hf1 hG
    have hum : u.Monic := Polynomial.Monic.of_mul_monic_left hGm (hu ▸ hHm)
    rcases (hHm.irreducible_iff_natDegree.mp hirr).2 _ u hGm hum hu.symm with h | h
    · rw [hGd] at h; exact absurd h (Nat.succ_ne_zero _)
    · have := congrArg natDegree hu
      rw [hGm.natDegree_mul hum, hHd, hGd, h] at this
      omega

end ACK

section ACF

theorem ac_list_range_sum {M : Type*} [AddCommMonoid M] (φ : ℕ → M) (R : ℕ) :
    ((List.range R).map φ).sum = ∑ t ∈ Finset.range R, φ t := by
  induction R with
  | zero => simp
  | succ R ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)] (hf : f.Monic)
  {m : ℕ} (hm : 1 ≤ m) {hc : List (List ℕ)} (hhc : IsMonicRep p f.natDegree m hc)
include hf hm hhc

theorem ac_decF_eq_zero_iff {x : List (List ℕ)} (hx : IsMonicRep.IsCoeffList' p f.natDegree m x) :
    decF p f hc x = 0 ↔ decPoly p f x = 0 := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  obtain ⟨hHm, hHd⟩ := decPoly_monic hf hf1 hhc
  constructor
  · intro h
    rw [decF, AdjoinRoot.mk_eq_zero] at h
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h ?_
    rw [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero hHm), hHd]
    exact decPoly_degree_lt hf hf1 hx
  · intro h; simp [decF, h]

variable [Fact (Irreducible (decPoly p f hc))]

theorem ac_finrankF : Module.finrank (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)) = m := by
  rw [ac_finrank]; exact (decPoly_monic hf ac_df_pos hhc).2

theorem ac_subfieldTest_iff (e : ℕ) {x : List (List ℕ)}
    (hx : IsMonicRep.IsCoeffList' p f.natDegree m x) :
    subfieldTest p (fcOf f) hc e x = true ↔
      decF p f hc x ^ (Fintype.card (AdjoinRoot f) ^ e) = decF p f hc x ∧
        decF p f hc x ^ e ∉ Set.range (algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))) := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  rw [ac_cardK]
  obtain ⟨h1, h1'⟩ := fPow_spec hf hf1 hm hhc hx ((p ^ f.natDegree) ^ e)
  obtain ⟨h2, h2'⟩ := fPow_spec hf hf1 hm hhc hx e
  obtain ⟨h3, h3'⟩ := fPow_spec hf hf1 hm hhc h2 (p ^ f.natDegree)
  rw [← ac_pow_card_eq_iff, ac_cardK, ← h2', ← h3', ← h1']
  unfold subfieldTest
  simp only [dg_fcOf hf hf1, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨congrArg _ ha, fun h => hb (decF_inj hf hf1 hm hhc h3 h2 h)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨decF_inj hf hf1 hm hhc h1 hx ha, fun h => hb (congrArg _ h)⟩

end ACF

section ACS

/-- the `J`-th sparse polynomial of `sparseTest` -/
noncomputable def acSp (p : ℕ) (f : (ZMod p)[X]) (R E J : ℕ) : (AdjoinRoot f)[X] :=
  ∑ t ∈ Finset.range R, C (decK p f (kOfIdx p f.natDegree
    ((digits (p ^ f.natDegree) R (J % (p ^ f.natDegree) ^ R)).getD t 0))) *
    X ^ ((digits E R (J / (p ^ f.natDegree) ^ R)).getD t 0)

/-- the guard of the `J`-th sparse test -/
def acCond (p d R E J : ℕ) : Bool :=
  strictInc (digits E R (J / (p ^ d) ^ R)) &&
    (digits (p ^ d) R (J % (p ^ d) ^ R)).any (fun c => c != 0)

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)] (hf : f.Monic)
  {m : ℕ} (hm : 1 ≤ m) {hc : List (List ℕ)} (hhc : IsMonicRep p f.natDegree m hc)
  [Fact (Irreducible (decPoly p f hc))]
include hf hm hhc

theorem ac_sparse_foldl (es cs : List ℕ) {x : List (List ℕ)}
    (hx : IsMonicRep.IsCoeffList' p f.natDegree m x) (l : List ℕ) (a : List (List ℕ))
    (ha : IsMonicRep.IsCoeffList' p f.natDegree m a) :
    IsMonicRep.IsCoeffList' p f.natDegree m (l.foldl (fun acc t => kpAdd p acc
      (fMul p (fcOf f) hc (fEmbed (fcOf f) hc (kOfIdx p f.natDegree (cs.getD t 0)))
        (fPow p (fcOf f) hc x (es.getD t 0)))) a) ∧
    decF p f hc (l.foldl (fun acc t => kpAdd p acc
      (fMul p (fcOf f) hc (fEmbed (fcOf f) hc (kOfIdx p f.natDegree (cs.getD t 0)))
        (fPow p (fcOf f) hc x (es.getD t 0)))) a) =
      decF p f hc a + (l.map fun t => algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))
        (decK p f (kOfIdx p f.natDegree (cs.getD t 0))) * decF p f hc x ^ (es.getD t 0)).sum := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  induction l generalizing a with
  | nil => simp [ha]
  | cons t l ih =>
    rw [List.foldl_cons]
    obtain ⟨e1, e1'⟩ := fEmbed_spec hf hf1 hm hhc (kOfIdx_isK hf hf1 (cs.getD t 0))
    obtain ⟨e2, e2'⟩ := fPow_spec hf hf1 hm hhc hx (es.getD t 0)
    obtain ⟨e3, e3'⟩ := fMul_spec hf hf1 hm hhc e1 e2
    obtain ⟨e4, e4'⟩ := kpAdd_spec hf hf1 ha e3
    obtain ⟨i1, i2⟩ := ih _ e4
    refine ⟨i1, ?_⟩
    rw [i2]
    have : decF p f hc (kpAdd p a (fMul p (fcOf f) hc (fEmbed (fcOf f) hc
        (kOfIdx p f.natDegree (cs.getD t 0))) (fPow p (fcOf f) hc x (es.getD t 0)))) =
        decF p f hc a + decF p f hc (fMul p (fcOf f) hc (fEmbed (fcOf f) hc
        (kOfIdx p f.natDegree (cs.getD t 0))) (fPow p (fcOf f) hc x (es.getD t 0))) := by
      simp only [decF]; rw [e4', map_add]
    rw [this, e3', e1', e2', AdjoinRoot.algebraMap_eq, List.map_cons, List.sum_cons, add_assoc]

theorem ac_sparseTest_iff (R E J : ℕ) {x : List (List ℕ)}
    (hx : IsMonicRep.IsCoeffList' p f.natDegree m x) :
    sparseTest p (fcOf f) hc R E x J = true ↔
      (acCond p f.natDegree R E J = true → aeval (decF p f hc x) (acSp p f R E J) ≠ 0) := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  have hz : IsMonicRep.IsCoeffList' p f.natDegree m (fZero (fcOf f) hc) :=
    (fZero_spec hf hf1 hm hhc).1
  obtain ⟨r1, r2⟩ := ac_sparse_foldl hf hm hhc (digits E R (J / (p ^ f.natDegree) ^ R))
    (digits (p ^ f.natDegree) R (J % (p ^ f.natDegree) ^ R)) hx (List.range R) _ hz
  rw [(fZero_spec hf hf1 hm hhc).2, zero_add, ac_list_range_sum] at r2
  have haev : aeval (decF p f hc x) (acSp p f R E J) = ∑ t ∈ Finset.range R,
      algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))
        (decK p f (kOfIdx p f.natDegree
          ((digits (p ^ f.natDegree) R (J % (p ^ f.natDegree) ^ R)).getD t 0))) *
        decF p f hc x ^ ((digits E R (J / (p ^ f.natDegree) ^ R)).getD t 0) := by
    simp only [acSp, map_sum, map_mul, aeval_C, map_pow, aeval_X]
  unfold sparseTest acCond
  simp only [dg_fcOf hf hf1]
  split_ifs with hcond
  · rw [Bool.not_eq_true', ← Bool.not_eq_true, kpIsZero_iff hf hf1 r1,
      ← ac_decF_eq_zero_iff hf hm hhc r1, r2, haev]
    exact ⟨fun h _ => h, fun h => h hcond⟩
  · exact ⟨fun _ h => absurd h hcond, fun _ => rfl⟩

end ACS

section ACS2

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)] (hf : f.Monic)
include hf

theorem ac_kOfIdx_ne_zero {j : ℕ} (hj : j < p ^ f.natDegree) (hj0 : j ≠ 0) :
    decK p f (kOfIdx p f.natDegree j) ≠ 0 := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  intro h
  rw [← kOfIdx_zero hf hf1] at h
  exact hj0 (kOfIdx_inj hf hf1 hj (Nat.pow_pos (Fact.out : p.Prime).pos) h)

theorem ac_sp_prop {R E J : ℕ} (hE : 0 < E) (hcond : acCond p f.natDegree R E J = true) :
    acSp p f R E J ≠ 0 ∧ (acSp p f R E J).natDegree < E := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  have hQ : 0 < p ^ f.natDegree := Nat.pow_pos (Fact.out : p.Prime).pos
  set es := digits E R (J / (p ^ f.natDegree) ^ R) with hes
  set cs := digits (p ^ f.natDegree) R (J % (p ^ f.natDegree) ^ R) with hcs
  unfold acCond at hcond
  rw [← hes, ← hcs, Bool.and_eq_true, List.any_eq_true] at hcond
  obtain ⟨hinc, c, hcmem, hc0⟩ := hcond
  have hc0' : c ≠ 0 := by simpa using hc0
  constructor
  · obtain ⟨t0, ht0, rfl⟩ := List.getElem_of_mem hcmem
    have ht0R : t0 < R := by rwa [hcs, ac_digits_length] at ht0
    intro hzero
    have := congrArg (fun q => q.coeff (es.getD t0 0)) hzero
    simp only [acSp, ← hes, ← hcs, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single t0] at this
    · rw [if_pos rfl] at this
      have hlt : cs.getD t0 0 < p ^ f.natDegree := ac_digits_lt _ _ _ _ hQ
      rw [List.getD_eq_getElem _ 0 ht0] at this hlt
      exact ac_kOfIdx_ne_zero hf hlt hc0' this
    · intro t ht htne
      rw [if_neg]
      have htR : t < R := Finset.mem_range.mp ht
      have hlen : es.length = R := ac_digits_length _ _ _
      rcases lt_or_gt_of_ne htne with h | h
      · exact (ac_strictInc_lt es hinc h (by omega)).ne'
      · exact (ac_strictInc_lt es hinc h (by omega)).ne
    · intro h; exact absurd (Finset.mem_range.mpr ht0R) h
  · have : (acSp p f R E J).natDegree ≤ E - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro t _
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      have := ac_digits_lt E R (J / (p ^ f.natDegree) ^ R) t hE
      omega
    omega

end ACS2

section ACS3

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)] (hf : f.Monic)
include hf

theorem ac_sp_surj {R E : ℕ} (hRE : R ≤ E) (hE : 1 < E) (s : (AdjoinRoot f)[X]) (hs : s ≠ 0)
    (hdeg : s.natDegree < E) (hsupp : s.support.card ≤ R) :
    ∃ J < E ^ R * (p ^ f.natDegree) ^ R, acCond p f.natDegree R E J = true ∧ acSp p f R E J = s := by
  classical
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  have hQ1 : 1 < p ^ f.natDegree := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  set Q := p ^ f.natDegree with hQ
  have hsub : s.support ⊆ Finset.range E := fun i hi =>
    Finset.mem_range.mpr (lt_of_le_of_lt (le_natDegree_of_mem_supp i hi) hdeg)
  obtain ⟨S, hS1, hS2, hS3⟩ := Finset.exists_subsuperset_card_eq hsub hsupp (by simpa using hRE)
  set emb := S.orderEmbOfFin hS3
  set ef : ℕ → ℕ := fun t => if h : t < R then emb ⟨t, h⟩ else 0 with hef
  have hefS : ∀ t, t < R → ef t ∈ S := fun t ht => by
    simp only [hef, dif_pos ht]; exact S.orderEmbOfFin_mem hS3 _
  have hefE : ∀ t, t < R → ef t < E := fun t ht => Finset.mem_range.mp (hS2 (hefS t ht))
  have hcoef : ∀ t, ∃ j < Q, decK p f (kOfIdx p f.natDegree j) = s.coeff (ef t) :=
    fun t => kOfIdx_surj hf hf1 _
  choose jf hjf1 hjf2 using hcoef
  set es := (List.range R).map ef with hes
  set cs := (List.range R).map jf with hcs
  have hesl : es.length = R := by simp [hes]
  have hcsl : cs.length = R := by simp [hcs]
  have hesB : ∀ x ∈ es, x < E := by
    intro x hx; rw [hes, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx; exact hefE t (List.mem_range.mp ht)
  have hcsB : ∀ x ∈ cs, x < Q := by
    intro x hx; rw [hcs, List.mem_map] at hx
    obtain ⟨t, _, rfl⟩ := hx; exact hjf1 t
  have hesget : ∀ t, t < R → es.getD t 0 = ef t := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]; simp [hes]
  have hcsget : ∀ t, t < R → cs.getD t 0 = jf t := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]; simp [hcs]
  set A := Nat.ofDigits E es
  set B := Nat.ofDigits Q cs
  have hA : A < E ^ R := hesl ▸ Nat.ofDigits_lt_base_pow_length hE hesB
  have hB : B < Q ^ R := hcsl ▸ Nat.ofDigits_lt_base_pow_length hQ1 hcsB
  have hQR : 0 < Q ^ R := by positivity
  have hdiv : (A * Q ^ R + B) / Q ^ R = A := by
    rw [add_comm, Nat.add_mul_div_right _ _ hQR, Nat.div_eq_of_lt hB, zero_add]
  have hmod : (A * Q ^ R + B) % Q ^ R = B := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]
  have hdE : digits E R A = es := ac_digits_ofDigits E R es hesB hesl
  have hdQ : digits Q R B = cs := ac_digits_ofDigits Q R cs hcsB hcsl
  have hmono : ∀ i j, i < j → j < R → ef i < ef j := fun i j hij hj => by
    simp only [hef, dif_pos hj, dif_pos (lt_trans hij hj)]
    exact emb.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr hij)
  refine ⟨A * Q ^ R + B, ?_, ?_, ?_⟩
  · calc A * Q ^ R + B < A * Q ^ R + Q ^ R := by omega
      _ = (A + 1) * Q ^ R := by ring
      _ ≤ E ^ R * Q ^ R := Nat.mul_le_mul_right _ hA
  · unfold acCond
    rw [← hQ, hdiv, hmod, hdE, hdQ, Bool.and_eq_true]
    refine ⟨ac_strictInc_of es fun i j hij hj => ?_, ?_⟩
    · rw [hesget i (by omega), hesget j (by omega)]; exact hmono i j hij (by omega)
    · obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hs
      have hiS : i ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]; exact hS1 hi
      obtain ⟨t, ht⟩ := hiS
      rw [List.any_eq_true]
      refine ⟨jf t, List.mem_map.mpr ⟨t, List.mem_range.mpr t.2, rfl⟩, ?_⟩
      have h1 := hjf2 t
      have h2 : ef t = i := by simp only [hef, dif_pos t.2]; exact ht
      rw [h2] at h1
      have hne : jf t ≠ 0 := by
        intro h0
        rw [h0, kOfIdx_zero hf hf1] at h1
        exact (Polynomial.mem_support_iff.mp hi) h1.symm
      simpa using hne
  · unfold acSp
    rw [← hQ, hdiv, hmod, hdE, hdQ]
    have h1 : ∀ t ∈ Finset.range R, C (decK p f (kOfIdx p f.natDegree (cs.getD t 0))) *
        X ^ (es.getD t 0) = C (s.coeff (ef t)) * X ^ (ef t) := by
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [hcsget t ht', hesget t ht', hjf2]
    rw [Finset.sum_congr rfl h1, Finset.sum_range]
    have h2 : ∀ t : Fin R, C (s.coeff (ef t)) * X ^ (ef t) =
        (fun i => C (s.coeff i) * X ^ i) (emb.toEmbedding t) := by
      intro t; simp [hef, emb]
    rw [Fintype.sum_congr _ _ h2, ← Finset.sum_map Finset.univ emb.toEmbedding
      (fun i => C (s.coeff i) * X ^ i)]
    have h3 : Finset.univ.map emb.toEmbedding = S := Finset.map_orderEmbOfFin_univ S hS3
    rw [h3]
    conv_rhs => rw [Polynomial.as_sum_support_C_mul_X_pow s]
    symm
    apply Finset.sum_subset hS1
    intro i _ hi
    rw [Polynomial.notMem_support_iff.mp hi, C_0, zero_mul]

end ACS3

section ACSearch

theorem ac_lt_two_pow (e : ℕ) (he : 3 ≤ e) : e < 2 ^ (e - 1) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    rw [show e + 1 - 1 = (e - 1) + 1 by omega, pow_succ]; omega

theorem ac_ineq1 (Q e : ℕ) (hQ : 2 ≤ Q) (he : 3 ≤ e) : e * Q < Q ^ e := by
  have h1 : 2 ^ (e - 1) ≤ Q ^ (e - 1) := Nat.pow_le_pow_left hQ _
  have h2 := ac_lt_two_pow e he
  rw [show Q ^ e = Q ^ (e - 1) * Q by rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
  exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)] (hf : f.Monic)
  {m : ℕ} (hm : 1 ≤ m) {hc : List (List ℕ)} (hhc : IsMonicRep p f.natDegree m hc)
  [Fact (Irreducible (decPoly p f hc))]
include hf hm hhc

theorem ac_gam_spec (e : ℕ) (he : 3 ≤ e) (hem : e ∣ m) :
    IsMonicRep.IsCoeffList' p f.natDegree m (gamSearch p (fcOf f) hc e) ∧
    decF p f hc (gamSearch p (fcOf f) hc e) ^ (Fintype.card (AdjoinRoot f) ^ e) =
      decF p f hc (gamSearch p (fcOf f) hc e) ∧
    decF p f hc (gamSearch p (fcOf f) hc e) ^ e ∉
      Set.range (algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))) := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  have hN : (p ^ dg (fcOf f)) ^ (hc.length - 1) = (p ^ f.natDegree) ^ m := by
    rw [dg_fcOf hf hf1, hhc.1.1, Nat.add_sub_cancel]
  have hQ2 : 2 ≤ p ^ f.natDegree :=
    le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) _)
  obtain ⟨z, hz1, hz2, -⟩ := ac_exists_sub (K := AdjoinRoot f)
    (F := AdjoinRoot (decPoly p f hc)) e (by omega)
    (by rw [ac_finrankF hf hm hhc]; exact hem) ∅
    (by rw [Finset.card_empty, zero_add, ac_cardK]; exact ac_ineq1 _ _ hQ2 he)
  obtain ⟨j, hj, hjz⟩ := fOfIdx_surj hf hf1 hm hhc z
  have hex : ∃ j < (p ^ dg (fcOf f)) ^ (hc.length - 1),
      subfieldTest p (fcOf f) hc e (fOfIdx p (fcOf f) hc j) = true :=
    ⟨j, hN ▸ hj, by
      rw [ac_subfieldTest_iff hf hm hhc e (fOfIdx_spec hf hf1 hm hhc j), hjz]; exact ⟨hz1, hz2⟩⟩
  have := (ac_findBelow_spec _ _ hex).1
  unfold gamSearch
  have hspec := fOfIdx_spec hf hf1 hm hhc (findBelow (fun j => subfieldTest p (fcOf f) hc e
    (fOfIdx p (fcOf f) hc j)) ((p ^ dg (fcOf f)) ^ (hc.length - 1)))
  exact ⟨hspec, (ac_subfieldTest_iff hf hm hhc e hspec).mp this⟩

theorem ac_sparseOK_iff (R E : ℕ) {x : List (List ℕ)}
    (hx : IsMonicRep.IsCoeffList' p f.natDegree m x) :
    sparseOK p (fcOf f) hc R E x = true ↔ ∀ J < E ^ R * (p ^ f.natDegree) ^ R,
      (acCond p f.natDegree R E J = true → aeval (decF p f hc x) (acSp p f R E J) ≠ 0) := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  unfold sparseOK sparseBound
  rw [dg_fcOf hf hf1, List.all_eq_true]
  simp only [List.mem_range]
  exact forall₂_congr fun J _ => ac_sparseTest_iff hf hm hhc R E J hx

theorem ac_del_spec (e R E : ℕ) (he : 3 ≤ e) (hem : e ∣ m) (hRE : R ≤ E) (hE : 1 < E)
    (hbig : E ^ R * (p ^ f.natDegree) ^ R * E + e * p ^ f.natDegree < (p ^ f.natDegree) ^ e) :
    IsMonicRep.IsCoeffList' p f.natDegree m (delSearch p (fcOf f) hc e R E) ∧
    decF p f hc (delSearch p (fcOf f) hc e R E) ^ (Fintype.card (AdjoinRoot f) ^ e) =
      decF p f hc (delSearch p (fcOf f) hc e R E) ∧
    decF p f hc (delSearch p (fcOf f) hc e R E) ^ e ∉
      Set.range (algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))) ∧
    ∀ s : (AdjoinRoot f)[X], s ≠ 0 → s.natDegree < E → s.support.card ≤ R →
      aeval (decF p f hc (delSearch p (fcOf f) hc e R E)) s ≠ 0 := by
  classical
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  have hN : (p ^ dg (fcOf f)) ^ (hc.length - 1) = (p ^ f.natDegree) ^ m := by
    rw [dg_fcOf hf hf1, hhc.1.1, Nat.add_sub_cancel]
  set Q := p ^ f.natDegree with hQ
  set bad : Finset (AdjoinRoot (decPoly p f hc)) :=
    ((Finset.range (E ^ R * Q ^ R)).filter (fun J => acCond p f.natDegree R E J = true)).biUnion
      (fun J => ((acSp p f R E J).map
        (algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)))).roots.toFinset) with hbad
  have hbadc : bad.card ≤ E ^ R * Q ^ R * E := by
    calc bad.card ≤ ∑ J ∈ (Finset.range (E ^ R * Q ^ R)).filter
          (fun J => acCond p f.natDegree R E J = true),
          ((acSp p f R E J).map
            (algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)))).roots.toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ J ∈ (Finset.range (E ^ R * Q ^ R)).filter
          (fun J => acCond p f.natDegree R E J = true), E := by
          apply Finset.sum_le_sum
          intro J hJ
          have hc' := (Finset.mem_filter.mp hJ).2
          refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
          rw [Polynomial.natDegree_map]
          exact (ac_sp_prop hf (by omega) hc').2.le
      _ ≤ E ^ R * Q ^ R * E := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (by simp))
  obtain ⟨z, hz1, hz2, hz3⟩ := ac_exists_sub (K := AdjoinRoot f)
    (F := AdjoinRoot (decPoly p f hc)) e (by omega)
    (by rw [ac_finrankF hf hm hhc]; exact hem) bad
    (by rw [ac_cardK, ← hQ]; omega)
  have hzs : ∀ J < E ^ R * Q ^ R, acCond p f.natDegree R E J = true →
      aeval z (acSp p f R E J) ≠ 0 := by
    intro J hJ hcond h0
    apply hz3
    rw [hbad, Finset.mem_biUnion]
    refine ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hJ, hcond⟩, ?_⟩
    have hne := (Polynomial.map_ne_zero_iff (algebraMap (AdjoinRoot f)
      (AdjoinRoot (decPoly p f hc))).injective).mpr (ac_sp_prop hf (by omega) hcond).1
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, IsRoot.def, ← Polynomial.eval₂_eq_eval_map,
      ← aeval_def]
    exact h0
  obtain ⟨j, hj, hjz⟩ := fOfIdx_surj hf hf1 hm hhc z
  have hex : ∃ j < (p ^ dg (fcOf f)) ^ (hc.length - 1),
      (subfieldTest p (fcOf f) hc e (fOfIdx p (fcOf f) hc j) &&
        sparseOK p (fcOf f) hc R E (fOfIdx p (fcOf f) hc j)) = true := by
    refine ⟨j, hN ▸ hj, ?_⟩
    have hs := fOfIdx_spec hf hf1 hm hhc j
    rw [Bool.and_eq_true, ac_subfieldTest_iff hf hm hhc e hs, ac_sparseOK_iff hf hm hhc R E hs, hjz]
    exact ⟨⟨hz1, hz2⟩, hzs⟩
  have := (ac_findBelow_spec _ _ hex).1
  unfold delSearch
  have hspec := fOfIdx_spec hf hf1 hm hhc (findBelow (fun j =>
    subfieldTest p (fcOf f) hc e (fOfIdx p (fcOf f) hc j) &&
        sparseOK p (fcOf f) hc R E (fOfIdx p (fcOf f) hc j)) ((p ^ dg (fcOf f)) ^ (hc.length - 1)))
  rw [Bool.and_eq_true, ac_subfieldTest_iff hf hm hhc e hspec,
    ac_sparseOK_iff hf hm hhc R E hspec] at this
  refine ⟨hspec, this.1.1, this.1.2, fun s hs hdeg hsupp => ?_⟩
  obtain ⟨J, hJ, hcond, rfl⟩ := ac_sp_surj hf hRE hE s hs hdeg hsupp
  exact this.2 J hJ hcond

end ACSearch

section ACAssembly

theorem ac_ineq2 (Q n r e : ℕ) (hr : 2 ≤ r) (hnQ : n ≤ Q) (hQ : 2 ≤ Q)
    (he : r * (2 ^ r + 1) + 2 * 2 ^ r + 7 ≤ e) :
    (n * r) ^ (2 ^ r) * Q ^ (2 ^ r) * (n * r) + e * Q < Q ^ e := by
  set R := 2 ^ r with hR
  have hrQ : r ≤ Q ^ r := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hQ r)
  have h1 : n * r ≤ Q * Q ^ r := Nat.mul_le_mul hnQ hrQ
  set c := r * (R + 1) + 2 * R + 1 with hc
  have h2 : (n * r) ^ R * Q ^ R * (n * r) ≤ Q ^ c :=
    calc (n * r) ^ R * Q ^ R * (n * r) = (n * r) ^ (R + 1) * Q ^ R := by ring
      _ ≤ (Q * Q ^ r) ^ (R + 1) * Q ^ R := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 _)
      _ = Q ^ c := by rw [hc]; ring
  have h3 : 2 * Q ^ c ≤ Q ^ e := by
    have hce : c + 1 ≤ e := by omega
    calc 2 * Q ^ c ≤ Q * Q ^ c := Nat.mul_le_mul_right _ hQ
      _ = Q ^ (c + 1) := by ring
      _ ≤ Q ^ e := Nat.pow_le_pow_right (by omega) hce
  have h4 : 2 * (e * Q) < Q ^ e := by
    have hR4 : 4 ≤ R := by
      rw [hR]; calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have he5 : 5 ≤ e := by nlinarith
    have h5 := ac_lt_two_pow (e - 2) (by omega)
    have h6 : 2 ^ (e - 1) = 4 * 2 ^ (e - 2 - 1) := by
      rw [show e - 1 = (e - 2 - 1) + 2 by omega, pow_add]; ring
    have h7 : 2 * e < 2 ^ (e - 1) := by omega
    have h8 : 2 ^ (e - 1) ≤ Q ^ (e - 1) := Nat.pow_le_pow_left hQ _
    have h9 : Q ^ e = Q ^ (e - 1) * Q := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [h9, ← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  omega

variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]} [Fact (Irreducible f)] (hf : f.Monic)
include hf

theorem ac_hSearch_spec (m : ℕ) (hm : 1 ≤ m) :
    IsMonicRep p f.natDegree m (hSearch p (fcOf f) m) ∧
      Irreducible (decPoly p f (hSearch p (fcOf f) m)) := by
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  obtain ⟨G, hGm, hGi, hGd⟩ := ac_exists_irred (k := AdjoinRoot f) p m hm
  obtain ⟨j, hj, hjG⟩ := monicOfIdx_surj hf hf1 m G hGm hGd
  have hex : ∃ j < (p ^ f.natDegree) ^ m,
      isIrred p (fcOf f) (monicOfIdx p f.natDegree m j) = true :=
    ⟨j, hj, by rw [ac_isIrred_iff hf hm (monicOfIdx_spec hf hf1 m j), hjG]; exact hGi⟩
  have := (ac_findBelow_spec _ _ hex).1
  unfold hSearch
  simp only [dg_fcOf hf hf1]
  have hs := monicOfIdx_spec hf hf1 m (findBelow (fun j =>
    isIrred p (fcOf f) (monicOfIdx p f.natDegree m j)) ((p ^ f.natDegree) ^ m))
  exact ⟨hs, (ac_isIrred_iff hf hm hs).mp this⟩

end ACAssembly

-- @@F@@

/-- admissible parameters -/
def Params.Valid (P : Params) : Prop :=
  2 ≤ P.r ∧ 2 ≤ P.g ∧ P.Ps.length = P.g ∧ P.Qs.length = P.g ∧
    (∀ x ∈ P.Ps ++ P.Qs, x.Prime) ∧ (P.Ps ++ P.Qs).Nodup ∧
    (∀ x ∈ P.Ps, P.g * 2 ^ P.r ≤ x) ∧
    (∀ x ∈ P.Qs, P.r * (2 ^ P.r + 1) + 2 * 2 ^ P.r + 7 ≤ x)

/-- **Correctness of the construction.** -/
theorem construct_correct (P : Params) (hP : P.Valid) (p : ℕ) [Fact p.Prime]
    (f : (ZMod p)[X]) [Fact (Irreducible f)] (hf : f.Monic)
    (n : ℕ) (hng : P.g ≤ n) (hnR : 2 ^ P.r ≤ n) (hnK : n ≤ p ^ f.natDegree) :
    let out := construct P p (fcOf f) n
    IsCoeffList p f ((decPoly p f out.1).natDegree + 1) out.1 ∧
    out.2.length = n ∧ (∀ x ∈ out.2, IsCoeffList p f (decPoly p f out.1).natDegree x) ∧
    (decPoly p f out.1).Monic ∧ Irreducible (decPoly p f out.1) ∧
    (decPoly p f out.1).natDegree = P.m ∧
    ∃ _hα : Function.Injective
        (fun i : Fin n => AdjoinRoot.mk (decPoly p f out.1) (decPoly p f (out.2.getD i []))),
      ∀ [Fact (Irreducible (decPoly p f out.1))],
        IsEffective (AdjoinRoot f) n P.g (blk P.g n) P.r
          (fun i : Fin n => AdjoinRoot.mk (decPoly p f out.1) (decPoly p f (out.2.getD i []))) := by
  dsimp only
  obtain ⟨hr, hg, hPl, hQl, hprime, hnodup, hPbig, hQbig⟩ := hP
  have hf1 : 1 ≤ f.natDegree := ac_df_pos
  have hn2 : 2 ≤ n := le_trans hg hng
  -- products and prime lists
  set Pf : Fin P.g → ℕ := fun i => P.Ps.getD i 0 with hPfdef
  set Qf : Fin P.g → ℕ := fun i => P.Qs.getD i 0 with hQfdef
  have hPget : ∀ i : Fin P.g, Pf i = P.Ps[(i : ℕ)]'(by rw [hPl]; exact i.2) := fun i =>
    List.getD_eq_getElem _ _ _
  have hQget : ∀ i : Fin P.g, Qf i = P.Qs[(i : ℕ)]'(by rw [hQl]; exact i.2) := fun i =>
    List.getD_eq_getElem _ _ _
  have hPmem : ∀ i, Pf i ∈ P.Ps := fun i => by rw [hPget]; exact List.getElem_mem _
  have hQmem : ∀ i, Qf i ∈ P.Qs := fun i => by rw [hQget]; exact List.getElem_mem _
  have hPprime : ∀ i, (Pf i).Prime := fun i => hprime _ (List.mem_append_left _ (hPmem i))
  have hQprime : ∀ i, (Qf i).Prime := fun i => hprime _ (List.mem_append_right _ (hQmem i))
  have hmprod : P.m = ∏ i, Pf i * Qf i := by
    unfold Params.m
    have : List.zipWith (· * ·) P.Ps P.Qs = List.ofFn (fun i : Fin P.g => Pf i * Qf i) := by
      apply List.ext_getElem
      · simp [hPl, hQl]
      · intro i h1 h2
        simp only [List.getElem_zipWith, List.getElem_ofFn]
        rw [hPget ⟨i, by simpa using h2⟩, hQget ⟨i, by simpa using h2⟩]
    rw [this, List.prod_ofFn]
  have hm1 : 1 ≤ P.m := by
    rw [hmprod]; exact Finset.prod_pos fun i _ => Nat.mul_pos (hPprime i).pos (hQprime i).pos
  have hPdvd : ∀ i, Pf i ∣ P.m := fun i => by
    rw [hmprod]; exact (Dvd.intro _ rfl).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hQdvd : ∀ i, Qf i ∣ P.m := fun i => by
    rw [hmprod]; exact (Dvd.intro_left _ rfl).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hr4 : 4 ≤ 2 ^ P.r := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ P.r := Nat.pow_le_pow_right (by norm_num) hr
  have hP3 : ∀ i, 3 ≤ Pf i := fun i => by
    have := hPbig _ (hPmem i); nlinarith
  have hQ3 : ∀ i, 3 ≤ Qf i := fun i => by
    have := hQbig _ (hQmem i); omega
  -- block size
  set B := blk P.g n with hBdef
  have hB1 : 1 ≤ B := Nat.div_pos (by omega) (by omega)
  have hBn : B < n := by
    rw [hBdef, blk, Nat.div_lt_iff_lt_mul (by omega)]
    have : n + P.g < n * P.g + 1 := by nlinarith
    omega
  have hgB : n ≤ P.g * B := by
    have h1 := Nat.div_add_mod (n + P.g - 1) P.g
    have h2 := Nat.mod_lt (n + P.g - 1) (by omega : P.g > 0)
    rw [hBdef, blk]; omega
  have hkB : ∀ k, k < n → k / B < P.g := fun k hk =>
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := Nat.mul_comm B P.g; omega)
  have hQ2 : 2 ≤ p ^ f.natDegree :=
    le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) _)
  -- the field
  set hc := hSearch p (fcOf f) P.m with hhcdef
  obtain ⟨hhc, hirr⟩ := ac_hSearch_spec hf P.m hm1
  have hfact : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
  obtain ⟨hHm, hHd⟩ := decPoly_monic hf hf1 hhc
  set gams := P.Ps.map fun e => gamSearch p (fcOf f) hc e with hgamsdef
  set dels := P.Qs.map fun e => delSearch p (fcOf f) hc e (2 ^ P.r) (n * P.r) with hdelsdef
  have hcons : construct P p (fcOf f) n =
      (hc, (List.range n).map (point p (fcOf f) hc B gams dels)) := rfl
  rw [hcons]
  dsimp only
  have hgams : ∀ i (hi : i < P.g), gams.getD i [] = gamSearch p (fcOf f) hc (Pf ⟨i, hi⟩) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simp [hgamsdef, hPl, hi]), List.getElem_map, hPget]
  have hdels : ∀ i (hi : i < P.g), dels.getD i [] =
      delSearch p (fcOf f) hc (Qf ⟨i, hi⟩) (2 ^ P.r) (n * P.r) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simp [hdelsdef, hQl, hi]), List.getElem_map, hQget]
  have hγ := fun i : Fin P.g => ac_gam_spec hf hm1 hhc (Pf i) (hP3 i) (hPdvd i)
  have hRE : 2 ^ P.r ≤ n * P.r := le_trans hnR (Nat.le_mul_of_pos_right _ (by omega))
  have hE : 1 < n * P.r := by nlinarith
  have hδ := fun i : Fin P.g => ac_del_spec hf hm1 hhc (Qf i) (2 ^ P.r) (n * P.r) (hQ3 i) (hQdvd i)
    hRE hE (ac_ineq2 _ n P.r _ hr hnK hQ2 (hQbig _ (hQmem i)))
  set γ : Fin P.g → AdjoinRoot (decPoly p f hc) :=
    fun i => decF p f hc (gamSearch p (fcOf f) hc (Pf i)) with hγdef
  set δ : Fin P.g → AdjoinRoot (decPoly p f hc) :=
    fun i => decF p f hc (delSearch p (fcOf f) hc (Qf i) (2 ^ P.r) (n * P.r)) with hδdef
  set grp : Fin n → Fin P.g := fun k => ⟨k / B, hkB k k.2⟩ with hgrpdef
  set c : Fin n → AdjoinRoot f := fun k => decK p f (kOfIdx p f.natDegree (k % B + 1)) with hcdef
  have hpt : ∀ k : Fin n,
      IsMonicRep.IsCoeffList' p f.natDegree P.m (point p (fcOf f) hc B gams dels k) ∧
      decF p f hc (point p (fcOf f) hc B gams dels k) =
        algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)) (c k) * γ (grp k) * δ (grp k) := by
    intro k
    unfold point
    rw [dg_fcOf hf hf1, hgams _ (hkB k k.2), hdels _ (hkB k k.2)]
    obtain ⟨e1, e1'⟩ := fEmbed_spec hf hf1 hm1 hhc (kOfIdx_isK hf hf1 (k % B + 1))
    obtain ⟨e2, e2'⟩ := fMul_spec hf hf1 hm1 hhc (hγ (grp k)).1 (hδ (grp k)).1
    obtain ⟨e3, e3'⟩ := fMul_spec hf hf1 hm1 hhc e1 e2
    refine ⟨e3, ?_⟩
    rw [e3', e1', e2', AdjoinRoot.algebraMap_eq, mul_assoc]
  have hgetD : ∀ k : Fin n, ((List.range n).map (point p (fcOf f) hc B gams dels)).getD k [] =
      point p (fcOf f) hc B gams dels k := fun k => by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  have hfun : (fun i : Fin n => AdjoinRoot.mk (decPoly p f hc) (decPoly p f
      (((List.range n).map (point p (fcOf f) hc B gams dels)).getD i []))) =
      fun k => algebraMap (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)) (c k) * γ (grp k) *
        δ (grp k) := by
    funext k
    rw [hgetD k]
    exact (hpt k).2
  have hEff : IsEffective (AdjoinRoot f) n P.g B P.r (fun i : Fin n => AdjoinRoot.mk
      (decPoly p f hc) (decPoly p f
        (((List.range n).map (point p (fcOf f) hc B gams dels)).getD i []))) := by
    rw [hfun]
    have hdeg : Module.finrank (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)) = ∏ i, Pf i * Qf i := by
      rw [ac_finrankF hf hm1 hhc, hmprod]
    have hlenPQ : (P.Ps ++ P.Qs).length = P.g + P.g := by simp [hPl, hQl]
    have hPa : ∀ i : Fin P.g, Pf i = (P.Ps ++ P.Qs)[(i : ℕ)]'(by omega) := fun i => by
      rw [hPget, List.getElem_append_left]
    have hQa : ∀ j : Fin P.g, Qf j = (P.Ps ++ P.Qs)[P.g + (j : ℕ)]'(by omega) := fun j => by
      rw [hQget, List.getElem_append_right (by omega)]; congr 1; omega
    have hdist : Function.Injective (Sum.elim Pf Qf) := by
      intro x y hxy
      rcases x with i | i <;> rcases y with j | j <;>
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
      · rw [hPa, hPa, hnodup.getElem_inj_iff] at hxy; rw [Fin.ext hxy]
      · rw [hPa, hQa, hnodup.getElem_inj_iff] at hxy; omega
      · rw [hQa, hPa, hnodup.getElem_inj_iff] at hxy; omega
      · rw [hQa, hQa, hnodup.getElem_inj_iff] at hxy; rw [Fin.ext (by omega : (i : ℕ) = j)]
    have hkQ : ∀ k : Fin n, (k : ℕ) % B + 1 < p ^ f.natDegree := fun k => by
      have := Nat.mod_lt (k : ℕ) (by omega : B > 0); omega
    have hc0 : ∀ k, c k ≠ 0 := fun k => ac_kOfIdx_ne_zero hf (hkQ k) (Nat.succ_ne_zero _)
    have hinj : ∀ k l, grp k = grp l → c k = c l → k = l := by
      intro k l hkl hcl
      have h1 : (k : ℕ) / B = l / B := congrArg Fin.val hkl
      have h2 : (k : ℕ) % B + 1 = l % B + 1 := kOfIdx_inj hf hf1 (hkQ k) (hkQ l) hcl
      have h3 := Nat.div_add_mod (k : ℕ) B
      have h4 := Nat.div_add_mod (l : ℕ) B
      apply Fin.ext
      rw [← h3, ← h4, h1, show (k : ℕ) % B = l % B by omega]
    have hb : ∀ j, (Finset.univ.filter fun k => grp k = j).card ≤ B := by
      intro j
      calc (Finset.univ.filter fun k => grp k = j).card ≤ (Finset.range B).card :=
            Finset.card_le_card_of_injOn (fun k : Fin n => (k : ℕ) % B)
              (fun k _ => by simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.mod_lt _ (by omega))
              (by
                intro k hk l hl heq
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk hl
                have h1 : (k : ℕ) / B = l / B := by
                  rw [← hl] at hk; exact congrArg Fin.val hk
                have h3 := Nat.div_add_mod (k : ℕ) B
                have h4 := Nat.div_add_mod (l : ℕ) B
                simp only at heq
                apply Fin.ext
                rw [← h3, ← h4, h1, heq])
        _ = B := Finset.card_range B
    exact RSSDConstr_isEffective_of_construction n P.g P.r B (by omega) (by omega) hr hBn.le
      Pf Qf hPprime hQprime hdist (fun i => hPbig _ (hPmem i)) hdeg γ δ
      (fun i => (hγ i).2.1) (fun i => (hγ i).2.2) (fun i => (hδ i).2.1) (fun i => (hδ i).2.2.1)
      (fun i => (hδ i).2.2.2) grp c hc0 hinj hb
  refine ⟨?_, by simp, ?_, hHm, hirr, hHd, hEff.2.2.2.2.1, hEff⟩
  · rw [hHd, isCoeffList_iff hf hf1]; exact hhc.1
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    rw [hHd, isCoeffList_iff hf hf1]
    exact (hpt ⟨k, List.mem_range.mp hk⟩).1

end RSSDAlg


-- ===================== TM_Timed.lean

/-!
# Timed machines: a reusable library on top of `OAI.MetricKMedian.Binary`

* extra `Poly` automation (folds, arithmetic, take/drop/getD, all/any, ...);
* `Timed ea eb f T`: a machine computing `f` within explicit time `T` (not necessarily polynomial),
  with `ofPoly`, `comp`, `mono`, `congr`, `thread`/`second`/`product`/`fanout`, `ite`;
* loops whose body is itself `Timed` (`loopT`, `loopFrom`);
* exponential search combinators `findBelow` / `allBelow` / `existsBelow`;
* the bridge to `HMBinPacking.OutputsWithin`.
-/

set_option linter.unusedSectionVars false

section RSSDTM_Lib

namespace RSSDTM

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

section Size

theorem enc_nat (a : ℕ) : (enc a).length = a.size := Nat.size_eq_bits_len a

theorem enc_bool (b : Bool) : (enc b).length = 1 := rfl

theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.2 (Nat.lt_two_pow_self)

theorem size_add (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.2
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ a.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ b.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem enc_nat_mono {a b : ℕ} (h : a ≤ b) : (enc a).length ≤ (enc b).length := by
  rw [enc_nat, enc_nat]; exact Nat.size_le_size h

theorem enc_list_nat_le (l : List ℕ) (S : ℕ) (h : ∀ a ∈ l, a.size ≤ S) :
    (enc l).length ≤ l.length * (2 * S + 1) :=
  EncodedList.length_bound _ l S (fun a ha => by rw [enc_nat]; exact h a ha)

theorem length_le_enc {β : Type} [Coding β] (l : List β) : l.length ≤ (enc l).length :=
  EncodedList.length_le _ l

theorem enc_pair (α β : Type) [Coding α] [Coding β] (x : α × β) :
    (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length := encodePair_length _ _ _

@[simp] theorem enc_pair_mk {α β : Type} [Coding α] [Coding β] (a : α) (b : β) :
    (enc (a, b)).length = 2 * (enc a).length + 1 + (enc b).length := encodePair_length _ _ _

theorem enc_list_append {β : Type} [Coding β] (l l' : List β) :
    (enc (l ++ l')).length = (enc l).length + (enc l').length := by
  change (encodeList enc (l ++ l')).length = _
  rw [EncodedList.append, List.length_append]; rfl

theorem enc_list_cons {β : Type} [Coding β] (a : β) (l : List β) :
    (enc (a :: l)).length = 2 * (enc a).length + 1 + (enc l).length := EncodedList.cons_length _ _ _

theorem enc_mem_le {β : Type} [Coding β] (l : List β) (a : β) (h : a ∈ l) :
    (enc a).length ≤ (enc l).length := EncodedList.member_length _ l a h

theorem enc_take_le {β : Type} [Coding β] (l : List β) (k : ℕ) :
    (enc (l.take k)).length ≤ (enc l).length := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [enc_list_append]; omega

theorem enc_drop_le {β : Type} [Coding β] (l : List β) (k : ℕ) :
    (enc (l.drop k)).length ≤ (enc l).length := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [enc_list_append]; omega

theorem enc_bool_list (w : List Bool) : (enc w).length = 3 * w.length := BooleanLists.length w

end Size

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

section
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem foldl_env (f : α → β → γ → β) (x : α) (l : List γ) (b : β) :
    l.foldl (fun (p : α × β) a => (p.1, f p.1 p.2 a)) (x, b) = (x, l.foldl (f x) b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact ih _

theorem fold_size (f : α → β → γ → β) (G : Polynomial ℕ)
    (hG : ∀ x b a, (enc (f x b a)).length ≤ (enc b).length + G.eval ((enc x).length + (enc a).length))
    (x : α) (M : ℕ) (pre : List γ) (hpre : ∀ a ∈ pre, (enc a).length ≤ M) (acc : β) :
    (enc (pre.foldl (f x) acc)).length ≤ (enc acc).length + pre.length * G.eval ((enc x).length + M) := by
  induction pre generalizing acc with
  | nil => simp
  | cons a pre ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (fun a' ha' => hpre a' (List.mem_cons_of_mem _ ha')) (f x acc a)
    have h2 := hG x acc a
    have h3 := polynomial_eval_mono G (show (enc x).length + (enc a).length ≤ (enc x).length + M by
      have := hpre a (List.mem_cons_self); omega)
    nlinarith

theorem Poly.list_foldl [Inhabited γ] {f : α → β → γ → β} {as : α → List γ} {b0 : α → β}
    (hf : Poly (fun y : (α × β) × γ => f y.1.1 y.1.2 y.2)) (has : Poly as) (hb0 : Poly b0)
    (G : Polynomial ℕ)
    (hG : ∀ x b a, (enc (f x b a)).length ≤ (enc b).length + G.eval ((enc x).length + (enc a).length)) :
    Poly (fun x => (as x).foldl (f x) (b0 x)) := by
  have hop : Poly (fun y : (α × β) × γ => (y.1.1, f y.1.1 y.1.2 y.2)) :=
    Poly.pair (Poly.comp Poly.fst Poly.fst) hf
  let P : PolyProgram (encodePair (encodePair enc enc) enc) (encodePair enc enc)
      (fun y : (α × β) × γ => (y.1.1, f y.1.1 y.1.2 y.2)) := hop.program
  let FP := PolyProgram.listFold (ea := (enc : γ → List Bool)) (eb := encodePair (enc : α → List Bool) (enc : β → List Bool))
    P default (X + X * G) (by
      intro as' b' pre suf hsplit
      obtain ⟨x, acc⟩ := b'
      rw [foldl_env]
      have hpre : ∀ a ∈ pre, (enc a).length ≤ (encodeList enc as').length := by
        intro a ha
        exact EncodedList.member_length _ as' a (by rw [hsplit]; exact List.mem_append_left _ ha)
      have hs := fold_size f G hG x _ pre hpre acc
      have hlen : pre.length ≤ (encodeList enc as').length := by
        have h1 := EncodedList.length_le (enc : γ → List Bool) as'
        have h2 : pre.length ≤ as'.length := by rw [hsplit, List.length_append]; omega
        omega
      simp only [encodePair_length, eval_add, eval_X, eval_mul]
      set L := 2 * (encodeList enc as').length + 1 + (2 * (enc x).length + 1 + (enc acc).length)
      have hG' := polynomial_eval_mono G (show (enc x).length + (encodeList enc as').length ≤ L by omega)
      have hm : pre.length * G.eval ((enc x).length + (encodeList enc as').length) ≤ L * G.eval L :=
        Nat.mul_le_mul (by omega) hG'
      change 2 * (enc x).length + 1 + (enc (pre.foldl (f x) acc)).length ≤ L + L * G.eval L
      omega)
  have hFP : Poly (fun z : List γ × (α × β) =>
      z.1.foldl (fun b a => (fun y : (α × β) × γ => (y.1.1, f y.1.1 y.1.2 y.2)) (b, a)) z.2) := ⟨FP⟩
  have hin : Poly (fun x => (as x, (x, b0 x))) := by fun_prop
  have h := Poly.comp Poly.snd (Poly.comp hFP hin)
  simp only [foldl_env] at h
  exact h

end

section Arith
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem Poly.nat_mod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem Poly.nat_div : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem Poly.nat_mod_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x % g x) := Poly.comp Poly.nat_mod (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_div_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) := Poly.comp Poly.nat_div (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_add_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_mul_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.nat_mul (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_sub_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)
@[fun_prop] theorem Poly.bool_and_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) := Poly.comp Poly.bool_and (Poly.pair hf hg)
@[fun_prop] theorem Poly.bool_or_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x || g x) := Poly.comp Poly.bool_or (Poly.pair hf hg)
@[fun_prop] theorem Poly.bool_not_comp {f : α → Bool} (hf : Poly f) :
    Poly (fun x => !f x) := Poly.comp Poly.bool_not hf
@[fun_prop] theorem Poly.nat_beq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) := by
  have h := Poly.nat_eq_comp hf hg
  have he : (fun x => decide (f x = g x)) = (fun x => f x == g x) := by
    funext x; cases h : (f x == g x) <;> simp_all
  rwa [he] at h

theorem list_all_eq_findIdx {γ : Type} (l : List γ) (p : γ → Bool) :
    l.all p = (l.findIdx (fun b => !p b) == l.length) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.all_cons, List.findIdx_cons, List.length_cons]
    cases h : p a <;> simp [ih]

@[fun_prop] theorem Poly.list_all [Inhabited β] {p : α → β → Bool} {as : α → List β}
    (hp : Poly (fun x : α × β => p x.1 x.2)) (ha : Poly as) : Poly (fun x => (as x).all (p x)) := by
  have h : Poly (fun x => ((as x).findIdx (fun b => !p x b) == (as x).length)) := by fun_prop
  simpa only [← list_all_eq_findIdx] using h

@[fun_prop] theorem Poly.list_take [Inhabited β] : Poly (fun x : List β × ℕ => x.1.take x.2) :=
  ⟨PolyProgram.listTake enc default⟩
@[fun_prop] theorem Poly.list_drop [Inhabited β] : Poly (fun x : List β × ℕ => x.1.drop x.2) :=
  ⟨PolyProgram.listDrop enc default⟩
@[fun_prop] theorem Poly.list_take_comp [Inhabited β] {l : α → List β} {k : α → ℕ} (hl : Poly l) (hk : Poly k) :
    Poly (fun x => (l x).take (k x)) := Poly.comp Poly.list_take (Poly.pair hl hk)
@[fun_prop] theorem Poly.list_drop_comp [Inhabited β] {l : α → List β} {k : α → ℕ} (hl : Poly l) (hk : Poly k) :
    Poly (fun x => (l x).drop (k x)) := Poly.comp Poly.list_drop (Poly.pair hl hk)
@[fun_prop] theorem Poly.list_append_comp [Inhabited β] {l l' : α → List β} (hl : Poly l) (hl' : Poly l') :
    Poly (fun x => l x ++ l' x) := Poly.comp Poly.list_append (Poly.pair hl hl')
@[fun_prop] theorem Poly.list_length_comp [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => (l x).length) := Poly.comp Poly.list_length hl
@[fun_prop] theorem Poly.list_range_length [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => List.range (l x).length) :=
  Poly.comp (f := fun xs : List β => List.range xs.length) Poly.list_indices hl
@[fun_prop] theorem Poly.list_zip_comp [Inhabited β] {γ : Type} [Coding γ] [Inhabited γ]
    {l : α → List β} {l' : α → List γ} (hl : Poly l) (hl' : Poly l') :
    Poly (fun x => (l x).zip (l' x)) := Poly.comp Poly.list_zip (Poly.pair hl hl')
@[fun_prop] theorem Poly.list_cons_comp {a : α → β} {l : α → List β} (ha : Poly a) (hl : Poly l) :
    Poly (fun x => a x :: l x) := Poly.comp Poly.list_cons (Poly.pair ha hl)

@[fun_prop] theorem Poly.list_getD_fn (d : β) {l : α → List β} {i : α → ℕ} (hl : Poly l) (hi : Poly i) :
    Poly (fun x => (l x).getD (i x) d) := by
  simp only [List.getD_eq_getElem?_getD]
  exact Poly.list_getD_comp d hl hi

theorem getD_var {γ : Type} [Inhabited γ] (l : List γ) (i : ℕ) (d : γ) :
    l.getD i d = if i < l.length then l.getD i default else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default _ _ (by omega)]

@[fun_prop] theorem Poly.list_getD_var [Inhabited β] {l : α → List β} {i : α → ℕ} {d : α → β}
    (hl : Poly l) (hi : Poly i) (hd : Poly d) : Poly (fun x => (l x).getD (i x) (d x)) := by
  simp only [getD_var (l _) (i _) (d _)]
  fun_prop

@[fun_prop] theorem Poly.nat_min_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => min (f x) (g x)) := by
  have : (fun x => min (f x) (g x)) = (fun x => if f x ≤ g x then f x else g x) := by
    funext x; split_ifs with h <;> omega
  rw [this]; fun_prop

@[fun_prop] theorem Poly.nat_max_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => max (f x) (g x)) := by
  have : (fun x => max (f x) (g x)) = (fun x => if f x ≤ g x then g x else f x) := by
    funext x; split_ifs with h <;> omega
  rw [this]; fun_prop

/-- `List.range k` for a number `k` given in binary is *not* polynomial; we provide it when the
number is bounded by the length of a list in the input. -/
theorem range_eq_take (k : ℕ) (l : List β) (h : k ≤ l.length) :
    List.range k = (List.range l.length).take k := by
  rw [List.take_range, Nat.min_eq_left h]

@[fun_prop] theorem Poly.list_reverse [Inhabited β] : Poly (List.reverse : List β → List β) :=
  ⟨PolyProgram.listReverse enc default⟩
@[fun_prop] theorem Poly.list_reverse_comp [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => (l x).reverse) := Poly.comp Poly.list_reverse hl

theorem list_any_eq_not_all {γ : Type} (l : List γ) (p : γ → Bool) :
    l.any p = !(l.all (fun b => !p b)) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.any_cons, List.all_cons, ih]; cases p a <;> simp

@[fun_prop] theorem Poly.list_any [Inhabited β] {p : α → β → Bool} {as : α → List β}
    (hp : Poly (fun x : α × β => p x.1 x.2)) (ha : Poly as) : Poly (fun x => (as x).any (p x)) := by
  have h : Poly (fun x => !((as x).all (fun b => !p x b))) := by fun_prop
  simpa only [← list_any_eq_not_all] using h

@[fun_prop] theorem Poly.nat_pow_const (k : ℕ) {f : α → ℕ} (hf : Poly f) : Poly (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using Automatic.Poly.const (α := α) (1 : ℕ)
  | succ k ih => simpa only [pow_succ] using Poly.nat_mul_comp ih hf

@[fun_prop] theorem Poly.nat_lt_bool {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := Poly.nat_lt_comp hf hg

end Arith


end RSSDTM

end RSSDTM_Lib

section RSSDTM_Timed

/-! # Machines with explicit (non-polynomial) running times -/

namespace RSSDTM

open OAI.MetricKMedian.Binary Polynomial

/-- A machine computing `f` from `ea`-codes to `eb`-codes within `T a` steps. -/
structure Timed {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) (T : α → ℕ) where
  machine : Machine
  run : ∀ a, ∃ t, t ≤ T a ∧ Trace machine.step t (machine.initialCfg (ea a)) (machine.finalCfg (eb (f a)))

theorem exchange_time {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (n : ℕ) :
    (PolyProgram.exchange ea eb).time.eval n = 3 * n + 5 := by
  show (WordTransducer.exchange.program.time).eval n = _
  simp [ParallelTransducer.program, show WordTransducer.exchange.width = 2 by decide]

theorem duplicate_time {α : Type} (ea : α → List Bool) (n : ℕ) :
    (PolyProgram.duplicate ea).time.eval n = 4 * n + 6 := by
  show (WordTransducer.duplicate.program.time).eval n = _
  simp [ParallelTransducer.program, show WordTransducer.duplicate.width = 3 by decide]

theorem identity_time {α : Type} (ea : α → List Bool) (n : ℕ) :
    (PolyProgram.identity ea).time.eval n = 2 * n + 3 := by
  show (WordTransducer.identity.program.time).eval n = _
  simp [Transducer.program, show WordTransducer.identity.width = 1 by decide]

theorem select_time {β : Type} (eb : β → List Bool) (n : ℕ) :
    (PolyProgram.select eb).time.eval n = 2 * n + 3 := by
  show (WordTransducer.select.program.time).eval n = _
  simp [Transducer.program, show WordTransducer.select.width = 1 by decide]

namespace Timed

variable {α β γ δ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {ed : δ → List Bool}

noncomputable def ofPoly {f : α → β} (P : PolyProgram ea eb f) :
    Timed ea eb f (fun a => P.time.eval (ea a).length) where
  machine := P.machine
  run a := by
    have hp := P.outputs a
    exact ⟨hp.steps, hp.steps_le_m, Trace.of_iterate hp.evals_in_steps⟩

noncomputable def comp {f : α → β} {g : β → γ} {T1 : α → ℕ} {T2 : β → ℕ}
    (P : Timed ea eb f T1) (Q : Timed eb ec g T2) :
    Timed ea ec (fun a => g (f a)) (fun a => T1 a + 2 * (eb (f a)).length + 2 + T2 (f a)) where
  machine := Compose.machine P.machine Q.machine
  run a := by
    obtain ⟨t1, h1, tr1⟩ := P.run a
    obtain ⟨t2, h2, tr2⟩ := Q.run (f a)
    exact ⟨_, by omega, Compose.run P.machine Q.machine tr1 tr2⟩

noncomputable def mono {f : α → β} {T T' : α → ℕ} (P : Timed ea eb f T) (h : ∀ a, T a ≤ T' a) :
    Timed ea eb f T' where
  machine := P.machine
  run a := by
    obtain ⟨t, ht, tr⟩ := P.run a
    exact ⟨t, ht.trans (h a), tr⟩

noncomputable def congr {f f' : α → β} {T : α → ℕ} (P : Timed ea eb f T) (h : ∀ a, f a = f' a) :
    Timed ea eb f' T where
  machine := P.machine
  run a := by rw [← h a]; exact P.run a

/-- Change both the function (pointwise equal) and the time bound (pointwise larger). -/
noncomputable def cast {f f' : α → β} {T T' : α → ℕ} (P : Timed ea eb f T) (hf : ∀ a, f a = f' a)
    (hT : ∀ a, T a ≤ T' a) : Timed ea eb f' T' :=
  (P.mono hT).congr hf

/-- Re-encode the input/output (the codes must agree pointwise). -/
noncomputable def recode {α' β' : Type} {ea' : α' → List Bool} {eb' : β' → List Bool}
    {f : α → β} {f' : α' → β'} {T : α → ℕ} (P : Timed ea eb f T) (i : α' → α)
    (hi : ∀ a, ea (i a) = ea' a) (ho : ∀ a, eb (f (i a)) = eb' (f' a)) :
    Timed ea' eb' f' (fun a => T (i a)) where
  machine := P.machine
  run a := by
    obtain ⟨t, ht, tr⟩ := P.run (i a)
    rw [hi, ho] at tr
    exact ⟨t, ht, tr⟩

theorem output_length {f : α → β} {T : α → ℕ} (P : Timed ea eb f T) (a : α) :
    (eb (f a)).length ≤ (ea a).length + T a * P.machine.growth := by
  obtain ⟨t, ht, tr⟩ := P.run a
  have hv := P.machine.trace_volume tr
  simp only [Machine.initial_volume, Machine.final_volume] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _)

/-- Loops with a polynomial-time body, explicit iteration counts and sizes (from F3). -/
noncomputable def loop {body : α → β ⊕ α} (P : PolyProgram ea (encodeLoop ea eb) body) (g : α → β)
    (N S : α → ℕ) (h : ∀ a, BoundedRun ea body (S a) (N a) a (g a)) :
    Timed ea eb g (fun a => N a * P.passTime (S a)) where
  machine := Loop.machine P.machine
  run a := by
    obtain ⟨t, ht, tr⟩ := P.run_loop (h a)
    exact ⟨t, ht, tr⟩

/-! ## Basic linear-time plumbing -/

noncomputable def id' (ea : α → List Bool) : Timed ea ea (fun a => a) (fun a => 2 * (ea a).length + 3) :=
  (ofPoly (PolyProgram.identity ea)).cast (fun _ => rfl) (fun _ => (identity_time ea _).le)

noncomputable def const (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    Timed ea eb (fun _ => b) (fun a => (PolyProgram.constant ea eb b).time.eval (ea a).length) :=
  ofPoly (PolyProgram.constant ea eb b)

noncomputable def exchange (ea : α → List Bool) (eb : β → List Bool) :
    Timed (encodePair ea eb) (encodePair eb ea) Prod.swap
      (fun x => 3 * (encodePair ea eb x).length + 5) :=
  (ofPoly (PolyProgram.exchange ea eb)).mono (fun _ => (exchange_time ea eb _).le)

noncomputable def duplicate (ea : α → List Bool) :
    Timed ea (encodePair ea ea) (fun a => (a, a)) (fun a => 4 * (ea a).length + 6) :=
  (ofPoly (PolyProgram.duplicate ea)).mono (fun _ => (duplicate_time ea _).le)

noncomputable def select (eb : β → List Bool) :
    Timed (encodePair encodeBool (encodePair eb eb)) eb (fun x => if x.1 then x.2.2 else x.2.1)
      (fun x => 2 * (encodePair encodeBool (encodePair eb eb) x).length + 3) :=
  (ofPoly (PolyProgram.select eb)).mono (fun _ => (select_time eb _).le)

/-! ## Threading data past a timed computation -/

/-- Run `P` on the first component, keeping the second. -/
noncomputable def thread {f : α → β} {T : α → ℕ} (P : Timed ea eb f T) (ec : γ → List Bool) :
    Timed (encodePair ea ec) (encodePair eb ec) (fun x => (f x.1, x.2))
      (fun x => T x.1 + 2 * (ea x.1).length + 3 * (eb (f x.1)).length + 5) where
  machine := Thread.machine P.machine
  run x := by
    obtain ⟨t, ht, tr⟩ := P.run x.1
    exact ⟨2 * (ea x.1).length + 3 * (eb (f x.1)).length + 5 + t, by omega,
      Thread.run P.machine (ec x.2) tr⟩

/-- Run `P` on the second component, keeping the first. -/
noncomputable def second {f : α → β} {T : α → ℕ} (P : Timed ea eb f T) (ec : γ → List Bool) :
    Timed (encodePair ec ea) (encodePair ec eb) (fun x => (x.1, f x.2))
      (fun x => T x.2 + 13 * ((ec x.1).length + (ea x.2).length + (eb (f x.2)).length) + 29) :=
  (((exchange ec ea).comp (P.thread ec)).comp (exchange eb ec)).cast (fun _ => rfl) (fun x => by
    simp only [encodePair_length, Prod.fst_swap, Prod.snd_swap]; omega)

noncomputable def product {f : α → β} {g : γ → δ} {T1 : α → ℕ} {T2 : γ → ℕ}
    (P : Timed ea eb f T1) (Q : Timed ec ed g T2) :
    Timed (encodePair ea ec) (encodePair eb ed) (fun x => (f x.1, g x.2))
      (fun x => T1 x.1 + T2 x.2 +
        20 * ((ea x.1).length + (eb (f x.1)).length + (ec x.2).length + (ed (g x.2)).length) + 38) :=
  ((P.thread ec).comp (Q.second eb)).cast (fun _ => rfl) (fun x => by
    simp only [encodePair_length]; omega)

noncomputable def fanout {f : α → β} {h : α → γ} {T1 T2 : α → ℕ}
    (P : Timed ea eb f T1) (Q : Timed ea ec h T2) :
    Timed ea (encodePair eb ec) (fun a => (f a, h a))
      (fun a => T1 a + T2 a + 50 * ((ea a).length + (eb (f a)).length + (ec (h a)).length) + 48) :=
  ((duplicate ea).comp (P.product Q)).cast (fun _ => rfl) (fun x => by
    simp only [encodePair_length]; omega)

/-- Branching (both branches are evaluated). -/
noncomputable def ite {p : α → Bool} {f g : α → β} {Tp Tf Tg : α → ℕ}
    (P : Timed ea encodeBool p Tp) (F : Timed ea eb f Tf) (G : Timed ea eb g Tg) :
    Timed ea eb (fun a => if p a then f a else g a)
      (fun a => Tp a + Tf a + Tg a + 200 * ((ea a).length + (eb (f a)).length + (eb (g a)).length) + 250) :=
  ((P.fanout (G.fanout F)).comp (select eb)).cast (fun _ => rfl) (fun x => by
    simp only [encodePair_length, encodeBool, List.length_singleton]
    omega)

/-! ## Loops whose body is itself timed -/

section LoopT

variable {f : α → β ⊕ α} {T : α → ℕ}

theorem loop_trace (P : Timed ea (encodeLoop ea eb) f T) (I : α → Prop) (g : α → β) (R : α → ℕ)
    (hstop : ∀ a b, I a → f a = .inl b → g a = b ∧ T a + 1 ≤ R a)
    (hstep : ∀ a a', I a → f a = .inr a' → I a' ∧ g a = g a' ∧ T a + 2 * (ea a').length + 3 + R a' ≤ R a) :
    ∀ a, I a → ∃ t ≤ R a, Trace (Loop.machine P.machine).step t
      ((Loop.machine P.machine).initialCfg (ea a)) ((Loop.machine P.machine).finalCfg (eb (g a))) := by
  intro a
  induction hR : R a using Nat.strong_induction_on generalizing a with
  | _ r ih =>
  intro hI
  obtain ⟨t, ht, tr⟩ := P.run a
  rcases hfa : f a with b | a'
  · obtain ⟨hg, hT⟩ := hstop a b hI hfa
    rw [hfa] at tr
    refine ⟨t + 1, by omega, ?_⟩
    rw [hg]; exact Loop.stop P.machine tr
  · obtain ⟨hI', hg, hT⟩ := hstep a a' hI hfa
    rw [hfa] at tr
    obtain ⟨t', ht', tr'⟩ := ih (R a') (by omega) a' rfl hI'
    refine ⟨t + 2 * (ea a').length + 3 + t', by omega, ?_⟩
    rw [hg]; exact Loop.next P.machine tr tr'

/-- A loop with a timed body, specified by a "remaining time" function `R`. -/
noncomputable def loopT (P : Timed ea (encodeLoop ea eb) f T) (g : α → β) (R : α → ℕ)
    (hstop : ∀ a b, f a = .inl b → g a = b ∧ T a + 1 ≤ R a)
    (hstep : ∀ a a', f a = .inr a' → g a = g a' ∧ T a + 2 * (ea a').length + 3 + R a' ≤ R a) :
    Timed ea eb g R where
  machine := Loop.machine P.machine
  run a := by
    obtain ⟨t, ht, tr⟩ := loop_trace P (fun _ => True) g R (fun a b _ h => hstop a b h)
      (fun a a' _ h => ⟨trivial, hstep a a' h⟩) a trivial
    exact ⟨t, ht, tr⟩

/-- Initialise a state with `Q`, then run a loop with timed body `P`, whose specification only needs
to hold on states satisfying an invariant `I` (established by `Q`, preserved by steps). -/
noncomputable def loopFrom {i : γ → α} {Ti : γ → ℕ} (Q : Timed ec ea i Ti)
    (P : Timed ea (encodeLoop ea eb) f T) (I : α → Prop) (g : α → β) (R : α → ℕ)
    (hinit : ∀ x, I (i x))
    (hstop : ∀ a b, I a → f a = .inl b → g a = b ∧ T a + 1 ≤ R a)
    (hstep : ∀ a a', I a → f a = .inr a' → I a' ∧ g a = g a' ∧ T a + 2 * (ea a').length + 3 + R a' ≤ R a) :
    Timed ec eb (fun x => g (i x)) (fun x => Ti x + 2 * (ea (i x)).length + 2 + R (i x)) where
  machine := Compose.machine Q.machine (Loop.machine P.machine)
  run x := by
    obtain ⟨t1, h1, tr1⟩ := Q.run x
    obtain ⟨t2, h2, tr2⟩ := loop_trace P I g R hstop hstep (i x) (hinit x)
    exact ⟨_, by omega, Compose.run _ _ tr1 tr2⟩

/-- Counting version: `N` is a potential that decreases by at least one at each step, `B` an upper
bound for the cost of one iteration that does not increase along the run. Total time `(N a + 1) * B a`. -/
noncomputable def loopFromCount {i : γ → α} {Ti : γ → ℕ} (Q : Timed ec ea i Ti)
    (P : Timed ea (encodeLoop ea eb) f T) (I : α → Prop) (g : α → β) (N B : α → ℕ)
    (hinit : ∀ x, I (i x))
    (hstop : ∀ a b, I a → f a = .inl b → g a = b ∧ T a + 1 ≤ B a)
    (hstep : ∀ a a', I a → f a = .inr a' →
      I a' ∧ g a = g a' ∧ N a' + 1 ≤ N a ∧ B a' ≤ B a ∧ T a + 2 * (ea a').length + 3 ≤ B a) :
    Timed ec eb (fun x => g (i x)) (fun x => Ti x + 2 * (ea (i x)).length + 2 + (N (i x) + 1) * B (i x)) :=
  loopFrom Q P I g (fun a => (N a + 1) * B a) hinit
    (fun a b hI h => by
      obtain ⟨h1, h2⟩ := hstop a b hI h
      exact ⟨h1, by nlinarith⟩)
    (fun a a' hI h => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hstep a a' hI h
      refine ⟨h1, h2, ?_⟩
      have : (N a' + 1) * B a' ≤ N a * B a := Nat.mul_le_mul h3 h4
      nlinarith)

end LoopT

end Timed

end RSSDTM

end RSSDTM_Timed

section RSSDTM_Coding

/-! # The `Coding`-based layer: sums, `Timed` wrappers -/

namespace RSSDTM

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

/-- Sums are coded as loop states: `.inl b ↦ false :: enc b`, `.inr a ↦ true :: enc a`. -/
instance instCodingSum {α β : Type} [Coding α] [Coding β] : Coding (β ⊕ α) :=
  ⟨encodeLoop enc enc⟩

theorem enc_sum_inl {α β : Type} [Coding α] [Coding β] (b : β) :
    (enc (Sum.inl b : β ⊕ α)) = false :: enc b := rfl
theorem enc_sum_inr {α β : Type} [Coding α] [Coding β] (a : α) :
    (enc (Sum.inr a : β ⊕ α)) = true :: enc a := rfl

section
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem Poly.sum_inl : Poly (Sum.inl : β → β ⊕ α) := ⟨PolyProgram.injectLeft enc enc⟩
@[fun_prop] theorem Poly.sum_inr : Poly (Sum.inr : α → β ⊕ α) := ⟨PolyProgram.injectRight enc enc⟩
@[fun_prop] theorem Poly.sum_inl_comp {g : γ → β} (hg : Poly g) : Poly (fun x => (Sum.inl (g x) : β ⊕ α)) :=
  Poly.comp Poly.sum_inl hg
@[fun_prop] theorem Poly.sum_inr_comp {g : γ → α} (hg : Poly g) : Poly (fun x => (Sum.inr (g x) : β ⊕ α)) :=
  Poly.comp Poly.sum_inr hg

end

namespace Timed

variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

/-- A `Poly` function as a timed machine. -/
noncomputable def ofP {f : α → β} (h : Poly f) :
    Timed (enc : α → List Bool) (enc : β → List Bool) f (fun a => h.program.time.eval (enc a).length) :=
  ofPoly h.program

/-- Pairing of two timed computations on the same input (`Coding` version of `fanout`). -/
noncomputable def pair {f : α → β} {h : α → γ} {T1 T2 : α → ℕ}
    (P : Timed (enc : α → List Bool) (enc : β → List Bool) f T1)
    (Q : Timed (enc : α → List Bool) (enc : γ → List Bool) h T2) :
    Timed (enc : α → List Bool) (enc : β × γ → List Bool) (fun a => (f a, h a))
      (fun a => T1 a + T2 a + 50 * ((enc a).length + (enc (f a)).length + (enc (h a)).length) + 48) :=
  fanout P Q

/-- Keep the input next to the result of a timed computation. -/
noncomputable def keep {f : α → β} {T : α → ℕ}
    (P : Timed (enc : α → List Bool) (enc : β → List Bool) f T) :
    Timed (enc : α → List Bool) (enc : α × β → List Bool) (fun a => (a, f a))
      (fun a => T a + 110 * ((enc a).length + (enc (f a)).length) + 60) :=
  ((id' enc).pair P).cast (fun _ => rfl) (fun a => by omega)

/-- Post-compose with a `Poly` function. -/
noncomputable def compP {f : α → β} {g : β → γ} {T : α → ℕ}
    (P : Timed (enc : α → List Bool) (enc : β → List Bool) f T) (hg : Poly g) :
    Timed (enc : α → List Bool) (enc : γ → List Bool) (fun a => g (f a))
      (fun a => T a + 2 * (enc (f a)).length + 2 + hg.program.time.eval (enc (f a)).length) :=
  P.comp (ofP hg)

/-- Pre-compose with a `Poly` function. -/
noncomputable def pcomp {f : β → γ} {g : α → β} {T : β → ℕ} (hg : Poly g)
    (P : Timed (enc : β → List Bool) (enc : γ → List Bool) f T) :
    Timed (enc : α → List Bool) (enc : γ → List Bool) (fun a => f (g a))
      (fun a => hg.program.time.eval (enc a).length + 2 * (enc (g a)).length + 2 + T (g a)) :=
  (ofP hg).comp P

end Timed

end RSSDTM

end RSSDTM_Coding

section RSSDTM_Search

/-! # Exhaustive search below a bound -/

namespace RSSDTM

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

/-- Least `j` with `i ≤ j < N` and `test j`, or `max i N` if there is none. -/
def findFrom (test : ℕ → Bool) (N i : ℕ) : ℕ :=
  if i < N then (if test i then i else findFrom test N (i + 1)) else i
termination_by N - i

/-- Least `i < N` with `test i = true`, or `N` if there is none. -/
def findBelow (test : ℕ → Bool) (N : ℕ) : ℕ := findFrom test N 0

theorem findFrom_eq (test : ℕ → Bool) (N i : ℕ) :
    findFrom test N i = if i < N then (if test i then i else findFrom test N (i + 1)) else i := by
  rw [findFrom]

theorem findFrom_ge (test : ℕ → Bool) (N i : ℕ) : i ≤ findFrom test N i := by
  rw [findFrom_eq]; split_ifs with h1 h2
  · exact le_rfl
  · exact (Nat.le_succ i).trans (findFrom_ge test N (i + 1))
  · exact le_rfl
termination_by N - i

theorem findFrom_le (test : ℕ → Bool) (N i : ℕ) (h : i ≤ N) : findFrom test N i ≤ N := by
  rw [findFrom_eq]; split_ifs with h1 h2
  · omega
  · exact findFrom_le test N (i + 1) (by omega)
  · exact h
termination_by N - i

theorem findFrom_spec (test : ℕ → Bool) (N i : ℕ) (h : findFrom test N i < N) :
    test (findFrom test N i) = true := by
  rw [findFrom_eq] at h ⊢; split_ifs at h ⊢ with h1 h2
  · exact h2
  · exact findFrom_spec test N (i + 1) h
  · omega
termination_by N - i

theorem findFrom_min (test : ℕ → Bool) (N i j : ℕ) (hij : i ≤ j) (hj : j < findFrom test N i) :
    test j = false := by
  rw [findFrom_eq] at hj; split_ifs at hj with h1 h2
  · omega
  · rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · simpa using h2
    · exact findFrom_min test N (i + 1) j hlt hj
  · omega
termination_by N - i

theorem findBelow_le (test : ℕ → Bool) (N : ℕ) : findBelow test N ≤ N :=
  findFrom_le test N 0 (Nat.zero_le _)

theorem findBelow_spec (test : ℕ → Bool) (N : ℕ) (h : findBelow test N < N) :
    test (findBelow test N) = true := findFrom_spec test N 0 h

theorem findBelow_min (test : ℕ → Bool) (N : ℕ) (j : ℕ) (hj : j < findBelow test N) :
    test j = false := findFrom_min test N 0 j (Nat.zero_le _) hj

theorem findBelow_lt_iff (test : ℕ → Bool) (N : ℕ) :
    findBelow test N < N ↔ ∃ i < N, test i = true := by
  constructor
  · intro h; exact ⟨_, h, findBelow_spec test N h⟩
  · rintro ⟨i, hi, ht⟩
    by_contra hc
    have hle := findBelow_le test N
    have := findBelow_min test N i (by omega)
    rw [ht] at this; exact Bool.noConfusion this

theorem findBelow_eq_iff (test : ℕ → Bool) (N : ℕ) :
    findBelow test N = N ↔ ∀ i < N, test i = false := by
  have h1 := findBelow_lt_iff test N
  have h2 := findBelow_le test N
  constructor
  · intro h i hi
    by_contra hc
    have : findBelow test N < N := h1.2 ⟨i, hi, by simpa using hc⟩
    omega
  · intro h
    by_contra hc
    obtain ⟨i, hi, ht⟩ := h1.1 (by omega)
    rw [h i hi] at ht; exact Bool.noConfusion ht

theorem findBelow_eq (test : ℕ → Bool) (N : ℕ) :
    findBelow test N = ((List.range N).find? test).getD N := by
  by_cases h : ∃ i < N, test i = true
  · have hlt := (findBelow_lt_iff test N).2 h
    obtain ⟨k, hk⟩ : ∃ k, (List.range N).find? test = some k := by
      rcases hf : (List.range N).find? test with _ | k
      · rw [List.find?_eq_none] at hf
        obtain ⟨i, hi, ht⟩ := h
        exact absurd ht (by simpa using hf i (List.mem_range.2 hi))
      · exact ⟨k, rfl⟩
    rw [hk, Option.getD_some]
    rw [List.find?_range_eq_some] at hk
    obtain ⟨hk1, hk2, hk3⟩ := hk
    apply le_antisymm
    · by_contra hc
      have := findBelow_min test N k (by omega)
      rw [hk1] at this; exact Bool.noConfusion this
    · by_contra hc
      have := hk3 (findBelow test N) (by omega)
      rw [findBelow_spec test N hlt] at this; exact Bool.noConfusion this
  · push Not at h
    rw [(findBelow_eq_iff test N).2 (fun i hi => by simpa using h i hi)]
    rw [show (List.range N).find? test = none from List.find?_eq_none.2 (fun i hi => by
      simpa using h i (List.mem_range.1 hi))]
    rfl

section Timing

variable {α : Type} [Coding α]

/-- The loop body of the search: state `(x, (i, n))`. -/
def searchBody (test : α × ℕ → Bool) (s : α × (ℕ × ℕ)) : ℕ ⊕ (α × (ℕ × ℕ)) :=
  if decide (s.2.1 < s.2.2) && !test (s.1, s.2.1) then .inr (s.1, (s.2.1 + 1, s.2.2)) else .inl s.2.1

theorem searchProj_poly : Poly (fun s : α × (ℕ × ℕ) => (s.1, s.2.1)) := by fun_prop

theorem searchSel_poly : Poly (fun p : (α × (ℕ × ℕ)) × Bool =>
    if decide (p.1.2.1 < p.1.2.2) && !p.2 then
      (Sum.inr (p.1.1, (p.1.2.1 + 1, p.1.2.2)) : ℕ ⊕ (α × (ℕ × ℕ))) else Sum.inl p.1.2.1) := by
  fun_prop

/-- Overhead polynomial of one search step (depends only on `α`'s coding). -/
noncomputable def searchStepOv (α : Type) [Coding α] : Polynomial ℕ :=
  (searchProj_poly (α := α)).program.time + (searchSel_poly (α := α)).program.time.comp (C 2 * X + C 2) +
    C 108 * X + C 109

noncomputable def searchStep {test : α × ℕ → Bool} {T : α × ℕ → ℕ}
    (P : Timed (enc : α × ℕ → List Bool) (enc : Bool → List Bool) test T) :
    Timed (enc : α × (ℕ × ℕ) → List Bool) (encodeLoop (enc : α × (ℕ × ℕ) → List Bool) (enc : ℕ → List Bool))
      (searchBody test) (fun s => T (s.1, s.2.1) + (searchStepOv α).eval (enc s).length) :=
  (((Timed.id' (enc : α × (ℕ × ℕ) → List Bool)).pair
    ((Timed.ofP (searchProj_poly (α := α))).comp P)).comp (Timed.ofP (searchSel_poly (α := α)))).cast
    (fun s => rfl) (fun s => by
      obtain ⟨x, i, n⟩ := s
      simp only [searchStepOv, eval_add, eval_comp, eval_mul, eval_C, eval_X, enc_pair_mk]
      have : (enc (test (x, i))).length = 1 := rfl
      have e2 : ∀ m : ℕ, 2 * m + 1 + 1 = 2 * m + 2 := fun m => rfl
      simp only [this, e2]
      omega)

theorem searchInit_poly {N : α → ℕ} (hN : Poly N) : Poly (fun x : α => (x, ((0 : ℕ), N x))) := by
  fun_prop

/-- Overhead polynomial of `findBelowTimed` (depends only on `α`'s coding and on the program for `N`). -/
noncomputable def findOv {N : α → ℕ} (hN : Poly N) : Polynomial ℕ :=
  (searchInit_poly hN).program.time + (searchStepOv α).comp (C 3 * X + C 2) + C 20 * X + C 20

theorem enc_zero : (enc (0 : ℕ)).length = 0 := rfl

/-- Size bound for search states `(x, (i, n))` with `i ≤ n`. -/
def searchL (s : α × (ℕ × ℕ)) : ℕ := 2 * (enc s.1).length + 3 * (enc s.2.2).length + 2

/-- **Exhaustive search.** If `test` is computed within `T`, and `T (x, i) ≤ U x` for all `i ≤ N x`,
then `x ↦ findBelow (fun i => test (x, i)) (N x)` is computed within
`(N x + 1) * (U x + findOv hN |x|+|N x|)`. -/
noncomputable def findBelowTimed {test : α × ℕ → Bool} {T : α × ℕ → ℕ}
    (P : Timed (enc : α × ℕ → List Bool) (enc : Bool → List Bool) test T)
    {N : α → ℕ} (hN : Poly N) (U : α → ℕ) (hU : ∀ x i, i ≤ N x → T (x, i) ≤ U x) :
    Timed (enc : α → List Bool) (enc : ℕ → List Bool) (fun x => findBelow (fun i => test (x, i)) (N x))
      (fun x => (N x + 1) * (U x + (findOv hN).eval ((enc x).length + (enc (N x)).length))) := by
  have hsize : ∀ s : α × (ℕ × ℕ), s.2.1 ≤ s.2.2 → (enc s).length ≤ searchL s := by
    rintro ⟨x, i, n⟩ h
    dsimp only at h ⊢
    have := enc_nat_mono h
    simp only [enc_pair_mk, searchL]; omega
  refine (Timed.loopFromCount (Timed.ofP (searchInit_poly hN)) (searchStep P)
    (fun s => s.2.1 ≤ s.2.2 ∧ s.2.2 = N s.1) (fun s => findFrom (fun j => test (s.1, j)) s.2.2 s.2.1)
    (fun s => s.2.2 - s.2.1) (fun s => U s.1 + (searchStepOv α).eval (searchL s) + 2 * searchL s + 3)
    (fun x => ⟨Nat.zero_le _, rfl⟩) ?_ ?_).cast (fun x => rfl) ?_
  · rintro ⟨x, i, n⟩ b ⟨hin, hn⟩ hf
    simp only at hin hn
    subst hn
    simp only [searchBody] at hf
    split_ifs at hf with hc
    cases hf
    refine ⟨?_, ?_⟩
    · rw [findFrom_eq]
      split_ifs with h1 h2
      · rfl
      · simp [h1, h2] at hc
      · rfl
    · have h1 := hU x i hin
      have h2 := polynomial_eval_mono (searchStepOv α) (hsize (x, (i, N x)) hin)
      simp only at h1 h2 ⊢
      omega
  · rintro ⟨x, i, n⟩ s' ⟨hin, hn⟩ hf
    simp only at hin hn
    subst hn
    simp only [searchBody] at hf
    split_ifs at hf with hc
    cases hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    obtain ⟨hlt, htest⟩ := hc
    refine ⟨⟨hlt, rfl⟩, ?_, by simp only; omega, le_rfl, ?_⟩
    · simp only
      conv_lhs => rw [findFrom_eq]
      simp [hlt, htest]
    · have h1 := hU x i hin
      have h2 := polynomial_eval_mono (searchStepOv α) (hsize (x, (i, N x)) hin)
      have h3 := hsize (x, (i + 1, N x)) hlt
      have h4 : searchL (x, (i + 1, N x)) = searchL (x, (i, N x)) := rfl
      simp only at h1 h2 h3 ⊢
      omega
  · intro x
    simp only [enc_pair_mk, enc_zero, Nat.sub_zero, searchL]
    set m := (enc x).length + (enc (N x)).length with hm
    have e1 := polynomial_eval_mono (searchInit_poly hN).program.time
      (show (enc x).length ≤ m by omega)
    have e2 := polynomial_eval_mono (searchStepOv α)
      (show 2 * (enc x).length + 3 * (enc (N x)).length + 2 ≤ 3 * m + 2 by omega)
    simp only [findOv, eval_add, eval_comp, eval_mul, eval_C, eval_X]
    change _ ≤ (N x + 1) * (U x + (eval m (searchInit_poly hN).program.time + eval (3 * m + 2) (searchStepOv α) +
      20 * m + 20))
    set K := eval m (searchInit_poly hN).program.time + 4 * m + 6
    set Z := U x + eval (3 * m + 2) (searchStepOv α) + 6 * m + 7
    have hK : K ≤ (N x + 1) * K := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hZ : (N x + 1) * (U x + eval (2 * (enc x).length + 3 * (enc (N x)).length + 2) (searchStepOv α) +
        2 * (2 * (enc x).length + 3 * (enc (N x)).length + 2) + 3) ≤ (N x + 1) * Z :=
      Nat.mul_le_mul_left _ (by omega)
    have hR : (N x + 1) * Z + (N x + 1) * K ≤ (N x + 1) * (U x + (eval m (searchInit_poly hN).program.time +
        eval (3 * m + 2) (searchStepOv α) + 20 * m + 20)) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega

theorem exists_findBelowTimed {test : α × ℕ → Bool} {T : α × ℕ → ℕ}
    (P : Timed (enc : α × ℕ → List Bool) (enc : Bool → List Bool) test T)
    {N : α → ℕ} (hN : Poly N) (U : α → ℕ) (hU : ∀ x i, i ≤ N x → T (x, i) ≤ U x) :
    ∃ Pl : Polynomial ℕ, Nonempty (Timed (enc : α → List Bool) (enc : ℕ → List Bool)
      (fun x => findBelow (fun i => test (x, i)) (N x))
      (fun x => (N x + 1) * (U x + Pl.eval ((enc x).length + (enc (N x)).length)))) :=
  ⟨_, ⟨findBelowTimed P hN U hU⟩⟩

theorem natLt_poly : Poly (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by fun_prop

/-- Overhead polynomial of `existsBelowTimed`. -/
noncomputable def existsOv {N : α → ℕ} (hN : Poly N) : Polynomial ℕ :=
  findOv hN + hN.program.time + natLt_poly.program.time.comp (C 3 * X + C 1) + C 200 * X + C 60

/-- **Bounded existential search**: `x ↦ decide (∃ i < N x, test (x, i))`. -/
noncomputable def existsBelowTimed {test : α × ℕ → Bool} {T : α × ℕ → ℕ}
    (P : Timed (enc : α × ℕ → List Bool) (enc : Bool → List Bool) test T)
    {N : α → ℕ} (hN : Poly N) (U : α → ℕ) (hU : ∀ x i, i ≤ N x → T (x, i) ≤ U x) :
    Timed (enc : α → List Bool) (enc : Bool → List Bool)
      (fun x => decide (∃ i < N x, test (x, i) = true))
      (fun x => (N x + 1) * (U x + (existsOv hN).eval ((enc x).length + (enc (N x)).length))) :=
  (((findBelowTimed P hN U hU).pair (Timed.ofP hN)).compP natLt_poly).cast
    (fun x => decide_eq_decide.2 (findBelow_lt_iff _ _)) (fun x => by
      have hfb := enc_nat_mono (findBelow_le (fun i => test (x, i)) (N x))
      simp only [enc_pair_mk, existsOv, eval_add, eval_comp, eval_mul, eval_C, eval_X]
      set m := (enc x).length + (enc (N x)).length with hm
      have e1 := polynomial_eval_mono hN.program.time (show (enc x).length ≤ m by omega)
      have e2 := polynomial_eval_mono natLt_poly.program.time
        (show 2 * (enc (findBelow (fun i => test (x, i)) (N x))).length + 1 + (enc (N x)).length ≤
          3 * m + 1 by omega)
      set E := eval m hN.program.time + eval (3 * m + 1) natLt_poly.program.time + 200 * m + 60
      have hE : E ≤ (N x + 1) * E := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      have hR : (N x + 1) * (U x + eval m (findOv hN)) + (N x + 1) * E ≤
          (N x + 1) * (U x + (eval m (findOv hN) + eval m hN.program.time +
            eval (3 * m + 1) natLt_poly.program.time + 200 * m + 60)) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      omega)

theorem boolNot_poly : Poly (fun b : Bool => !b) := by fun_prop

/-- The constant cost of negating a Boolean result. -/
noncomputable def notCost : ℕ := 4 + boolNot_poly.program.time.eval 1

/-- Overhead polynomial of `allBelowTimed`. -/
noncomputable def allOv {N : α → ℕ} (hN : Poly N) : Polynomial ℕ :=
  existsOv hN + C (2 * notCost)

/-- **Bounded universal check**: `x ↦ decide (∀ i < N x, test (x, i))`. -/
noncomputable def allBelowTimed {test : α × ℕ → Bool} {T : α × ℕ → ℕ}
    (P : Timed (enc : α × ℕ → List Bool) (enc : Bool → List Bool) test T)
    {N : α → ℕ} (hN : Poly N) (U : α → ℕ) (hU : ∀ x i, i ≤ N x → T (x, i) ≤ U x) :
    Timed (enc : α → List Bool) (enc : Bool → List Bool)
      (fun x => decide (∀ i < N x, test (x, i) = true))
      (fun x => (N x + 1) * (U x + (allOv hN).eval ((enc x).length + (enc (N x)).length))) :=
  ((existsBelowTimed (test := fun y => !test y) (P.compP boolNot_poly) hN (fun x => U x + notCost)
    (fun x i hi => by
      have := hU x i hi
      simp only [notCost, enc_bool]; omega)).compP boolNot_poly).cast
    (fun x => by
      rw [Bool.eq_iff_iff]
      simp) (fun x => by
      simp only [allOv, enc_bool, eval_add, eval_C, notCost]
      set m := (enc x).length + (enc (N x)).length
      have h1 : 4 + eval 1 boolNot_poly.program.time ≤ (N x + 1) * (4 + eval 1 boolNot_poly.program.time) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      have h2 : (N x + 1) * (U x + (4 + eval 1 boolNot_poly.program.time) + eval m (existsOv hN)) +
          (N x + 1) * (4 + eval 1 boolNot_poly.program.time) ≤
          (N x + 1) * (U x + (eval m (existsOv hN) + 2 * (4 + eval 1 boolNot_poly.program.time))) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      omega)

end Timing

end RSSDTM

end RSSDTM_Search

section RSSDTM_Bridge

/-! # From machines to `HMBinPacking.OutputsWithin` -/

namespace RSSDTM

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

/-- The bundled Mathlib machine of a framework machine (identity alphabets). -/
def TMof (M : Machine) : Turing.TM2ComputableAux Bool Bool := ⟨M.tm, Equiv.refl Bool, Equiv.refl Bool⟩

theorem outputsWithin_of_trace (M : Machine) (w o : List Bool) (t T : ℕ) (ht : t ≤ T)
    (tr : Trace M.step t (M.initialCfg w) (M.finalCfg o)) :
    HMBinPacking.OutputsWithin (TMof M) w o T := by
  have hw : List.map (⇑(Equiv.refl Bool).symm) w = w := List.map_id w
  have ho : List.map (⇑(Equiv.refl Bool).symm) o = o := List.map_id o
  have tr' : Trace M.step t (M.initialCfg (List.map (⇑(Equiv.refl Bool).symm) w))
      (M.finalCfg (List.map (⇑(Equiv.refl Bool).symm) o)) := by rw [hw, ho]; exact tr
  exact ⟨⟨⟨t, tr'.iterate_eq⟩, ht⟩⟩

namespace Timed

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

/-- Any timed machine yields `OutputsWithin` on the codes. -/
theorem outputsWithin {f : α → β} {T : α → ℕ} (P : Timed ea eb f T) (a : α) :
    HMBinPacking.OutputsWithin (TMof P.machine) (ea a) (eb (f a)) (T a) := by
  obtain ⟨t, ht, tr⟩ := P.run a
  exact outputsWithin_of_trace _ _ _ t _ ht tr

theorem outputsWithin_mono {f : α → β} {T : α → ℕ} (P : Timed ea eb f T) (a : α) (T' : ℕ)
    (h : T a ≤ T') : HMBinPacking.OutputsWithin (TMof P.machine) (ea a) (eb (f a)) T' := by
  obtain ⟨t, ht, tr⟩ := P.run a
  exact outputsWithin_of_trace _ _ _ t _ (ht.trans h) tr

theorem pack_time (n : ℕ) : BooleanLists.packProgram.time.eval n = 4 * n + 5 := by
  show (BooleanLists.pack.program.time).eval n = _
  simp [Transducer.program, show BooleanLists.pack.width = 3 by decide]

theorem unpack_time (n : ℕ) : BooleanLists.unpackProgram.time.eval n = 2 * n + 3 := by
  show (BooleanLists.unpack.program.time).eval n = _
  simp [Transducer.program, show BooleanLists.unpack.width = 1 by decide]

/-- From a `Coding`-level machine on Boolean lists (each bit coded by 3 bits) to raw bit strings. -/
noncomputable def raw {f : List Bool → List Bool} {T : List Bool → ℕ}
    (P : Timed (enc : List Bool → List Bool) (enc : List Bool → List Bool) f T) :
    Timed id id f (fun w => T w + 10 * w.length + 12 * (f w).length + 12) :=
  (((ofPoly BooleanLists.packProgram).comp P).comp (ofPoly BooleanLists.unpackProgram)).cast
    (fun _ => rfl) (fun w => by
      have h1 := enc_bool_list w
      have h2 := enc_bool_list (f w)
      simp only [id, pack_time, unpack_time] at *
      change 4 * w.length + 5 + 2 * (encodeList encodeBool w).length + 2 + T w +
        2 * (encodeList encodeBool (f w)).length + 2 + (2 * (encodeList encodeBool (f w)).length + 3) ≤ _
      rw [BooleanLists.length, BooleanLists.length]
      omega)

/-- End-to-end: a `Coding`-level machine on Boolean lists gives `OutputsWithin` on raw bits. -/
theorem outputsWithin_raw {f : List Bool → List Bool} {T : List Bool → ℕ}
    (P : Timed (enc : List Bool → List Bool) (enc : List Bool → List Bool) f T) (w : List Bool) :
    HMBinPacking.OutputsWithin (TMof P.raw.machine) w (f w) (T w + 10 * w.length + 12 * (f w).length + 12) :=
  P.raw.outputsWithin w

end Timed

end RSSDTM

end RSSDTM_Bridge

section RSSDTM_Example

/-! # Sanity example: integer square-root-type search in time `(n+2)·poly(log n)` -/

namespace RSSDTM

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

theorem example_test_poly : Poly (fun p : ℕ × ℕ => decide (p.1 ≤ p.2 * p.2)) := by fun_prop

theorem example_N_poly : Poly (fun n : ℕ => n + 1) := by fun_prop

theorem size_succ_le (n : ℕ) : (n + 1).size ≤ n.size + 2 := by
  have := size_add n 1
  have h1 : (1 : ℕ).size = 1 := by decide
  omega

theorem example_sqrt_search : ∃ Q : Polynomial ℕ,
    Nonempty (Timed (enc : ℕ → List Bool) (enc : ℕ → List Bool)
      (fun n : ℕ => findBelow (fun i => decide (n ≤ i * i)) (n + 1))
      (fun n => (n + 2) * Q.eval n.size)) := by
  let Pt := example_test_poly.program.time
  have P := findBelowTimed (Timed.ofP example_test_poly) example_N_poly
    (fun n => Pt.eval (3 * (enc (n + 1)).length + 1)) (fun n i hi => by
      apply polynomial_eval_mono
      have := enc_nat_mono hi
      have := enc_nat_mono (Nat.le_add_right n 1)
      simp only [enc_pair_mk]; omega)
  refine ⟨Pt.comp (C 3 * X + C 7) + (findOv example_N_poly).comp (C 2 * X + C 2), ⟨P.cast (fun _ => rfl) ?_⟩⟩
  intro n
  simp only [enc_nat, eval_add, eval_comp, eval_mul, eval_C, eval_X]
  have hs := size_succ_le n
  have e1 := polynomial_eval_mono Pt (show 3 * (n + 1).size + 1 ≤ 3 * n.size + 7 by omega)
  have e2 := polynomial_eval_mono (findOv example_N_poly) (show n.size + (n + 1).size ≤ 2 * n.size + 2 by omega)
  exact Nat.mul_le_mul_left _ (by omega)

end RSSDTM

end RSSDTM_Example


-- ===================== TM_prims_A.lean

/-! # Polynomial-time primitives, part A: generic tools and `𝔽_p[Y]/(f)` arithmetic -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic RSSDAlg Polynomial

namespace RSSDTMP

open RSSDTM (enc_nat enc_pair enc_list_cons length_le_enc enc_mem_le size_add)

section Gen
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem size_bound_of {f : α → β} (h : Automatic.Poly f) :
    ∃ P : Polynomial ℕ, ∀ a, (enc (f a)).length ≤ P.eval (enc a).length :=
  ⟨h.program.sizeBound, fun a => h.program.length_bound a⟩

theorem peval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b :=
  polynomial_eval_mono P h

/-- folds whose step output is bounded once the state is clamped -/
theorem poly_foldl_clamp [Inhabited γ] {f : α → β → γ → β} {as : α → List γ} {b0 : α → β}
    (cl : α → β → β) (I : α → β → Prop)
    (hf : Automatic.Poly (fun y : (α × β) × γ => f y.1.1 y.1.2 y.2))
    (hcl : Automatic.Poly (fun y : α × β => cl y.1 y.2))
    (has : Automatic.Poly as) (hb0 : Automatic.Poly b0)
    (C : Polynomial ℕ) (hC : ∀ x b, (enc (cl x b)).length ≤ C.eval (enc x).length)
    (hI0 : ∀ x, I x (b0 x)) (hIf : ∀ x b a, I x b → I x (f x b a))
    (hIcl : ∀ x b, I x b → cl x b = b) :
    Automatic.Poly (fun x => (as x).foldl (f x) (b0 x)) := by
  have heq : ∀ x, (as x).foldl (f x) (b0 x) = (as x).foldl (fun b a => f x (cl x b) a) (b0 x) := by
    intro x
    suffices h : ∀ (l : List γ) b, I x b → l.foldl (f x) b = l.foldl (fun b a => f x (cl x b) a) b from
      h _ _ (hI0 x)
    intro l
    induction l with
    | nil => intros; rfl
    | cons a l ih =>
      intro b hb
      simp only [List.foldl_cons, hIcl x b hb]
      exact ih _ (hIf x b a hb)
  simp only [heq]
  have hf' : Automatic.Poly (fun y : (α × β) × γ => f y.1.1 (cl y.1.1 y.1.2) y.2) :=
    Automatic.Poly.comp hf (Automatic.Poly.pair (Automatic.Poly.pair
      (Automatic.Poly.comp Automatic.Poly.fst Automatic.Poly.fst)
      (Automatic.Poly.comp hcl Automatic.Poly.fst)) Automatic.Poly.snd)
  obtain ⟨P, hP⟩ := size_bound_of hf
  refine RSSDTM.Poly.list_foldl (f := fun x b a => f x (cl x b) a) hf' has hb0
    (P.comp (4 * X + 2 * C + 3)) ?_
  intro x b a
  have h1 := hP ((x, cl x b), a)
  have h2 := hC x b
  have h3 := peval_mono C (show (enc x).length ≤ (enc x).length + (enc a).length by omega)
  simp only [RSSDTM.enc_pair_mk] at h1
  have h4 := peval_mono P (show 2 * (2 * (enc x).length + 1 + (enc (cl x b)).length) + 1 + (enc a).length
      ≤ 4 * ((enc x).length + (enc a).length) + 2 * C.eval ((enc x).length + (enc a).length) + 3 by omega)
  simp only [eval_comp, eval_add, eval_mul, eval_X, eval_ofNat]
  omega

/-- folds with additive growth controlled by a polynomial-time term -/
theorem poly_foldl_growth [Inhabited γ] {δ : Type} [Coding δ] {f : α → β → γ → β} {as : α → List γ}
    {b0 : α → β} (t : α → γ → δ) (K : ℕ)
    (hf : Automatic.Poly (fun y : (α × β) × γ => f y.1.1 y.1.2 y.2))
    (ht : Automatic.Poly (fun y : α × γ => t y.1 y.2))
    (has : Automatic.Poly as) (hb0 : Automatic.Poly b0)
    (hg : ∀ x b a, (enc (f x b a)).length ≤ (enc b).length + K * (enc (t x a)).length + K) :
    Automatic.Poly (fun x => (as x).foldl (f x) (b0 x)) := by
  obtain ⟨P, hP⟩ := size_bound_of ht
  refine RSSDTM.Poly.list_foldl hf has hb0 (C K * P.comp (2 * X + 1) + C K) ?_
  intro x b a
  have h1 := hP (x, a)
  simp only [RSSDTM.enc_pair_mk] at h1
  have h4 := peval_mono P (show 2 * (enc x).length + 1 + (enc a).length
      ≤ 2 * ((enc x).length + (enc a).length) + 1 by omega)
  have h5 := hg x b a
  simp only [eval_comp, eval_add, eval_mul, eval_X, eval_C, eval_one, eval_ofNat]
  have : K * (enc (t x a)).length ≤ K * P.eval (2 * ((enc x).length + (enc a).length) + 1) :=
    Nat.mul_le_mul_left _ (h1.trans h4)
  omega

theorem poly_foldl_const [Inhabited γ] {f : α → β → γ → β} (l : List γ) {b0 : α → β}
    (hf : ∀ c : γ, Automatic.Poly (fun y : α × β => f y.1 y.2 c)) (hb0 : Automatic.Poly b0) :
    Automatic.Poly (fun x => l.foldl (f x) (b0 x)) := by
  induction l generalizing b0 with
  | nil => simpa using hb0
  | cons c l ih =>
    simp only [List.foldl_cons]
    exact ih (Automatic.Poly.comp (hf c) (Automatic.Poly.pair Automatic.Poly.identity hb0))

theorem poly_map_range_const [Inhabited β] {g : α → ℕ → β} (n : ℕ)
    (hg : ∀ i, Automatic.Poly (fun x => g x i)) :
    Automatic.Poly (fun x => (List.range n).map (g x)) := by
  induction n with
  | zero => simpa using Automatic.Poly.const (α := α) ([] : List β)
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    exact RSSDTM.Poly.list_append_comp ih
      (RSSDTM.Poly.list_cons_comp (hg n) (Automatic.Poly.const []))

theorem size_mul (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.2
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  rw [pow_add]
  exact Nat.mul_lt_mul'' ha hb

theorem foldl_mul_const (p c : ℕ) (l : List β) :
    l.foldl (fun a _ => a * p) c = c * p ^ l.length := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.length_cons, pow_succ]; ring

@[fun_prop] theorem Poly.pow_length [Inhabited β] {p : α → ℕ} {l : α → List β}
    (hp : Automatic.Poly p) (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => p x ^ (l x).length) := by
  have he : (fun x => p x ^ (l x).length) = (fun x => (l x).foldl (fun a _ => a * p x) 1) := by
    funext x; rw [foldl_mul_const]; simp
  rw [he]
  refine poly_foldl_growth (f := fun x a _ => a * p x) (fun x _ => p x) 1 (by fun_prop) (by fun_prop)
    hl (Automatic.Poly.const 1) ?_
  intro x b a
  simp only [enc_nat]
  have := size_mul b (p x)
  omega

end Gen

section Basic
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem dg_eq (fc : List ℕ) : dg fc = fc.tail.length := by simp [dg]

theorem padTo_eq {δ : Type} (z : δ) (d : ℕ) (l : List δ) :
    padTo z d l = (l ++ List.replicate d z).take d := by
  simp only [padTo, List.take_append, List.take_replicate]
  congr 2
  omega

theorem replicate_eq_map {δ ε : Type} (l : List ε) (z : δ) :
    List.replicate l.length z = l.map (fun _ => z) := by simp

@[fun_prop] theorem Poly.padTo_comp [Inhabited β] [Inhabited γ] {z : α → β} {L : α → List γ}
    {l : α → List β} (hz : Automatic.Poly z) (hL : Automatic.Poly L) (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => padTo (z x) (L x).length (l x)) := by
  simp only [padTo_eq, replicate_eq_map]
  fun_prop

@[fun_prop] theorem Poly.dg_comp {fc : α → List ℕ} (h : Automatic.Poly fc) :
    Automatic.Poly (fun x => dg (fc x)) := by
  simp only [dg]; fun_prop

@[fun_prop] theorem Poly.kZero_comp {fc : α → List ℕ} (h : Automatic.Poly fc) :
    Automatic.Poly (fun x => kZero (dg (fc x))) := by
  simp only [kZero, dg_eq, replicate_eq_map]; fun_prop

@[fun_prop] theorem Poly.kOne_comp {fc : α → List ℕ} (h : Automatic.Poly fc) :
    Automatic.Poly (fun x => kOne (dg (fc x))) := by
  simp only [kOne, dg_eq]; fun_prop

theorem kOfIdx_eq (p : ℕ) (fc : List ℕ) (j : ℕ) :
    kOfIdx p (dg fc) j =
      (List.range fc.tail.length).map (fun i => j / p ^ (fc.tail.take i).length % p) := by
  rw [kOfIdx, dg_eq]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.length_take, Nat.min_eq_left hi.le]

@[fun_prop] theorem Poly.kOfIdx_comp {p : α → ℕ} {fc : α → List ℕ} {j : α → ℕ}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hj : Automatic.Poly j) :
    Automatic.Poly (fun x => kOfIdx (p x) (dg (fc x)) (j x)) := by
  simp only [kOfIdx_eq]
  fun_prop

theorem kpOfIdx_eq {δ : Type} (p : ℕ) (fc : List ℕ) (len j : ℕ) (L : List δ) (h : len ≤ L.length) :
    kpOfIdx p (dg fc) len j =
      ((List.range L.length).take len).map (fun l =>
        kOfIdx p (dg fc) (j / (p ^ fc.tail.length) ^ (L.take l).length % p ^ fc.tail.length)) := by
  rw [kpOfIdx, List.take_range, Nat.min_eq_left h, dg_eq]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.length_take, Nat.min_eq_left (by omega)]

theorem Poly.kpOfIdx_var [Inhabited γ] {p : α → ℕ} {fc : α → List ℕ} {len : α → ℕ} {j : α → ℕ} {L : α → List γ}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hlen : Automatic.Poly len)
    (hj : Automatic.Poly j) (hL : Automatic.Poly L) (h : ∀ x, len x ≤ (L x).length) :
    Automatic.Poly (fun x => kpOfIdx (p x) (dg (fc x)) (len x) (j x)) := by
  have he : (fun x => kpOfIdx (p x) (dg (fc x)) (len x) (j x)) = fun x =>
      ((List.range (L x).length).take (len x)).map (fun l =>
        kOfIdx (p x) (dg (fc x)) (j x / (p x ^ (fc x).tail.length) ^ ((L x).take l).length %
          p x ^ (fc x).tail.length)) := by
    funext x; exact kpOfIdx_eq _ _ _ _ _ (h x)
  rw [he]
  fun_prop

theorem Poly.monicOfIdx_var [Inhabited γ] {p : α → ℕ} {fc : α → List ℕ} {len : α → ℕ} {j : α → ℕ} {L : α → List γ}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hlen : Automatic.Poly len)
    (hj : Automatic.Poly j) (hL : Automatic.Poly L) (h : ∀ x, len x ≤ (L x).length) :
    Automatic.Poly (fun x => monicOfIdx (p x) (dg (fc x)) (len x) (j x)) := by
  simp only [monicOfIdx]
  have := Poly.kpOfIdx_var hp hfc hlen hj hL h
  fun_prop

end Basic

section ZArith
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem zipWith_eq {δ ε ζ : Type} (f : δ → ε → ζ) (a : List δ) (b : List ε) :
    List.zipWith f a b = (a.zip b).map (fun q => f q.1 q.2) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih => cases b with
    | nil => simp
    | cons y b => simp [ih]

theorem mapIdx_eq {δ ε : Type} (f : ℕ → δ → ε) (l : List δ) (d : δ) :
    l.mapIdx f = (List.range l.length).map (fun i => f i (l.getD i d)) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem]

theorem getLastD_eq {δ : Type} (l : List δ) (d : δ) : l.getLastD d = l.getD (l.length - 1) d := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, rfl⟩
  · subst h; rfl
  · simp

theorem iterate_eq_foldl {δ ε : Type} (f : δ → δ) (l : List ε) (c : δ) :
    Nat.iterate f l.length c = l.foldl (fun b _ => f b) c := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih => simp only [List.length_cons, Function.iterate_succ_apply, List.foldl_cons, ih]

@[fun_prop] theorem Poly.kAdd_comp {p : α → ℕ} {a b : α → List ℕ} (hp : Automatic.Poly p)
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => kAdd (p x) (a x) (b x)) := by
  simp only [kAdd, zipWith_eq]; fun_prop

@[fun_prop] theorem Poly.kSub_comp {p : α → ℕ} {a b : α → List ℕ} (hp : Automatic.Poly p)
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => kSub (p x) (a x) (b x)) := by
  simp only [kSub, zipWith_eq]; fun_prop

@[fun_prop] theorem Poly.list_sum_comp {l : α → List ℕ} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => (l x).sum) := by
  simp only [List.sum_eq_foldl]
  refine poly_foldl_growth (f := fun _ b a => b + a) (fun _ a => a) 1 (by fun_prop) (by fun_prop)
    hl (Automatic.Poly.const 0) ?_
  intro x b a
  simp only [enc_nat]
  have := size_add b a
  omega

theorem zMulRaw_eq (p : ℕ) (a b : List ℕ) :
    zMulRaw p a b = (List.range (a ++ b).tail.length).map (fun k =>
      (((List.range (a ++ b).length).take (k + 1)).foldl
        (fun acc i => acc + a.getD i 0 * b.getD (k - i) 0) 0) % p) := by
  rw [zMulRaw, List.length_tail, List.length_append]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [List.take_range, Nat.min_eq_left (by omega)]

@[fun_prop] theorem Poly.zMulRaw_comp {p : α → ℕ} {a b : α → List ℕ} (hp : Automatic.Poly p)
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => zMulRaw (p x) (a x) (b x)) := by
  simp only [zMulRaw_eq]
  have hin : Automatic.Poly (fun y : α × ℕ =>
      ((List.range (a y.1 ++ b y.1).length).take (y.2 + 1)).foldl
        (fun acc i => acc + (a y.1).getD i 0 * (b y.1).getD (y.2 - i) 0) 0) := by
    refine poly_foldl_growth (f := fun (y : α × ℕ) (acc i : ℕ) => acc + (a y.1).getD i 0 * (b y.1).getD (y.2 - i) 0)
      (fun (y : α × ℕ) (i : ℕ) => (a y.1).getD i 0 * (b y.1).getD (y.2 - i) 0) 1 (by fun_prop) (by fun_prop)
      (by fun_prop) (Automatic.Poly.const 0) ?_
    intro y c i
    simp only [enc_nat]
    have := size_add c ((a y.1).getD i 0 * (b y.1).getD (y.2 - i) 0)
    omega
  have := Automatic.Poly.list_map (f := fun x k => ((List.range (a x ++ b x).length).take (k + 1)).foldl
        (fun acc i => acc + (a x).getD i 0 * (b x).getD (k - i) 0) 0 % p x)
    (as := fun x => List.range (a x ++ b x).tail.length) (by fun_prop) (by fun_prop)
  exact this

/-- `zRedStep` as a map over indices -/
def zRedStep' (p : ℕ) (fc c : List ℕ) : List ℕ :=
  (List.range c.tail.length).map (fun i =>
    if c.length - fc.length ≤ i then
      (c.getD i 0 + (p - (c.getD (c.length - 1) 0 * fc.getD (i - (c.length - fc.length)) 0) % p)) % p
    else c.getD i 0)

theorem zRedStep_eq (p : ℕ) (fc c : List ℕ) : zRedStep p fc c = zRedStep' p fc c := by
  rw [zRedStep, zRedStep', mapIdx_eq _ _ 0, getLastD_eq, List.length_dropLast, List.length_tail]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have : c.dropLast.getD i 0 = c.getD i 0 := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
    simp
  simp only [this]

theorem zMod_eq (p : ℕ) (fc c : List ℕ) :
    zMod p fc c = padTo 0 fc.tail.length ((c.drop fc.tail.length).foldl (fun b _ => zRedStep' p fc b) c) := by
  rw [zMod, dg_eq, ← List.length_drop, iterate_eq_foldl]
  simp only [zRedStep_eq]

theorem modsub_le (p u w : ℕ) : (u + (p - w)) % p ≤ max u p := by
  rcases Nat.eq_zero_or_pos p with h | h
  · subst h; simp
  · exact (Nat.mod_lt _ h).le.trans (le_max_right _ _)

theorem getD_le_of {l : List ℕ} {B : ℕ} (h : ∀ v ∈ l, v ≤ B) (i : ℕ) : l.getD i 0 ≤ B := by
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; exact Nat.zero_le _

theorem enc_le_enc_snd {δ ε : Type} [Coding δ] [Coding ε] (x : δ × ε) :
    (enc x.2).length ≤ (enc x).length := by rw [enc_pair]; omega
theorem enc_le_enc_fst {δ ε : Type} [Coding δ] [Coding ε] (x : δ × ε) :
    (enc x.1).length ≤ (enc x).length := by rw [enc_pair]; omega

theorem Poly.zMod_unc : Automatic.Poly (fun y : ℕ × List ℕ × List ℕ => zMod y.1 y.2.1 y.2.2) := by
  simp only [zMod_eq]
  have hB : Automatic.Poly (fun y : ℕ × List ℕ × List ℕ => y.1 + y.2.2.sum) := by fun_prop
  obtain ⟨PB, hPB⟩ := size_bound_of hB
  have hfold : Automatic.Poly (fun y : ℕ × List ℕ × List ℕ =>
      (y.2.2.drop y.2.1.tail.length).foldl (fun b _ => zRedStep' y.1 y.2.1 b) y.2.2) := by
    refine poly_foldl_clamp (f := fun (y : ℕ × List ℕ × List ℕ) (b : List ℕ) (_ : ℕ) => zRedStep' y.1 y.2.1 b)
      (fun (y : ℕ × List ℕ × List ℕ) (b : List ℕ) => (b.take y.2.2.length).map (fun v => min v (y.1 + y.2.2.sum)))
      (fun (y : ℕ × List ℕ × List ℕ) (b : List ℕ) => b.length ≤ y.2.2.length ∧ ∀ v ∈ b, v ≤ y.1 + y.2.2.sum)
      (by unfold zRedStep'; fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (X * (2 * PB + 1)) ?_ ?_ ?_ ?_
    · intro y b
      have h1 := RSSDTM.enc_list_nat_le ((b.take y.2.2.length).map (fun v => min v (y.1 + y.2.2.sum)))
        (y.1 + y.2.2.sum).size (by
          intro a ha
          obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
          exact Nat.size_le_size (min_le_right _ _))
      have h2 : ((b.take y.2.2.length).map (fun v => min v (y.1 + y.2.2.sum))).length ≤ (enc y).length := by
        simp only [List.length_map, List.length_take]
        have := length_le_enc y.2.2
        have := enc_le_enc_snd y.2
        have := enc_le_enc_snd y
        omega
      have h3 := hPB y
      rw [enc_nat] at h3
      simp only [eval_mul, eval_X, eval_add, eval_ofNat, eval_one]
      calc _ ≤ _ := h1
        _ ≤ (enc y).length * (2 * (y.1 + y.2.2.sum).size + 1) := Nat.mul_le_mul_right _ h2
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    · intro y
      refine ⟨le_rfl, fun v hv => ?_⟩
      have := List.le_sum_of_mem hv
      omega
    · rintro y b - ⟨hl, hv⟩
      refine ⟨by simp [zRedStep']; omega, ?_⟩
      intro v hv'
      simp only [zRedStep', List.mem_map, List.mem_range] at hv'
      obtain ⟨i, -, rfl⟩ := hv'
      have hg := getD_le_of hv i
      split_ifs
      · exact (modsub_le _ _ _).trans (max_le hg (by omega))
      · exact hg
    · rintro y b ⟨hl, hv⟩
      rw [List.take_of_length_le hl]
      conv_rhs => rw [← List.map_id b]
      apply List.map_congr_left
      intro v hv'
      exact min_eq_left (hv v hv')
  have := Poly.padTo_comp (z := fun _ : ℕ × List ℕ × List ℕ => (0 : ℕ)) (L := fun y => y.2.1.tail)
    (Automatic.Poly.const 0) (by fun_prop) hfold
  exact this

@[fun_prop] theorem Poly.zMod_comp {p : α → ℕ} {fc c : α → List ℕ} (hp : Automatic.Poly p)
    (hfc : Automatic.Poly fc) (hc : Automatic.Poly c) :
    Automatic.Poly (fun x => zMod (p x) (fc x) (c x)) :=
  Automatic.Poly.comp Poly.zMod_unc (Automatic.Poly.pair hp (Automatic.Poly.pair hfc hc))

@[fun_prop] theorem Poly.kMul_comp {p : α → ℕ} {fc a b : α → List ℕ} (hp : Automatic.Poly p)
    (hfc : Automatic.Poly fc) (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => kMul (p x) (fc x) (a x) (b x)) := by
  simp only [kMul]; fun_prop

end ZArith

section KPArith
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

abbrev KP := List (List ℕ)

@[fun_prop] theorem Poly.list_flatten_comp [Inhabited β] {l : α → List (List β)} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => (l x).flatten) :=
  Automatic.Poly.comp ⟨PolyProgram.listFlatten enc default⟩ hl

theorem kAdd_enc_le (p : ℕ) (a b : List ℕ) :
    (enc (kAdd p a b)).length ≤ (enc a).length + 3 * (enc b).length := by
  induction a generalizing b with
  | nil => simp [kAdd]
  | cons x a ih =>
    cases b with
    | nil => simp only [kAdd, List.zipWith_nil_right]; exact Nat.zero_le _
    | cons y b =>
      have h := ih b
      simp only [kAdd, List.zipWith_cons_cons] at h ⊢
      rw [enc_list_cons, enc_list_cons, enc_list_cons]
      simp only [enc_nat] at h ⊢
      have h1 := Nat.size_le_size (Nat.mod_le (x + y) p)
      have h2 := size_add x y
      omega

theorem kpMulRaw_eq (p : ℕ) (fc : List ℕ) (a b : KP) :
    kpMulRaw p fc a b = (List.range (a ++ b).tail.length).map (fun k =>
      ((List.range (a ++ b).length).take (k + 1)).foldl
        (fun acc i => kAdd p acc (kMul p fc (a.getD i (kZero (dg fc))) (b.getD (k - i) (kZero (dg fc)))))
        (kZero (dg fc))) := by
  rw [kpMulRaw, List.length_tail, List.length_append]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [List.take_range, Nat.min_eq_left (by omega)]

@[fun_prop] theorem Poly.kpMulRaw_comp {p : α → ℕ} {fc : α → List ℕ} {a b : α → KP}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc)
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => kpMulRaw (p x) (fc x) (a x) (b x)) := by
  simp only [kpMulRaw_eq]
  have hin : Automatic.Poly (fun y : α × ℕ =>
      ((List.range (a y.1 ++ b y.1).length).take (y.2 + 1)).foldl
        (fun acc i => kAdd (p y.1) acc (kMul (p y.1) (fc y.1) ((a y.1).getD i (kZero (dg (fc y.1))))
          ((b y.1).getD (y.2 - i) (kZero (dg (fc y.1)))))) (kZero (dg (fc y.1)))) := by
    refine poly_foldl_growth (f := fun (y : α × ℕ) (acc : List ℕ) (i : ℕ) =>
        kAdd (p y.1) acc (kMul (p y.1) (fc y.1) ((a y.1).getD i (kZero (dg (fc y.1))))
          ((b y.1).getD (y.2 - i) (kZero (dg (fc y.1))))))
      (fun (y : α × ℕ) (i : ℕ) => kMul (p y.1) (fc y.1) ((a y.1).getD i (kZero (dg (fc y.1))))
          ((b y.1).getD (y.2 - i) (kZero (dg (fc y.1))))) 3 (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) ?_
    intro y c i
    have := kAdd_enc_le (p y.1) c (kMul (p y.1) (fc y.1) ((a y.1).getD i (kZero (dg (fc y.1))))
          ((b y.1).getD (y.2 - i) (kZero (dg (fc y.1)))))
    omega
  have := Automatic.Poly.list_map (f := fun x k => ((List.range (a x ++ b x).length).take (k + 1)).foldl
        (fun acc i => kAdd (p x) acc (kMul (p x) (fc x) ((a x).getD i (kZero (dg (fc x))))
          ((b x).getD (k - i) (kZero (dg (fc x)))))) (kZero (dg (fc x))))
    (as := fun x => List.range (a x ++ b x).tail.length) (by fun_prop) (by fun_prop)
  exact this

/-- `kpRedStep` as a map over indices -/
def kpRedStep' (p : ℕ) (fc : List ℕ) (g c : KP) : KP :=
  (List.range c.tail.length).map (fun i =>
    if c.length - g.length ≤ i then
      kSub p (c.getD i (kZero (dg fc))) (kMul p fc (c.getD (c.length - 1) (kZero (dg fc)))
        (g.getD (i - (c.length - g.length)) (kZero (dg fc))))
    else c.getD i (kZero (dg fc)))

theorem kpRedStep_eq (p : ℕ) (fc : List ℕ) (g c : KP) : kpRedStep p fc g c = kpRedStep' p fc g c := by
  rw [kpRedStep, kpRedStep', mapIdx_eq _ _ (kZero (dg fc)), getLastD_eq, List.length_dropLast,
    List.length_tail]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have : c.dropLast.getD i (kZero (dg fc)) = c.getD i (kZero (dg fc)) := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
    simp
  simp only [this]

theorem kpMod_eq (p : ℕ) (fc : List ℕ) (g c : KP) :
    kpMod p fc g c = padTo (kZero (dg fc)) g.tail.length
      ((c.drop g.tail.length).foldl (fun b _ => kpRedStep' p fc g b) c) := by
  rw [kpMod, ← List.length_tail, ← List.length_drop, iterate_eq_foldl]
  simp only [kpRedStep_eq]

theorem flatten_length_le_enc (c : KP) : c.flatten.length ≤ (enc c).length := by
  induction c with
  | nil => simp
  | cons k c ih =>
    rw [enc_list_cons, List.flatten_cons, List.length_append]
    have := length_le_enc k
    omega

theorem getD_mem_of_lt {δ : Type} (l : List δ) (i : ℕ) (d : δ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem kSub_length_le (p : ℕ) (a b : List ℕ) : (kSub p a b).length ≤ a.length := by
  simp [kSub]

theorem kSub_le (p : ℕ) (a b : List ℕ) (B : ℕ) (hB : p ≤ B) (ha : ∀ v ∈ a, v ≤ B) :
    ∀ v ∈ kSub p a b, v ≤ B := by
  intro v hv
  rw [kSub, zipWith_eq] at hv
  obtain ⟨⟨u, w⟩, hm, rfl⟩ := List.mem_map.1 hv
  exact (modsub_le _ _ _).trans (max_le (ha u (List.of_mem_zip hm).1) hB)

theorem Poly.kpMod_unc : Automatic.Poly (fun y : ℕ × List ℕ × KP × KP => kpMod y.1 y.2.1 y.2.2.1 y.2.2.2) := by
  simp only [kpMod_eq]
  have hB : Automatic.Poly (fun y : ℕ × List ℕ × KP × KP => y.1 + y.2.2.2.flatten.sum) := by
    have : Automatic.Poly (fun y : ℕ × List ℕ × KP × KP => y.2.2.2.flatten) :=
      Automatic.Poly.comp ⟨PolyProgram.listFlatten enc default⟩ (by fun_prop)
    fun_prop
  have hL2 : Automatic.Poly (fun y : ℕ × List ℕ × KP × KP => y.2.2.2.flatten.length) := by
    have : Automatic.Poly (fun y : ℕ × List ℕ × KP × KP => y.2.2.2.flatten) :=
      Automatic.Poly.comp ⟨PolyProgram.listFlatten enc default⟩ (by fun_prop)
    fun_prop
  obtain ⟨PB, hPB⟩ := size_bound_of hB
  have hfold : Automatic.Poly (fun y : ℕ × List ℕ × KP × KP =>
      (y.2.2.2.drop y.2.2.1.tail.length).foldl (fun b _ => kpRedStep' y.1 y.2.1 y.2.2.1 b) y.2.2.2) := by
    refine poly_foldl_clamp (f := fun (y : ℕ × List ℕ × KP × KP) (b : KP) (_ : List ℕ) =>
        kpRedStep' y.1 y.2.1 y.2.2.1 b)
      (fun (y : ℕ × List ℕ × KP × KP) (b : KP) => (b.take y.2.2.2.length).map (fun k =>
        (k.take y.2.2.2.flatten.length).map (fun v => min v (y.1 + y.2.2.2.flatten.sum))))
      (fun (y : ℕ × List ℕ × KP × KP) (b : KP) => b.length ≤ y.2.2.2.length ∧
        ∀ k ∈ b, k.length ≤ y.2.2.2.flatten.length ∧ ∀ v ∈ k, v ≤ y.1 + y.2.2.2.flatten.sum)
      (by unfold kpRedStep'; fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (X * (2 * (X * (2 * PB + 1)) + 1)) ?_ ?_ ?_ ?_
    · intro y b
      have h3 := hPB y
      rw [enc_nat] at h3
      set B := y.1 + y.2.2.2.flatten.sum
      set L2 := y.2.2.2.flatten.length
      have hc1 : y.2.2.2.length ≤ (enc y).length := by
        have := length_le_enc y.2.2.2
        have := enc_le_enc_snd y.2.2
        have := enc_le_enc_snd y.2
        have := enc_le_enc_snd y
        omega
      have hc2 : L2 ≤ (enc y).length := by
        have := flatten_length_le_enc y.2.2.2
        have := enc_le_enc_snd y.2.2
        have := enc_le_enc_snd y.2
        have := enc_le_enc_snd y
        omega
      have h1 := EncodedList.length_bound enc ((b.take y.2.2.2.length).map (fun k =>
        (k.take L2).map (fun v => min v B))) (L2 * (2 * B.size + 1)) (by
          intro k hk
          obtain ⟨k', -, rfl⟩ := List.mem_map.1 hk
          refine (RSSDTM.enc_list_nat_le _ B.size ?_).trans ?_
          · intro a ha
            obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
            exact Nat.size_le_size (min_le_right _ _)
          · simp only [List.length_map, List.length_take]
            exact Nat.mul_le_mul_right _ (min_le_left _ _))
      have h2 : ((b.take y.2.2.2.length).map (fun k => (k.take L2).map (fun v => min v B))).length
          ≤ (enc y).length := by
        simp only [List.length_map, List.length_take]
        omega
      change (encodeList enc _).length ≤ _
      simp only [eval_mul, eval_X, eval_add, eval_ofNat, eval_one]
      calc _ ≤ _ := h1
        _ ≤ (enc y).length * (2 * (L2 * (2 * B.size + 1)) + 1) := Nat.mul_le_mul_right _ h2
        _ ≤ _ := by
          apply Nat.mul_le_mul_left
          have : L2 * (2 * B.size + 1) ≤ (enc y).length * (2 * eval (enc y).length PB + 1) :=
            Nat.mul_le_mul hc2 (by omega)
          omega
    · intro y
      refine ⟨le_rfl, fun k hk => ⟨?_, fun v hv => ?_⟩⟩
      · rw [List.length_flatten]
        exact List.le_sum_of_mem (List.mem_map_of_mem hk)
      · have := List.le_sum_of_mem (List.mem_flatten.2 ⟨k, hk, hv⟩)
        omega
    · rintro y b - ⟨hl, hv⟩
      refine ⟨by simp [kpRedStep']; omega, ?_⟩
      intro k hk
      simp only [kpRedStep', List.mem_map, List.mem_range] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      have hm := hv _ (getD_mem_of_lt b i (kZero (dg y.2.1)) (by simp at hi; omega))
      split_ifs
      · exact ⟨(kSub_length_le _ _ _).trans hm.1, kSub_le _ _ _ _ (by omega) hm.2⟩
      · exact hm
    · rintro y b ⟨hl, hv⟩
      rw [List.take_of_length_le hl]
      conv_rhs => rw [← List.map_id b]
      apply List.map_congr_left
      intro k hk
      rw [List.take_of_length_le (hv k hk).1]
      conv_rhs => rw [← List.map_id k]
      apply List.map_congr_left
      intro v hv'
      exact min_eq_left ((hv k hk).2 v hv')
  have := Poly.padTo_comp (z := fun y : ℕ × List ℕ × KP × KP => kZero (dg y.2.1))
    (L := fun y => y.2.2.1.tail) (by fun_prop) (by fun_prop) hfold
  exact this

@[fun_prop] theorem Poly.kpMod_comp {p : α → ℕ} {fc : α → List ℕ} {g c : α → KP}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hg : Automatic.Poly g) (hc : Automatic.Poly c) :
    Automatic.Poly (fun x => kpMod (p x) (fc x) (g x) (c x)) :=
  Automatic.Poly.comp Poly.kpMod_unc (Automatic.Poly.pair hp (Automatic.Poly.pair hfc (Automatic.Poly.pair hg hc)))

@[fun_prop] theorem Poly.fMul_comp {p : α → ℕ} {fc : α → List ℕ} {hc a b : α → KP}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hhc : Automatic.Poly hc)
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => fMul (p x) (fc x) (hc x) (a x) (b x)) := by
  simp only [fMul]; fun_prop

end KPArith

end RSSDTMP


-- ===================== TM_prims_B.lean

/-! # Polynomial-time primitives, part B: `F`-arithmetic, powers, tests -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic RSSDAlg Polynomial

namespace RSSDTMP

open RSSDTM (enc_nat enc_pair enc_list_cons length_le_enc enc_mem_le size_add)

section Red
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

/-- a reduced `K`-element: at most `d` entries, each reduced mod `p` -/
def Red (p d : ℕ) (k : List ℕ) : Prop := k.length ≤ d ∧ ∀ v ∈ k, v % p = v

theorem red_kZero (p d : ℕ) : Red p d (kZero d) := by
  refine ⟨by simp [kZero], fun v hv => ?_⟩
  simp only [kZero, List.mem_replicate] at hv
  rw [hv.2]; simp

theorem red_kAdd (p d : ℕ) (a b : List ℕ) (ha : Red p d a) : Red p d (kAdd p a b) := by
  refine ⟨?_, fun v hv => ?_⟩
  · simp only [kAdd, List.length_zipWith]; have := ha.1; omega
  · rw [kAdd, zipWith_eq] at hv
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hv
    exact Nat.mod_mod _ _

theorem red_kSub (p d : ℕ) (a b : List ℕ) (ha : Red p d a) : Red p d (kSub p a b) := by
  refine ⟨?_, fun v hv => ?_⟩
  · simp only [kSub, List.length_zipWith]; have := ha.1; omega
  · rw [kSub, zipWith_eq] at hv
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hv
    exact Nat.mod_mod _ _

theorem red_foldl_kAdd (p d : ℕ) (l : List ℕ) (g : ℕ → List ℕ) (acc : List ℕ) (h : Red p d acc) :
    Red p d (l.foldl (fun acc i => kAdd p acc (g i)) acc) := by
  induction l generalizing acc with
  | nil => exact h
  | cons i l ih => exact ih _ (red_kAdd _ _ _ _ h)

theorem red_kpMulRaw (p : ℕ) (fc : List ℕ) (a b : KP) : ∀ k ∈ kpMulRaw p fc a b, Red p (dg fc) k := by
  intro k hk
  rw [kpMulRaw] at hk
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hk
  exact red_foldl_kAdd _ _ _ _ _ (red_kZero _ _)

theorem red_kpRedStep' (p : ℕ) (fc : List ℕ) (g c : KP) (h : ∀ k ∈ c, Red p (dg fc) k) :
    ∀ k ∈ kpRedStep' p fc g c, Red p (dg fc) k := by
  intro k hk
  simp only [kpRedStep', List.mem_map, List.mem_range] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  have hm := h _ (getD_mem_of_lt c i (kZero (dg fc)) (by simp at hi; omega))
  split_ifs
  · exact red_kSub _ _ _ _ hm
  · exact hm

theorem red_padTo {δ : Type} (P : δ → Prop) (z : δ) (hz : P z) (d : ℕ) (l : List δ) (hl : ∀ k ∈ l, P k) :
    ∀ k ∈ padTo z d l, P k := by
  intro k hk
  rw [padTo_eq] at hk
  rcases List.mem_append.1 (List.mem_of_mem_take hk) with h | h
  · exact hl k h
  · rw [(List.mem_replicate.1 h).2]; exact hz

theorem length_padTo {δ : Type} (z : δ) (d : ℕ) (l : List δ) : (padTo z d l).length = d := by
  rw [padTo_eq]; simp

theorem red_kpMod (p : ℕ) (fc : List ℕ) (g c : KP) (h : ∀ k ∈ c, Red p (dg fc) k) :
    ∀ k ∈ kpMod p fc g c, Red p (dg fc) k := by
  rw [kpMod_eq]
  apply red_padTo _ _ (red_kZero _ _)
  generalize c.drop g.tail.length = l
  induction l generalizing c with
  | nil => exact h
  | cons a l ih => exact ih _ (red_kpRedStep' _ _ _ _ h)

theorem red_fMul (p : ℕ) (fc : List ℕ) (hc a b : KP) : ∀ k ∈ fMul p fc hc a b, Red p (dg fc) k :=
  red_kpMod _ _ _ _ (red_kpMulRaw _ _ _ _)

theorem length_fMul (p : ℕ) (fc : List ℕ) (hc a b : KP) : (fMul p fc hc a b).length = hc.length - 1 := by
  rw [fMul, kpMod, length_padTo]

theorem enc_red_le (p d : ℕ) (k : List ℕ) (hk : Red p d k) (hgood : ¬ (p = 0 ∧ 0 < d)) :
    (enc k).length ≤ d * (2 * p.size + 1) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · have : d = 0 := by omega
    subst this
    have : k = [] := List.eq_nil_of_length_eq_zero (by have := hk.1; omega)
    subst this; exact Nat.zero_le _
  · refine (RSSDTM.enc_list_nat_le k p.size ?_).trans (Nat.mul_le_mul_right _ hk.1)
    intro v hv
    have := hk.2 v hv
    have : v < p := by rw [← this]; exact Nat.mod_lt _ hp
    exact Nat.size_le_size this.le

theorem enc_fMul_le (p : ℕ) (fc : List ℕ) (hc a b : KP) (hgood : ¬ (p = 0 ∧ 0 < dg fc)) :
    (enc (fMul p fc hc a b)).length ≤ hc.length * (2 * (dg fc * (2 * p.size + 1)) + 1) := by
  refine (EncodedList.length_bound enc _ (dg fc * (2 * p.size + 1)) ?_).trans ?_
  · intro k hk; exact enc_red_le _ _ _ (red_fMul _ _ _ _ _ k hk) hgood
  · rw [length_fMul]; exact Nat.mul_le_mul_right _ (by omega)

end Red

section FPow
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem fOne_eq (fc : List ℕ) (hc : KP) : fOne fc hc = padTo (kZero (dg fc)) hc.tail.length [kOne (dg fc)] := by
  simp [fOne]

theorem fEmbed_eq (fc : List ℕ) (hc : KP) (c : List ℕ) :
    fEmbed fc hc c = padTo (kZero (dg fc)) hc.tail.length [c] := by
  simp [fEmbed]

theorem fZero_eq (fc : List ℕ) (hc : KP) : fZero fc hc = hc.tail.map (fun _ => kZero (dg fc)) := by
  simp [fZero]

@[fun_prop] theorem Poly.fOne_comp {fc : α → List ℕ} {hc : α → KP} (hfc : Automatic.Poly fc)
    (hhc : Automatic.Poly hc) : Automatic.Poly (fun x => fOne (fc x) (hc x)) := by
  simp only [fOne_eq]; fun_prop

@[fun_prop] theorem Poly.fEmbed_comp {fc : α → List ℕ} {hc : α → KP} {c : α → List ℕ}
    (hfc : Automatic.Poly fc) (hhc : Automatic.Poly hc) (hcc : Automatic.Poly c) :
    Automatic.Poly (fun x => fEmbed (fc x) (hc x) (c x)) := by
  simp only [fEmbed_eq]; fun_prop

@[fun_prop] theorem Poly.fZero_comp {fc : α → List ℕ} {hc : α → KP} (hfc : Automatic.Poly fc)
    (hhc : Automatic.Poly hc) : Automatic.Poly (fun x => fZero (fc x) (hc x)) := by
  simp only [fZero_eq]; fun_prop

@[fun_prop] theorem Poly.kpAdd_comp {p : α → ℕ} {a b : α → KP} (hp : Automatic.Poly p)
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => kpAdd (p x) (a x) (b x)) := by
  simp only [kpAdd, zipWith_eq]; fun_prop

@[fun_prop] theorem Poly.kpIsZero_comp {c : α → KP} (hc : Automatic.Poly c) :
    Automatic.Poly (fun x => kpIsZero (c x)) := by
  simp only [kpIsZero]; fun_prop

theorem Poly.nat_bits : Automatic.Poly (Nat.bits : ℕ → List Bool) := ⟨PolyProgram.natAsList⟩

@[fun_prop] theorem Poly.nat_bits_comp {e : α → ℕ} (he : Automatic.Poly e) :
    Automatic.Poly (fun x => Nat.bits (e x)) := Automatic.Poly.comp Poly.nat_bits he

/-- the powering step -/
def powStep (p : ℕ) (fc : List ℕ) (hc x : KP) (acc : KP) (b : Bool) : KP :=
  if b then fMul p fc hc (fMul p fc hc acc acc) x else fMul p fc hc acc acc

theorem fPow_eq (p : ℕ) (fc : List ℕ) (hc x : KP) (e : ℕ) :
    fPow p fc hc x e = (Nat.bits e).reverse.foldl (powStep p fc hc x) (fOne fc hc) := rfl

/-- `fPow` with the exponent clamped to `≤ 1` in the degenerate case `p = 0`, `deg f > 0`
(where `fPow` is genuinely not polynomial-time: no reduction happens). -/
def fPowG (p : ℕ) (fc : List ℕ) (hc x : KP) (e : ℕ) : KP :=
  fPow p fc hc x (if p = 0 ∧ 0 < dg fc then min e 1 else e)

theorem fPowG_of_good (p : ℕ) (fc : List ℕ) (hc x : KP) (e : ℕ) (h : ¬ (p = 0 ∧ 0 < dg fc)) :
    fPowG p fc hc x e = fPow p fc hc x e := by
  simp [fPowG, h]

theorem fPowG_of_pos (p : ℕ) (fc : List ℕ) (hc x : KP) (e : ℕ) (h : 0 < p) :
    fPowG p fc hc x e = fPow p fc hc x e := fPowG_of_good _ _ _ _ _ (by omega)

theorem fPowG_of_le_one (p : ℕ) (fc : List ℕ) (hc x : KP) (e : ℕ) (h : e ≤ 1) :
    fPowG p fc hc x e = fPow p fc hc x e := by
  simp only [fPowG]; split_ifs <;> simp [Nat.min_eq_left h]

abbrev PowIn := ((ℕ × List ℕ) × KP) × (KP × ℕ)

def badP (p : ℕ) (fc : List ℕ) : Bool := decide (p = 0) && decide (0 < dg fc)

theorem Poly.fPowG_unc : Automatic.Poly (fun y : PowIn => fPowG y.1.1.1 y.1.1.2 y.1.2 y.2.1 y.2.2) := by
  have he : (fun y : PowIn => fPowG y.1.1.1 y.1.1.2 y.1.2 y.2.1 y.2.2) = fun y =>
      if badP y.1.1.1 y.1.1.2 then
        (if y.2.2 = 0 then fOne y.1.1.2 y.1.2 else
          fMul y.1.1.1 y.1.1.2 y.1.2 (fMul y.1.1.1 y.1.1.2 y.1.2 (fOne y.1.1.2 y.1.2) (fOne y.1.1.2 y.1.2)) y.2.1)
      else (Nat.bits y.2.2).reverse.foldl (fun acc b => if badP y.1.1.1 y.1.1.2 then acc else
        powStep y.1.1.1 y.1.1.2 y.1.2 y.2.1 acc b) (fOne y.1.1.2 y.1.2) := by
    funext y
    obtain ⟨⟨⟨p, fc⟩, hc⟩, x, e⟩ := y
    simp only [fPowG, badP]
    by_cases hb : p = 0 ∧ 0 < dg fc
    · simp only [hb, and_self, decide_true, Bool.and_self, ↓reduceIte, fPow_eq]
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; simp
      · rw [if_neg (by omega), Nat.min_eq_right (by omega)]
        simp [powStep]
    · have : (decide (p = 0) && decide (0 < dg fc)) = false := by
        simpa using hb
      simp only [hb, ↓reduceIte, this, Bool.false_eq_true, fPow_eq]
  rw [he]
  refine Automatic.Poly.ite (by unfold badP; fun_prop) (by fun_prop) ?_
  refine RSSDTM.Poly.list_foldl (f := fun (y : PowIn) (acc : KP) (b : Bool) =>
      if badP y.1.1.1 y.1.1.2 then acc else powStep y.1.1.1 y.1.1.2 y.1.2 y.2.1 acc b)
    (by unfold badP powStep; fun_prop) (by fun_prop) (by fun_prop)
    (X * (2 * (X * (2 * X + 1)) + 1)) ?_
  intro y acc b
  split_ifs with hb
  · exact Nat.le_add_right _ _
  · have hgood : ¬ (y.1.1.1 = 0 ∧ 0 < dg y.1.1.2) := by
      intro h; apply hb; simp [badP, h.1, h.2]
    have h1 : (enc (powStep y.1.1.1 y.1.1.2 y.1.2 y.2.1 acc b)).length ≤
        y.1.2.length * (2 * (dg y.1.1.2 * (2 * y.1.1.1.size + 1)) + 1) := by
      unfold powStep; split_ifs <;> exact enc_fMul_le _ _ _ _ _ hgood
    have hy : (enc y).length = 2 * (2 * (2 * y.1.1.1.size + 1 + (enc y.1.1.2).length) + 1 +
        (enc y.1.2).length) + 1 + (enc y.2).length := by
      obtain ⟨⟨⟨p, fc⟩, hc⟩, x, e⟩ := y
      simp only [RSSDTM.enc_pair_mk, enc_nat]
    have h2 := length_le_enc y.1.2
    have h3 : dg y.1.1.2 ≤ (enc y.1.1.2).length := by
      have := length_le_enc y.1.1.2; simp only [dg]; omega
    set N := (enc y).length + (enc b).length
    have hN1 : y.1.2.length ≤ N := by omega
    have hN2 : dg y.1.1.2 ≤ N := by omega
    have hN3 : y.1.1.1.size ≤ N := by omega
    simp only [eval_mul, eval_X, eval_add, eval_ofNat, eval_one]
    calc _ ≤ _ := h1
      _ ≤ N * (2 * (N * (2 * N + 1)) + 1) := by
        apply Nat.mul_le_mul hN1
        have : dg y.1.1.2 * (2 * y.1.1.1.size + 1) ≤ N * (2 * N + 1) := Nat.mul_le_mul hN2 (by omega)
        omega
      _ ≤ _ := Nat.le_add_left _ _

@[fun_prop] theorem Poly.fPowG_comp {p : α → ℕ} {fc : α → List ℕ} {hc x : α → KP} {e : α → ℕ}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hhc : Automatic.Poly hc)
    (hx : Automatic.Poly x) (he : Automatic.Poly e) :
    Automatic.Poly (fun a => fPowG (p a) (fc a) (hc a) (x a) (e a)) :=
  Automatic.Poly.comp (g := fun a => (((p a, fc a), hc a), (x a, e a))) Poly.fPowG_unc (by fun_prop)

theorem Poly.fPow_const (e : ℕ) {p : α → ℕ} {fc : α → List ℕ} {hc x : α → KP}
    (hp : Automatic.Poly p) (hfc : Automatic.Poly fc) (hhc : Automatic.Poly hc)
    (hx : Automatic.Poly x) :
    Automatic.Poly (fun a => fPow (p a) (fc a) (hc a) (x a) e) := by
  simp only [fPow_eq]
  refine poly_foldl_const (f := fun a acc b => powStep (p a) (fc a) (hc a) (x a) acc b) _ ?_ (by fun_prop)
  intro c
  cases c <;> simp only [powStep] <;> fun_prop

end FPow

section Tests
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem Poly.pow_dg_comp {p : α → ℕ} {fc : α → List ℕ} (hp : Automatic.Poly p)
    (hfc : Automatic.Poly fc) : Automatic.Poly (fun x => p x ^ dg (fc x)) := by
  simp only [dg_eq]; exact Poly.pow_length hp (by fun_prop)

theorem list_decide_eq {δ : Type} [DecidableEq δ] (l1 l2 : List δ) :
    decide (l1 = l2) = (l1.length == l2.length && (l1.zip l2).all (fun q => decide (q.1 = q.2))) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp
  | cons a l1 ih =>
    cases l2 with
    | nil => simp
    | cons b l2 =>
      have := ih l2
      simp only [List.cons.injEq, List.length_cons, List.zip_cons_cons, List.all_cons] at this ⊢
      by_cases hab : a = b <;> simp_all

@[fun_prop] theorem Poly.listNat_deq_comp {a b : α → List ℕ} (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => decide (a x = b x)) := by
  simp only [list_decide_eq]; fun_prop

@[fun_prop] theorem Poly.kp_deq_comp {a b : α → KP} (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => decide (a x = b x)) := by
  simp only [list_decide_eq (l1 := a _)]; fun_prop

theorem subfieldTest_eq (p : ℕ) (fc : List ℕ) (hc : KP) (e : ℕ) (x : KP) :
    subfieldTest p fc hc e x = (decide (fPowG p fc hc x ((p ^ dg fc) ^ e) = x) &&
      !decide (fPowG p fc hc (fPow p fc hc x e) (p ^ dg fc) = fPow p fc hc x e)) := by
  simp only [subfieldTest, Bool.beq_eq_decide_eq]
  by_cases hb : p = 0 ∧ 0 < dg fc
  · have h0 : p ^ dg fc = 0 := by rw [hb.1]; exact zero_pow (by omega)
    rw [fPowG_of_le_one _ _ _ _ _ (by rw [h0]; exact pow_le_one₀ le_rfl zero_le_one),
      fPowG_of_le_one _ _ _ _ _ (by rw [h0]; exact zero_le_one)]
  · rw [fPowG_of_good _ _ _ _ _ hb, fPowG_of_good _ _ _ _ _ hb]

theorem strictInc_eq (l : List ℕ) : strictInc l = (l.zip l.tail).all (fun q => decide (q.1 < q.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [strictInc, ih, List.tail_cons, List.zip_cons_cons, List.all_cons]

theorem foldl_congr_mem {δ ε : Type} (l : List ε) (f g : δ → ε → δ) (b : δ)
    (h : ∀ acc t, t ∈ l → f acc t = g acc t) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h _ _ List.mem_cons_self]
    exact ih _ (fun acc t ht => h acc t (List.mem_cons_of_mem _ ht))

/-- `sparseTest` with the polynomial-time power -/
def sparseTest' (p : ℕ) (fc : List ℕ) (hc : KP) (R E : ℕ) (x : KP) (J : ℕ) : Bool :=
  if strictInc (digits E R (J / (p ^ dg fc) ^ R)) &&
      (digits (p ^ dg fc) R (J % (p ^ dg fc) ^ R)).any (fun c => !(c == 0)) then
    !(kpIsZero ((List.range R).foldl
      (fun acc t => kpAdd p acc (fMul p fc hc (fEmbed fc hc (kOfIdx p (dg fc)
          ((digits (p ^ dg fc) R (J % (p ^ dg fc) ^ R)).getD t 0)))
        (fPowG p fc hc x ((digits E R (J / (p ^ dg fc) ^ R)).getD t 0)))) (fZero fc hc)))
  else true

theorem sparseTest_eq (p : ℕ) (fc : List ℕ) (hc : KP) (R E : ℕ) (x : KP) (J : ℕ) :
    sparseTest p fc hc R E x J = sparseTest' p fc hc R E x J := by
  unfold sparseTest sparseTest'
  dsimp only
  simp only [bne]
  split_ifs with hif
  swap
  · rfl
  refine congrArg (fun z => !kpIsZero z) ?_
  apply foldl_congr_mem
  intro acc t ht
  rw [List.mem_range] at ht
  have key : fPowG p fc hc x ((digits E R (J / (p ^ dg fc) ^ R)).getD t 0) =
      fPow p fc hc x ((digits E R (J / (p ^ dg fc) ^ R)).getD t 0) := by
    by_cases hb : p = 0 ∧ 0 < dg fc
    · have h0 : p ^ dg fc = 0 := by rw [hb.1]; exact zero_pow (by omega)
      rw [fPowG_of_le_one]
      refine (getD_le_of (B := 0) ?_ t).trans zero_le_one
      intro v hv
      simp only [digits, List.mem_map, List.mem_range] at hv
      obtain ⟨i, -, rfl⟩ := hv
      rw [h0, zero_pow (by omega)]; simp
    · rw [fPowG_of_good _ _ _ _ _ hb]
  rw [key]

@[fun_prop] theorem Poly.digits_const (R : ℕ) {B j : α → ℕ} (hB : Automatic.Poly B) (hj : Automatic.Poly j) :
    Automatic.Poly (fun x => digits (B x) R (j x)) := by
  simp only [digits]
  exact poly_map_range_const R (fun i => by fun_prop)

@[fun_prop] theorem Poly.strictInc_comp {l : α → List ℕ} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => strictInc (l x)) := by
  simp only [strictInc_eq]; fun_prop

abbrev SpIn := (((ℕ × List ℕ) × KP) × ℕ) × KP

theorem Poly.sparseTest_unc (R : ℕ) :
    Automatic.Poly (fun x : SpIn × ℕ =>
      sparseTest x.1.1.1.1.1 x.1.1.1.1.2 x.1.1.1.2 R x.1.1.2 x.1.2 x.2) := by
  simp only [sparseTest_eq, sparseTest']
  refine Automatic.Poly.ite (by fun_prop) ?_ (by fun_prop)
  have : Automatic.Poly (fun x : SpIn × ℕ => (List.range R).foldl
      (fun acc t => kpAdd x.1.1.1.1.1 acc (fMul x.1.1.1.1.1 x.1.1.1.1.2 x.1.1.1.2
        (fEmbed x.1.1.1.1.2 x.1.1.1.2 (kOfIdx x.1.1.1.1.1 (dg x.1.1.1.1.2)
          ((digits (x.1.1.1.1.1 ^ dg x.1.1.1.1.2) R (x.2 % (x.1.1.1.1.1 ^ dg x.1.1.1.1.2) ^ R)).getD t 0)))
        (fPowG x.1.1.1.1.1 x.1.1.1.1.2 x.1.1.1.2 x.1.2
          ((digits x.1.1.2 R (x.2 / (x.1.1.1.1.1 ^ dg x.1.1.1.1.2) ^ R)).getD t 0))))
      (fZero x.1.1.1.1.2 x.1.1.1.2)) := by
    refine poly_foldl_const _ (fun t => ?_) (by fun_prop)
    fun_prop
  fun_prop

/-- `irredTest` with the bounded-degree candidate -/
def irredTest' (p : ℕ) (fc : List ℕ) (hc : KP) (J : ℕ) : Bool :=
  if J / (p ^ fc.tail.length) ^ hc.tail.tail.length + 1 < hc.tail.length then
    !(kpIsZero (kpMod p fc (monicOfIdx p (dg fc)
      (min (J / (p ^ fc.tail.length) ^ hc.tail.tail.length + 1) hc.tail.length)
      (J % (p ^ fc.tail.length) ^ hc.tail.tail.length % (p ^ fc.tail.length) ^
        (hc.tail.take (J / (p ^ fc.tail.length) ^ hc.tail.tail.length + 1)).length)) hc))
  else true

theorem irredTest_eq (p : ℕ) (fc : List ℕ) (hc : KP) (J : ℕ) : irredTest p fc hc J = irredTest' p fc hc J := by
  simp only [irredTest, irredTest', dg_eq, List.length_tail]
  have e1 : hc.length - 1 - 1 = hc.length - 2 := by omega
  rw [e1]
  split_ifs with h
  · rw [Nat.min_eq_left h.le, List.length_take, Nat.min_eq_left (by simp; omega)]
  · rfl

theorem Poly.irredTest_unc : Automatic.Poly (fun x : ((ℕ × List ℕ) × KP) × ℕ =>
    irredTest x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  simp only [irredTest_eq, irredTest']
  refine Automatic.Poly.ite_prop (by fun_prop) ?_ (by fun_prop)
  have := Poly.monicOfIdx_var (p := fun x : ((ℕ × List ℕ) × KP) × ℕ => x.1.1.1)
    (fc := fun x => x.1.1.2)
    (len := fun x => min (x.2 / (x.1.1.1 ^ x.1.1.2.tail.length) ^ x.1.2.tail.tail.length + 1) x.1.2.tail.length)
    (j := fun x => x.2 % (x.1.1.1 ^ x.1.1.2.tail.length) ^ x.1.2.tail.tail.length %
        (x.1.1.1 ^ x.1.1.2.tail.length) ^
        (x.1.2.tail.take (x.2 / (x.1.1.1 ^ x.1.1.2.tail.length) ^ x.1.2.tail.tail.length + 1)).length)
    (L := fun x => x.1.2.tail) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun x => by simp)
  fun_prop

end Tests

end RSSDTMP


-- ===================== TM_prims_C.lean

/-! # Polynomial-time primitives, part C: input parsing and output encoding -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic RSSDAlg Polynomial
open RSListDecodingCapacity.AllRates

namespace RSSDTMP

open RSSDTM (enc_nat enc_pair enc_list_cons length_le_enc enc_mem_le size_add enc_bool_list)

section Enc
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem Poly.nat_bits' : Automatic.Poly (Nat.bits : ℕ → List Bool) := ⟨PolyProgram.natAsList⟩

theorem encNat_eq (k : ℕ) : encNat k = (Nat.bits k).flatMap (fun b => [false, b]) ++ [true, false] := by
  simp only [encNat, encBits, Nat.digits_two_eq_bits, List.map_map]
  congr 2
  conv_rhs => rw [← List.map_id (Nat.bits k)]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

@[fun_prop] theorem Poly.encNat_comp {k : α → ℕ} (hk : Automatic.Poly k) :
    Automatic.Poly (fun x => encNat (k x)) := by
  simp only [encNat_eq]
  have := Automatic.Poly.comp Poly.nat_bits' hk
  fun_prop

theorem Poly.encList_of [Inhabited β] {f : β → List Bool} (hf : Automatic.Poly f) :
    Automatic.Poly (encList f) := by
  have : encList f = fun l : List β => encNat l.length ++ l.flatMap f := by
    funext l; rfl
  rw [this]
  have hf' : Automatic.Poly (fun y : List β × β => f y.2) := Automatic.Poly.comp hf Automatic.Poly.snd
  fun_prop

theorem Poly.encNat' : Automatic.Poly encNat := Poly.encNat_comp Automatic.Poly.identity

end Enc

section Parse
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

/-- value of a little-endian bit list -/
def bval (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map (fun b => cond b 1 0))

theorem bval_bits (k : ℕ) : bval (Nat.bits k) = k := by
  rw [bval, ← Nat.digits_two_eq_bits, Nat.ofDigits_digits]

theorem bval_cons (a : Bool) (l : List Bool) : bval (a :: l) = cond a 1 0 + 2 * bval l := by
  simp [bval, Nat.ofDigits_cons]

theorem bval_lt (l : List Bool) : bval l < 2 ^ l.length := by
  rw [bval]
  have := Nat.ofDigits_lt_base_pow_length (b := 2) (l := l.map (fun b => cond b 1 0)) (by norm_num)
    (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; cases b <;> simp)
  simpa using this

theorem bval_foldl (l : List Bool) (c : ℕ) :
    l.reverse.foldl (fun acc b => 2 * acc + cond b 1 0) c = c * 2 ^ l.length + bval l := by
  induction l generalizing c with
  | nil => simp [bval]
  | cons a l ih =>
    rw [List.reverse_cons, List.foldl_append, ih, bval_cons]
    simp only [List.foldl_cons, List.foldl_nil, List.length_cons, pow_succ]
    ring

@[fun_prop] theorem Poly.bval_comp {l : α → List Bool} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => bval (l x)) := by
  have he : (fun x => bval (l x)) = fun x => (l x).reverse.foldl (fun acc b => 2 * acc + cond b 1 0) 0 := by
    funext x; rw [bval_foldl]; simp
  rw [he]
  have hc : Automatic.Poly (fun y : (α × ℕ) × Bool => 2 * y.1.2 + cond y.2 1 0) := by
    have : (fun y : (α × ℕ) × Bool => 2 * y.1.2 + cond y.2 1 0) =
        fun y => 2 * y.1.2 + (if y.2 then 1 else 0) := by
      funext y; cases y.2 <;> rfl
    rw [this]; fun_prop
  refine poly_foldl_growth (f := fun (x : α) (acc : ℕ) (b : Bool) => 2 * acc + cond b 1 0)
    (fun x b => b) 2 hc (by fun_prop) (by fun_prop) (Automatic.Poly.const 0) ?_
  intro x acc b
  simp only [enc_nat]
  have : (2 * acc + cond b 1 0).size ≤ acc.size + 1 := by
    apply Nat.size_le.2
    have := Nat.lt_size_self acc
    rw [pow_succ]
    cases b <;> simp <;> omega
  omega

/-- pairs of consecutive bits -/
def pairsOf : List Bool → List (Bool × Bool)
  | a :: b :: w => (a, b) :: pairsOf w
  | _ => []

theorem pairsOf_eq (w : List Bool) :
    pairsOf w = ((List.range w.length).take (w.length / 2)).map
      (fun i => (w.getD (2 * i) false, w.getD (2 * i + 1) false)) := by
  rw [List.take_range, Nat.min_eq_left (Nat.div_le_self _ _)]
  induction w using pairsOf.induct with
  | case1 a b w ih =>
    rw [pairsOf, ih]
    have : (a :: b :: w).length / 2 = w.length / 2 + 1 := by simp; omega
    rw [this, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
  | case2 w h =>
    rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
    · rfl
    · simp [pairsOf]
    · exact absurd rfl (h a b w)

theorem pairsOf_flatMap (l : List Bool) (rest : List Bool) :
    pairsOf (l.flatMap (fun b => [false, b]) ++ rest) = l.map (fun b => (false, b)) ++ pairsOf rest := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.cons_append, List.nil_append, pairsOf, ih,
      List.map_cons]

def decStep (st : List Bool × List ℕ) (pr : Bool × Bool) : List Bool × List ℕ :=
  if pr.1 then ([], st.2 ++ [bval st.1]) else (st.1 ++ [pr.2], st.2)

theorem decStep_falses (l cur : List Bool) (out : List ℕ) :
    (l.map (fun b => (false, b))).foldl decStep (cur, out) = (cur ++ l, out) := by
  induction l generalizing cur with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons, decStep, Bool.false_eq_true, ↓reduceIte, ih,
      List.append_assoc, List.cons_append, List.nil_append]

theorem decode_flatMap (L : List ℕ) (out : List ℕ) (rest : List Bool) :
    (pairsOf (L.flatMap encNat ++ rest)).foldl decStep ([], out) =
      (pairsOf rest).foldl decStep ([], out ++ L) := by
  induction L generalizing out with
  | nil => simp
  | cons k L ih =>
    rw [List.flatMap_cons, encNat_eq, List.append_assoc, List.append_assoc, pairsOf_flatMap,
      List.foldl_append, decStep_falses]
    simp only [List.cons_append, List.nil_append, pairsOf, List.foldl_cons, decStep, ↓reduceIte,
      bval_bits]
    rw [ih]
    simp

def parseIn (w : List Bool) : ℕ × (List ℕ × ℕ) :=
  let L := ((pairsOf w).foldl decStep ([], [])).2
  (L.getD 0 0, ((L.drop 2).take (L.getD 1 0), L.getD (2 + L.getD 1 0) 0))

theorem parseIn_spec (p n : ℕ) (fc : List ℕ) :
    parseIn (encNat p ++ encList encNat fc ++ encNat n) = (p, (fc, n)) := by
  have hw : encNat p ++ encList encNat fc ++ encNat n =
      (p :: fc.length :: (fc ++ [n])).flatMap encNat ++ [] := by
    simp [encList, List.flatMap_append]
  rw [parseIn, hw, decode_flatMap]
  simp only [pairsOf, List.foldl_nil, List.nil_append]
  have h1 : (p :: fc.length :: (fc ++ [n])).getD 1 0 = fc.length := rfl
  rw [h1, show 2 + fc.length = fc.length + 1 + 1 by omega]
  simp

theorem decStep_size (st : List Bool × List ℕ) (pr : Bool × Bool) :
    (enc (decStep st pr)).length ≤ (enc st).length + 6 := by
  unfold decStep
  split_ifs
  · simp only [RSSDTM.enc_pair_mk, enc_bool_list, List.length_nil, RSSDTM.enc_list_append,
      enc_list_cons, enc_nat]
    have h1 : (bval st.1).size ≤ st.1.length := Nat.size_le.2 (bval_lt _)
    have h2 : (enc ([] : List ℕ)).length = 0 := rfl
    have h3 : (enc st).length = 2 * (3 * st.1.length) + 1 + (enc st.2).length := by
      rw [enc_pair, enc_bool_list]
    omega
  · simp only [RSSDTM.enc_pair_mk, enc_bool_list, List.length_append, List.length_cons,
      List.length_nil]
    have h3 : (enc st).length = 2 * (3 * st.1.length) + 1 + (enc st.2).length := by
      rw [enc_pair, enc_bool_list]
    omega

theorem Poly.parseIn_poly : Automatic.Poly parseIn := by
  have hpairs : Automatic.Poly (fun w : List Bool => pairsOf w) := by
    simp only [pairsOf_eq]; fun_prop
  have hfold : Automatic.Poly (fun w : List Bool => (pairsOf w).foldl decStep ([], [])) := by
    refine poly_foldl_growth (f := fun (_ : List Bool) st pr => decStep st pr) (fun _ pr => pr) 6
      (by unfold decStep; fun_prop) (by fun_prop) hpairs (Automatic.Poly.const _) ?_
    intro x st pr
    have := decStep_size st pr
    omega
  unfold RSSDTMP.parseIn
  have := Automatic.Poly.comp Automatic.Poly.snd hfold
  fun_prop

end Parse

end RSSDTMP


-- ===================== TM_prims_D.lean

/-! # `fPow` itself is not polynomial-time (degenerate input `p = 0`) -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic RSSDAlg Polynomial

namespace RSSDTMP

theorem poly_bound' (P : Polynomial ℕ) : ∀ x : ℕ, P.eval x ≤ P.eval 1 * (x + 1) ^ P.natDegree := by
  intro x
  rw [eval_eq_sum_range, eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ x) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos x) (by omega)))

theorem sq_le_two_pow (s : ℕ) (hs : 5 ≤ s) : s * s + s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ]; nlinarith

/-- a polynomial is eventually below `2^k` -/
theorem exists_lt_two_pow (P : Polynomial ℕ) (A : ℕ) : ∃ k, P.eval (A + k + 1) < 2 ^ k := by
  set M := P.eval 1
  set d := P.natDegree
  set s := A + d + M + 7
  refine ⟨s * (d + 1) + M, ?_⟩
  have h1 := poly_bound' P (A + (s * (d + 1) + M) + 1)
  have h2 : A + (s * (d + 1) + M) + 1 + 1 ≤ 2 ^ s := by
    have := sq_le_two_pow s (by omega)
    have : s * (d + 1) ≤ s * s := Nat.mul_le_mul_left _ (by omega)
    omega
  have h3 : (A + (s * (d + 1) + M) + 1 + 1) ^ d ≤ 2 ^ (s * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h2 _
  have h4 : M < 2 ^ M := Nat.lt_two_pow_self
  have h5 : 0 < 2 ^ (s * d) := by positivity
  calc P.eval (A + (s * (d + 1) + M) + 1) ≤ M * (A + (s * (d + 1) + M) + 1 + 1) ^ d := h1
    _ ≤ M * 2 ^ (s * d) := Nat.mul_le_mul_left _ h3
    _ < 2 ^ M * 2 ^ (s * d) := Nat.mul_lt_mul_of_pos_right h4 h5
    _ = 2 ^ (M + s * d) := by rw [pow_add]
    _ ≤ 2 ^ (s * (d + 1) + M) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem fMul_deg (a b : ℕ) : fMul 0 [0, 1] [[0], [1]] [[a]] [[b]] = [[a * b]] := by
  simp [fMul, kpMod, kpMulRaw, kMul, zMod, zMulRaw, kAdd, padTo, dg, kZero]

theorem fPow_deg_aux (l : List Bool) (c : ℕ) :
    l.reverse.foldl (powStep 0 [0, 1] [[0], [1]] [[2]]) [[2 ^ c]] = [[2 ^ (c * 2 ^ l.length + bval l)]] := by
  induction l generalizing c with
  | nil => simp [bval]
  | cons a l ih =>
    rw [List.reverse_cons, List.foldl_append, ih, bval_cons]
    cases a <;> simp only [List.foldl_cons, List.foldl_nil, powStep, fMul_deg, List.length_cons,
      Bool.false_eq_true, ↓reduceIte, cond_true, cond_false] <;> ring_nf

theorem fPow_deg (e : ℕ) : fPow 0 [0, 1] [[0], [1]] [[2]] e = [[2 ^ e]] := by
  have h1 : fOne [0, 1] [[0], [1]] = [[2 ^ 0]] := by simp [fOne, padTo, kZero, kOne, dg]
  rw [fPow_eq, h1, fPow_deg_aux, bval_bits]
  simp

/-- `fPow` is **not** polynomial-time on all inputs: with `p = 0`, `fc = [0,1]`, `hc = [[0],[1]]`,
`x = [[2]]` it computes `[[2^e]]`, whose encoding is exponentially longer than that of `e`. -/
theorem not_poly_fPow : ¬ Automatic.Poly (fun x : ((ℕ × List ℕ) × KP) × (KP × ℕ) =>
    fPow x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2) := by
  intro h
  obtain ⟨P, hP⟩ := size_bound_of h
  obtain ⟨k, hk⟩ := exists_lt_two_pow P
    (2 * (enc ((((0 : ℕ), [0, 1]), [[0], [1]]) : (ℕ × List ℕ) × KP)).length + 1 +
      (2 * (enc ([[2]] : KP)).length + 1))
  have h1 := hP ((((0 : ℕ), [0, 1]), [[0], [1]]), ([[2]], 2 ^ k))
  simp only [fPow_deg] at h1
  have h2 : (enc (2 ^ 2 ^ k : ℕ)).length ≤ (enc ([[2 ^ 2 ^ k]] : KP)).length :=
    (RSSDTM.enc_mem_le _ _ List.mem_cons_self).trans (RSSDTM.enc_mem_le _ _ List.mem_cons_self)
  rw [RSSDTM.enc_nat, Nat.size_pow] at h2
  have h3 : (enc (((((0 : ℕ), [0, 1]), [[0], [1]]), ([[2]], 2 ^ k)) : ((ℕ × List ℕ) × KP) × (KP × ℕ))).length
      = 2 * (enc ((((0 : ℕ), [0, 1]), [[0], [1]]) : (ℕ × List ℕ) × KP)).length + 1 +
      (2 * (enc ([[2]] : KP)).length + 1) + k + 1 := by
    simp only [RSSDTM.enc_pair_mk, RSSDTM.enc_nat, Nat.size_pow]; ring
  rw [h3] at h1
  omega

end RSSDTMP


-- ===================== TM_prims.lean

/-!
# Polynomial-time primitives of the construction (proofs of the interface `TM_spec.lean`)

All statements are copied from `Solutions/TM_spec.lean` (namespace `RSSDTMSpec`), except
`construct_TM` (not treated here) and `poly_fPow`, which is **false** as stated: for `p = 0`
no reduction happens and `fPow 0 [0,1] [[0],[1]] [[2]] e = [[2^e]]` has exponentially long output.
It is replaced by `poly_fPowG` (exponent clamped in the degenerate case `p = 0 ∧ 0 < dg fc`,
agreeing with `fPow` whenever `0 < p`); `subfieldTest`/`sparseTest` are proved as stated.
-/

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic RSSDAlg

namespace RSSDTMSpec

abbrev Ctx := ℕ × List ℕ                 -- (p, fc)
abbrev KP := List (List ℕ)                -- K-polynomials / F-elements

theorem poly_pow_dg : Automatic.Poly (fun c : Ctx => c.1 ^ dg c.2) := by fun_prop

theorem poly_kOfIdx : Automatic.Poly (fun x : Ctx × ℕ => kOfIdx x.1.1 (dg x.1.2) x.2) := by fun_prop

theorem poly_kpOfIdx (len : ℕ) : Automatic.Poly (fun x : Ctx × ℕ => kpOfIdx x.1.1 (dg x.1.2) len x.2) := by
  exact RSSDTMP.Poly.kpOfIdx_var (len := fun _ => len) (L := fun _ => List.replicate len (0 : ℕ))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => by simp)

theorem poly_monicOfIdx (deg : ℕ) :
    Automatic.Poly (fun x : Ctx × ℕ => monicOfIdx x.1.1 (dg x.1.2) deg x.2) := by
  exact RSSDTMP.Poly.monicOfIdx_var (len := fun _ => deg) (L := fun _ => List.replicate deg (0 : ℕ))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => by simp)

theorem poly_kMul : Automatic.Poly (fun x : Ctx × (List ℕ × List ℕ) => kMul x.1.1 x.1.2 x.2.1 x.2.2) := by
  fun_prop

theorem poly_fMul :
    Automatic.Poly (fun x : (Ctx × KP) × (KP × KP) => fMul x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2) := by
  fun_prop

/-- replacement for the (false) `poly_fPow`: the clamped power `fPowG`
(`fPowG = fPow` whenever `0 < p`, see `RSSDTMP.fPowG_of_pos`). -/
theorem poly_fPowG :
    Automatic.Poly (fun x : (Ctx × KP) × (KP × ℕ) =>
      RSSDTMP.fPowG x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2) :=
  RSSDTMP.Poly.fPowG_unc

/-- `poly_fPow` of the interface is false (degenerate input `p = 0`). -/
theorem poly_fPow_false :
    ¬ Automatic.Poly (fun x : (Ctx × KP) × (KP × ℕ) => fPow x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2) :=
  RSSDTMP.not_poly_fPow

theorem fPowG_eq_fPow (p : ℕ) (fc : List ℕ) (hc x : KP) (e : ℕ) (hp : 0 < p) :
    RSSDTMP.fPowG p fc hc x e = fPow p fc hc x e :=
  RSSDTMP.fPowG_of_pos p fc hc x e hp

theorem poly_irredTest :
    Automatic.Poly (fun x : (Ctx × KP) × ℕ => irredTest x.1.1.1 x.1.1.2 x.1.2 x.2) :=
  RSSDTMP.Poly.irredTest_unc

theorem poly_irredBound (m : ℕ) : Automatic.Poly (fun c : Ctx => irredBound c.1 c.2 m) := by
  unfold irredBound; fun_prop

theorem poly_subfieldTest (e : ℕ) :
    Automatic.Poly (fun x : (Ctx × KP) × KP => subfieldTest x.1.1.1 x.1.1.2 x.1.2 e x.2) := by
  simp only [RSSDTMP.subfieldTest_eq]
  have := RSSDTMP.Poly.fPow_const e (p := fun x : (Ctx × KP) × KP => x.1.1.1) (fc := fun x => x.1.1.2)
    (hc := fun x => x.1.2) (x := fun x => x.2) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  fun_prop

theorem poly_fOfIdx : Automatic.Poly (fun x : (Ctx × KP) × ℕ => fOfIdx x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  unfold fOfIdx
  exact RSSDTMP.Poly.kpOfIdx_var (len := fun x : (Ctx × KP) × ℕ => x.1.2.length - 1)
    (L := fun x => x.1.2.tail) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun _ => by simp)

theorem poly_sparseTest (R : ℕ) :
    Automatic.Poly (fun x : (((Ctx × KP) × ℕ) × KP) × ℕ =>
      sparseTest x.1.1.1.1.1 x.1.1.1.1.2 x.1.1.1.2 R x.1.1.2 x.1.2 x.2) :=
  RSSDTMP.Poly.sparseTest_unc R

theorem poly_sparseBound (R : ℕ) :
    Automatic.Poly (fun x : Ctx × ℕ => sparseBound x.1.1 x.1.2 R x.2) := by
  unfold sparseBound; fun_prop

theorem poly_point :
    Automatic.Poly (fun x : ((Ctx × KP) × (ℕ × (List KP × List KP))) × ℕ =>
      point x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2) := by
  unfold point; fun_prop

/-! ## Input parsing and output encoding -/

open RSListDecodingCapacity.AllRates in
/-- a polytime parser of the raw input `encNat p ++ encList encNat fc ++ encNat n` -/
theorem exists_parse : ∃ parse : List Bool → ℕ × (List ℕ × ℕ), Automatic.Poly parse ∧
    ∀ (p n : ℕ) (fc : List ℕ), parse (encNat p ++ encList encNat fc ++ encNat n) = (p, (fc, n)) :=
  ⟨RSSDTMP.parseIn, RSSDTMP.Poly.parseIn_poly, RSSDTMP.parseIn_spec⟩

open RSListDecodingCapacity.AllRates in
def outEnc (o : KP × List KP) : List Bool :=
  encList (encList encNat) o.1 ++ encList (encList (encList encNat)) o.2

theorem poly_outEnc : Automatic.Poly outEnc := by
  have hA : Automatic.Poly (RSListDecodingCapacity.AllRates.encList
      (RSListDecodingCapacity.AllRates.encList RSListDecodingCapacity.AllRates.encNat)) :=
    RSSDTMP.Poly.encList_of (RSSDTMP.Poly.encList_of RSSDTMP.Poly.encNat')
  have hB : Automatic.Poly (RSListDecodingCapacity.AllRates.encList
      (RSListDecodingCapacity.AllRates.encList
        (RSListDecodingCapacity.AllRates.encList RSListDecodingCapacity.AllRates.encNat))) :=
    RSSDTMP.Poly.encList_of hA
  exact RSSDTM.Poly.list_append_comp (Automatic.Poly.comp hA Automatic.Poly.fst)
    (Automatic.Poly.comp hB Automatic.Poly.snd)

end RSSDTMSpec


-- ===================== TM_construct_pkg.lean

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

namespace RSSDTMC

open RSSDTM

/-! ## Polynomially bounded functions -/

/-- `F` is bounded by a polynomial in the measure `μ`. -/
def PB {α : Type} (μ : α → ℕ) (F : α → ℕ) : Prop := ∃ Pol : Polynomial ℕ, ∀ x, F x ≤ Pol.eval (μ x)

section PBs
variable {α : Type} {μ : α → ℕ}

theorem PB.of_le {F G : α → ℕ} (hG : PB μ G) (h : ∀ x, F x ≤ G x) : PB μ F := by
  obtain ⟨P, hP⟩ := hG; exact ⟨P, fun x => (h x).trans (hP x)⟩

theorem PB.self : PB μ μ := ⟨X, fun x => by simp⟩

theorem PB.const (c : ℕ) : PB μ (fun _ => c) := ⟨C c, fun x => by simp⟩

theorem PB.add {F G : α → ℕ} (hF : PB μ F) (hG : PB μ G) : PB μ (fun x => F x + G x) := by
  obtain ⟨P, hP⟩ := hF; obtain ⟨Q, hQ⟩ := hG
  exact ⟨P + Q, fun x => by simp only [eval_add]; exact Nat.add_le_add (hP x) (hQ x)⟩

theorem PB.mul {F G : α → ℕ} (hF : PB μ F) (hG : PB μ G) : PB μ (fun x => F x * G x) := by
  obtain ⟨P, hP⟩ := hF; obtain ⟨Q, hQ⟩ := hG
  exact ⟨P * Q, fun x => by simp only [eval_mul]; exact Nat.mul_le_mul (hP x) (hQ x)⟩

theorem PB.pow (k : ℕ) {F : α → ℕ} (hF : PB μ F) : PB μ (fun x => F x ^ k) := by
  obtain ⟨P, hP⟩ := hF
  exact ⟨P ^ k, fun x => by simp only [eval_pow]; exact Nat.pow_le_pow_left (hP x) k⟩

theorem PB.comp (Pol : Polynomial ℕ) {F : α → ℕ} (hF : PB μ F) : PB μ (fun x => Pol.eval (F x)) := by
  obtain ⟨P, hP⟩ := hF
  exact ⟨Pol.comp P, fun x => by rw [eval_comp]; exact polynomial_eval_mono _ (hP x)⟩

theorem PB.trans {β : Type} {ν : β → ℕ} {F : β → ℕ} (g : α → β) (hF : PB ν F)
    (hν : PB μ (fun x => ν (g x))) : PB μ (fun x => F (g x)) := by
  obtain ⟨P, hP⟩ := hF; obtain ⟨Q, hQ⟩ := hν
  exact ⟨P.comp Q, fun x => (hP (g x)).trans (by rw [eval_comp]; exact polynomial_eval_mono _ (hQ x))⟩

end PBs

/-! ## Timed computability with polynomial time in a measure -/

section PTs
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

def msr (q : α → ℕ) (x : α) : ℕ := q x + (enc x).length

/-- `f` is computed by a timed machine in time polynomial in `q x + |x|`. -/
def PT (q : α → ℕ) (f : α → β) : Prop :=
  ∃ T : α → ℕ, Nonempty (Timed (enc : α → List Bool) (enc : β → List Bool) f T) ∧ PB (msr q) T

theorem PB.enc (q : α → ℕ) : PB (msr q) (fun x => (enc x).length) :=
  PB.of_le PB.self (fun x => by simp [msr])

theorem PB.q (q : α → ℕ) : PB (msr q) q :=
  PB.of_le PB.self (fun x => by simp [msr])

theorem PT.out {q : α → ℕ} {f : α → β} {T : α → ℕ}
    (P : Timed (enc : α → List Bool) (enc : β → List Bool) f T) (hT : PB (msr q) T) :
    PB (msr q) (fun x => (enc (f x)).length) :=
  PB.of_le (PB.add (PB.enc q) (PB.mul hT (PB.const P.machine.growth))) (fun x => P.output_length x)

theorem PT.of_poly (q : α → ℕ) {f : α → β} (h : Poly f) : PT q f :=
  ⟨_, ⟨Timed.ofP h⟩, PB.comp _ (PB.enc q)⟩

theorem PT.congr {q : α → ℕ} {f f' : α → β} (hf : PT q f) (h : ∀ x, f x = f' x) : PT q f' := by
  obtain ⟨T, ⟨P⟩, hT⟩ := hf
  exact ⟨T, ⟨P.congr h⟩, hT⟩

theorem PT.comp {q1 : α → ℕ} {q2 : β → ℕ} {f : α → β} {g : β → γ} (hf : PT q1 f) (hg : PT q2 g)
    (hq : PB (msr q1) (fun x => q2 (f x))) : PT q1 (fun x => g (f x)) := by
  obtain ⟨T1, ⟨P1⟩, h1⟩ := hf
  obtain ⟨T2, ⟨P2⟩, h2⟩ := hg
  have ho := PT.out P1 h1
  refine ⟨_, ⟨P1.comp P2⟩, ?_⟩
  have h3 : PB (msr q1) (fun x => T2 (f x)) := PB.trans f h2 (PB.add hq ho)
  exact PB.add (PB.add (PB.add h1 (PB.mul (PB.const 2) ho)) (PB.const 2)) h3

theorem PT.pair {q : α → ℕ} {f : α → β} {h : α → γ} (hf : PT q f) (hh : PT q h) :
    PT q (fun x => (f x, h x)) := by
  obtain ⟨T1, ⟨P1⟩, h1⟩ := hf
  obtain ⟨T2, ⟨P2⟩, h2⟩ := hh
  refine ⟨_, ⟨P1.pair P2⟩, ?_⟩
  exact PB.add (PB.add (PB.add h1 h2) (PB.mul (PB.const 50)
    (PB.add (PB.add (PB.enc q) (PT.out P1 h1)) (PT.out P2 h2)))) (PB.const 48)

theorem PT.keep {q : α → ℕ} {f : α → β} (hf : PT q f) : PT q (fun x => (x, f x)) :=
  PT.pair (PT.of_poly q (by fun_prop : Poly (fun x : α => x))) hf

theorem PT.pcomp {q1 : α → ℕ} {q2 : β → ℕ} {g : α → β} {F : β → γ} (hg : Poly g) (hF : PT q2 F)
    (hq : PB (msr q1) (fun x => q2 (g x))) : PT q1 (fun x => F (g x)) :=
  PT.comp (PT.of_poly q1 hg) hF hq

theorem PT.compP {q : α → ℕ} {f : α → β} {g : β → γ} (hf : PT q f) (hg : Poly g) :
    PT q (fun x => g (f x)) :=
  PT.comp hf (PT.of_poly (fun _ => 0) hg) (PB.const 0)

theorem PT.findBelow {q : α → ℕ} {test : α × ℕ → Bool} (ht : PT (fun y : α × ℕ => q y.1) test)
    {N : α → ℕ} (hN : Poly N) (hNb : PB (msr q) N) :
    PT q (fun x => RSSDTM.findBelow (fun i => test (x, i)) (N x)) := by
  obtain ⟨T, ⟨P⟩, Pol, hP⟩ := ht
  obtain ⟨Pn, hPn⟩ := id hNb
  refine ⟨_, ⟨findBelowTimed P hN (fun x => Pol.eval (q x + (2 * (enc x).length + 1 + Pn.eval (msr q x))))
    (fun x i hi => ?_)⟩, ?_⟩
  · refine (hP (x, i)).trans (polynomial_eval_mono _ ?_)
    have := size_le_self i; have := hPn x
    simp only [msr, enc_pair_mk, enc_nat] at *; omega
  · refine PB.mul (PB.add hNb (PB.const 1)) (PB.add ?_ ?_)
    · exact PB.comp Pol (PB.add (PB.q q) (PB.add (PB.add (PB.mul (PB.const 2) (PB.enc q)) (PB.const 1))
        (PB.comp Pn PB.self)))
    · refine PB.comp _ (PB.of_le (PB.add (PB.enc q) hNb) (fun x => ?_))
      rw [enc_nat]; have := size_le_self (N x); omega

theorem PT.allBelow {q : α → ℕ} {test : α × ℕ → Bool} (ht : PT (fun y : α × ℕ => q y.1) test)
    {N : α → ℕ} (hN : Poly N) (hNb : PB (msr q) N) :
    PT q (fun x => decide (∀ i < N x, test (x, i) = true)) := by
  obtain ⟨T, ⟨P⟩, Pol, hP⟩ := ht
  obtain ⟨Pn, hPn⟩ := id hNb
  refine ⟨_, ⟨allBelowTimed P hN (fun x => Pol.eval (q x + (2 * (enc x).length + 1 + Pn.eval (msr q x))))
    (fun x i hi => ?_)⟩, ?_⟩
  · refine (hP (x, i)).trans (polynomial_eval_mono _ ?_)
    have := size_le_self i; have := hPn x
    simp only [msr, enc_pair_mk, enc_nat] at *; omega
  · refine PB.mul (PB.add hNb (PB.const 1)) (PB.add ?_ ?_)
    · exact PB.comp Pol (PB.add (PB.q q) (PB.add (PB.add (PB.mul (PB.const 2) (PB.enc q)) (PB.const 1))
        (PB.comp Pn PB.self)))
    · refine PB.comp _ (PB.of_le (PB.add (PB.enc q) hNb) (fun x => ?_))
      rw [enc_nat]; have := size_le_self (N x); omega

theorem PT.list_map [Inhabited β] {q : α → ℕ} {F : ℕ → α → β} :
    ∀ (l : List ℕ), (∀ e ∈ l, PT q (F e)) → PT q (fun x => l.map (fun e => F e x))
  | [], _ => PT.of_poly q (Automatic.Poly.const ([] : List β))
  | e :: l, h =>
    (PT.compP (PT.pair (h e List.mem_cons_self)
      (PT.list_map l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))))
      (Poly.list_cons (α := β))).congr (fun x => rfl)

end PTs

/-! ## Building `List.replicate n false` by a counting loop -/

def repBody (a : ℕ × List Bool) : List Bool ⊕ (ℕ × List Bool) :=
  if a.1 = 0 then Sum.inl a.2 else Sum.inr (a.1 - 1, false :: a.2)

theorem repBody_poly : Poly repBody := by unfold repBody; fun_prop

theorem rep_PT : PT (fun c : ℕ => c) (fun c => List.replicate c false) := by
  have hi : Poly (fun c : ℕ => (c, ([] : List Bool))) := by fun_prop
  let L : ℕ × List Bool → ℕ := fun a => 3 * a.1 + 3 * a.2.length + 1
  have hL : ∀ a, (enc a).length ≤ L a := by
    rintro ⟨c, l⟩
    simp only [enc_pair_mk, enc_nat, enc_bool_list, L]; have := size_le_self c; omega
  have P := Timed.loopFromCount (Timed.ofP hi) (Timed.ofP repBody_poly) (fun _ => True)
     (fun a => List.replicate a.1 false ++ a.2) (fun a => a.1) (fun a => (repBody_poly.program.time).eval (L a) + 2 * L a + 4)
     (fun _ => trivial) (fun a b _ hab => ?_) (fun a a' _ hab => ?_)
  · refine ⟨_, ⟨P.congr (fun c => by simp)⟩, ?_⟩
    refine PB.add (PB.add (PB.add (PB.comp _ (PB.enc _)) (PB.mul (PB.const 2) (PB.of_le
      (PB.add (PB.mul (PB.const 3) PB.self) (PB.const 1)) (fun c => ?_)))) (PB.const 2))
      (PB.mul (PB.add (PB.of_le (PB.q (fun c : ℕ => c)) (fun c => le_rfl)) (PB.const 1)) (PB.add (PB.add (PB.comp (repBody_poly.program.time) (PB.of_le
        (PB.add (PB.mul (PB.const 3) PB.self) (PB.const 1)) (fun c => ?_)))
        (PB.mul (PB.const 2) (PB.of_le (PB.add (PB.mul (PB.const 3) PB.self) (PB.const 1)) (fun c => ?_))))
        (PB.const 4)))
    all_goals simp only [msr, enc_pair_mk, enc_nat, L, List.length_nil]
    all_goals (have := size_le_self c; have e0 : (enc ([] : List Bool)).length = 0 := rfl; omega)
  · obtain ⟨c, l⟩ := a
    simp only [repBody] at hab
    split_ifs at hab with h0
    cases hab
    obtain rfl : c = 0 := h0
    refine ⟨by simp, ?_⟩
    have := polynomial_eval_mono (repBody_poly.program.time) (hL (0, b))
    omega
  · obtain ⟨c, l⟩ := a
    simp only [repBody] at hab
    split_ifs at hab with h0
    cases hab
    change ¬ c = 0 at h0
    have h1 := polynomial_eval_mono (repBody_poly.program.time) (hL (c, l))
    have h2 := hL (c - 1, false :: l)
    simp only [L, List.length_cons] at h1 h2 ⊢
    have e : 3 * (c - 1) + 3 * (l.length + 1) + 1 = 3 * c + 3 * l.length + 1 := by omega
    refine ⟨trivial, ?_, by omega, by rw [e], by omega⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp [List.replicate_succ']

/-! ## From `PT` to `OutputsWithin` -/

theorem PT.outputs {q : List Bool → ℕ} {F : List Bool → List Bool} (h : PT q F) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (Pol : Polynomial ℕ), ∀ w,
      ∀ T' : ℕ, Pol.eval (q w + 3 * w.length) ≤ T' → HMBinPacking.OutputsWithin M w (F w) T' := by
  obtain ⟨T, ⟨P⟩, hT⟩ := h
  have ho := PT.out P hT
  obtain ⟨Pol, hPol⟩ : PB (msr q) (fun w => T w + 10 * w.length + 12 * (F w).length + 12) := by
    refine PB.add (PB.add (PB.add hT (PB.mul (PB.const 10) (PB.of_le (PB.enc q) (fun w => ?_))))
      (PB.mul (PB.const 12) (PB.of_le ho (fun w => ?_)))) (PB.const 12)
    · rw [enc_bool_list]; omega
    · rw [enc_bool_list]; omega
  refine ⟨TMof P.raw.machine, Pol, fun w T' hT' => P.raw.outputsWithin_mono w _ ?_⟩
  have := hPol w
  simp only [msr, enc_bool_list] at this
  exact this.trans hT'

/-! ## Polynomials in `Q ≥ 2` -/

theorem eval_le_pow (Pol : Polynomial ℕ) : ∃ a d : ℕ, ∀ y, Pol.eval y ≤ a * (y + 1) ^ d := by
  induction Pol using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨a1, d1, h1⟩ := hP
    obtain ⟨a2, d2, h2⟩ := hQ
    refine ⟨a1 + a2, d1 + d2, fun y => ?_⟩
    have e1 : (y + 1) ^ d1 ≤ (y + 1) ^ (d1 + d2) := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : (y + 1) ^ d2 ≤ (y + 1) ^ (d1 + d2) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [eval_add, add_mul]
    exact Nat.add_le_add ((h1 y).trans (Nat.mul_le_mul_left _ e1)) ((h2 y).trans (Nat.mul_le_mul_left _ e2))
  | monomial n x =>
    refine ⟨x, n, fun y => ?_⟩
    rw [eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) n)

theorem eval_le_Qpow (Pol : Polynomial ℕ) (c k : ℕ) : ∃ D : ℕ, ∀ Q y : ℕ, 2 ≤ Q → y ≤ c * Q ^ k →
    Pol.eval y ≤ Q ^ D := by
  obtain ⟨a, d, h⟩ := eval_le_pow Pol
  refine ⟨a + (c + k) * d, fun Q y hQ hy => (h y).trans ?_⟩
  have ha : a ≤ Q ^ a := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hQ a)
  have hc : c + 1 ≤ Q ^ c := (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hQ c)
  have hQk : 1 ≤ Q ^ k := Nat.one_le_pow _ _ (by omega)
  have hy1 : y + 1 ≤ Q ^ (c + k) := by
    rw [pow_add]
    have : y + 1 ≤ (c + 1) * Q ^ k := by nlinarith
    exact this.trans (Nat.mul_le_mul_right _ hc)
  rw [pow_add, pow_mul]
  exact Nat.mul_le_mul ha (Nat.pow_le_pow_left hy1 d)

/-! ## The stages of the construction -/

section Stages
open RSSDAlg RSSDTMSpec

def qC (c : Ctx) : ℕ := c.1 ^ dg c.2

/-! ### The field polynomial `h` -/

def irrM (m : ℕ) (z : Ctx × KP) : Bool :=
  decide (∀ i < irredBound z.1.1 z.1.2 m, irredTest z.1.1 z.1.2 z.2 i = true)

theorem irrM_PT (m : ℕ) : PT (fun z : Ctx × KP => qC z.1) (irrM m) :=
  (PT.allBelow (q := fun z : Ctx × KP => qC z.1)
    (test := fun x : (Ctx × KP) × ℕ => irredTest x.1.1.1 x.1.1.2 x.1.2 x.2)
    (PT.of_poly _ poly_irredTest) (N := fun z => irredBound z.1.1 z.1.2 m)
    (by have h := Automatic.Poly.comp (poly_irredBound m) (Automatic.Poly.fst (α := Ctx) (β := KP))
        exact h)
    (PB.of_le (PB.mul (PB.const (m - 1)) (PB.pow (m - 1) (PB.q _))) (fun z => le_of_eq rfl))).congr
    (fun _ => rfl)

def hTest (m : ℕ) (y : Ctx × ℕ) : Bool := irrM m (y.1, monicOfIdx y.1.1 (dg y.1.2) m y.2)

theorem hTest_PT (m : ℕ) : PT (fun y : Ctx × ℕ => qC y.1) (hTest m) :=
  PT.pcomp (g := fun y : Ctx × ℕ => (y.1, monicOfIdx y.1.1 (dg y.1.2) m y.2))
    (Automatic.Poly.pair Automatic.Poly.fst (poly_monicOfIdx m)) (irrM_PT m)
    (PB.of_le (PB.q _) (fun _ => le_rfl))

def hS (m : ℕ) (c : Ctx) : KP :=
  monicOfIdx c.1 (dg c.2) m (RSSDTM.findBelow (fun j => hTest m (c, j)) ((c.1 ^ dg c.2) ^ m))

theorem hS_PT (m : ℕ) : PT qC (hS m) :=
  (PT.compP (PT.keep (PT.findBelow (q := qC) (hTest_PT m) (N := fun c : Ctx => (c.1 ^ dg c.2) ^ m)
      (RSSDTM.Poly.nat_pow_const m poly_pow_dg) (PB.pow m (PB.q _)))) (poly_monicOfIdx m)).congr
    (fun _ => rfl)

/-! ### The `γ`'s -/

def gTest (e : ℕ) (y : (Ctx × KP) × ℕ) : Bool :=
  subfieldTest y.1.1.1 y.1.1.2 y.1.2 e (fOfIdx y.1.1.1 y.1.1.2 y.1.2 y.2)

theorem gTest_poly (e : ℕ) : Poly (gTest e) := by
  have h := Automatic.Poly.comp (poly_subfieldTest e)
    (Automatic.Poly.pair (Automatic.Poly.fst (α := Ctx × KP) (β := ℕ)) poly_fOfIdx)
  exact h

def gam (m e : ℕ) (z : Ctx × KP) : KP :=
  fOfIdx z.1.1 z.1.2 z.2 (RSSDTM.findBelow (fun j => gTest e (z, j)) ((z.1.1 ^ dg z.1.2) ^ m))

theorem gam_PT (m e : ℕ) : PT (fun z : Ctx × KP => qC z.1) (gam m e) :=
  (PT.compP (PT.keep (PT.findBelow (q := fun z : Ctx × KP => qC z.1) (PT.of_poly _ (gTest_poly e))
      (N := fun z : Ctx × KP => (z.1.1 ^ dg z.1.2) ^ m)
      (RSSDTM.Poly.nat_pow_const m (Automatic.Poly.comp poly_pow_dg Automatic.Poly.fst))
      (PB.pow m (PB.q _)))) poly_fOfIdx).congr (fun _ => rfl)

/-! ### The `δ`'s -/

def qD (w : (Ctx × KP) × ℕ) : ℕ := qC w.1.1 + w.2

def spM (R : ℕ) (w : ((Ctx × KP) × ℕ) × KP) : Bool :=
  decide (∀ J < sparseBound w.1.1.1.1 w.1.1.1.2 R w.1.2,
    sparseTest w.1.1.1.1 w.1.1.1.2 w.1.1.2 R w.1.2 w.2 J = true)

theorem spM_PT (R : ℕ) : PT (fun w : ((Ctx × KP) × ℕ) × KP => qD w.1) (spM R) :=
  (PT.allBelow (q := fun w : ((Ctx × KP) × ℕ) × KP => qD w.1)
    (test := fun x : (((Ctx × KP) × ℕ) × KP) × ℕ =>
      sparseTest x.1.1.1.1.1 x.1.1.1.1.2 x.1.1.1.2 R x.1.1.2 x.1.2 x.2)
    (PT.of_poly _ (poly_sparseTest R)) (N := fun w => sparseBound w.1.1.1.1 w.1.1.1.2 R w.1.2)
    (Automatic.Poly.comp (poly_sparseBound R)
      (by fun_prop : Poly (fun w : ((Ctx × KP) × ℕ) × KP => (w.1.1.1, w.1.2))))
    (PB.of_le (PB.mul (PB.pow R (PB.q _)) (PB.pow R (PB.q _))) (fun w => by
      unfold sparseBound
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by simp only [qD]; omega) R)
        (Nat.pow_le_pow_left (by simp only [qD, qC]; omega) R)))).congr (fun _ => rfl)

def dIdx (y : ((Ctx × KP) × ℕ) × ℕ) : KP := fOfIdx y.1.1.1.1 y.1.1.1.2 y.1.1.2 y.2

theorem dIdx_poly : Poly dIdx := by
  have h := Automatic.Poly.comp poly_fOfIdx
    (by fun_prop : Poly (fun y : ((Ctx × KP) × ℕ) × ℕ => (y.1.1, y.2)))
  exact h

def dTest (R e : ℕ) (y : ((Ctx × KP) × ℕ) × ℕ) : Bool :=
  subfieldTest y.1.1.1.1 y.1.1.1.2 y.1.1.2 e (dIdx y) && spM R (y.1, dIdx y)

theorem dTest_PT (R e : ℕ) : PT (fun y : ((Ctx × KP) × ℕ) × ℕ => qD y.1) (dTest R e) := by
  have hA : Poly (fun y : ((Ctx × KP) × ℕ) × ℕ => subfieldTest y.1.1.1.1 y.1.1.1.2 y.1.1.2 e (dIdx y)) :=
    Automatic.Poly.comp (poly_subfieldTest e) (Automatic.Poly.pair
      (by fun_prop : Poly (fun y : ((Ctx × KP) × ℕ) × ℕ => y.1.1)) dIdx_poly)
  have hB : Poly (fun y : ((Ctx × KP) × ℕ) × ℕ => (y.1, dIdx y)) :=
    Automatic.Poly.pair Automatic.Poly.fst dIdx_poly
  exact (PT.compP (PT.pair (PT.of_poly _ hA) (PT.pcomp hB (spM_PT R) (PB.of_le (PB.q _) (fun _ => le_rfl))))
    Automatic.Poly.bool_and).congr (fun _ => rfl)

def del (R e m : ℕ) (z : (Ctx × KP) × ℕ) : KP :=
  fOfIdx z.1.1.1 z.1.1.2 z.1.2 (RSSDTM.findBelow (fun j => dTest R e (z, j)) ((z.1.1.1 ^ dg z.1.1.2) ^ m))

theorem del_PT (R e m : ℕ) : PT qD (del R e m) :=
  (PT.compP (PT.keep (PT.findBelow (q := qD) (dTest_PT R e)
      (N := fun z : (Ctx × KP) × ℕ => (z.1.1.1 ^ dg z.1.1.2) ^ m)
      (RSSDTM.Poly.nat_pow_const m (Automatic.Poly.comp poly_pow_dg
        (by fun_prop : Poly (fun z : (Ctx × KP) × ℕ => z.1.1))))
      (PB.of_le (PB.pow m (PB.q _)) (fun z => Nat.pow_le_pow_left (by simp only [qD, qC]; omega) m))))
      dIdx_poly).congr (fun _ => rfl)

end Stages

/-! ## The pipeline -/

section Pipeline
open RSSDAlg RSSDTMSpec RSListDecodingCapacity.AllRates

abbrev S := ℕ × (List ℕ × ℕ)

def qS (s : S) : ℕ := s.1 ^ dg s.2.1 + s.2.2

variable (P : Params)

def st1 (s : S) : S × KP := (s, hS P.m (s.1, s.2.1))

theorem st1_PT : PT qS (st1 P) :=
  PT.keep (PT.pcomp (g := fun s : S => (s.1, s.2.1)) (by fun_prop) (hS_PT P.m)
    (PB.of_le (PB.q _) (fun s => by simp only [qS, qC]; omega)))

def st2 (x : S × KP) : (S × KP) × List KP :=
  (x, P.Ps.map (fun e => gam P.m e ((x.1.1, x.1.2.1), x.2)))

theorem st2_PT : PT (fun x : S × KP => qS x.1) (st2 P) :=
  PT.keep (PT.pcomp (g := fun x : S × KP => ((x.1.1, x.1.2.1), x.2)) (by fun_prop)
    (PT.list_map P.Ps (fun e _ => gam_PT P.m e))
    (PB.of_le (PB.q _) (fun x => by simp only [qS, qC]; omega)))

def st3 (x : (S × KP) × List KP) : ((S × KP) × List KP) × List KP :=
  (x, P.Qs.map (fun e => del (2 ^ P.r) e P.m (((x.1.1.1, x.1.1.2.1), x.1.2), x.1.1.2.2 * P.r)))

theorem st3_PT : PT (fun x : (S × KP) × List KP => qS x.1.1) (st3 P) :=
  PT.keep (PT.pcomp
    (g := fun x : (S × KP) × List KP => (((x.1.1.1, x.1.1.2.1), x.1.2), x.1.1.2.2 * P.r))
    (by fun_prop) (PT.list_map P.Qs (fun e _ => del_PT (2 ^ P.r) e P.m))
    (PB.of_le (PB.mul (PB.const (P.r + 1)) (PB.q _)) (fun x => by
      simp only [qD, qS, qC]
      nlinarith [Nat.zero_le (P.r * x.1.1.1 ^ dg x.1.1.2.1), Nat.zero_le x.1.1.2.2])))

def st4 (x : ((S × KP) × List KP) × List KP) : (((S × KP) × List KP) × List KP) × List Bool :=
  (x, List.replicate x.1.1.1.2.2 false)

theorem st4_PT : PT (fun x : ((S × KP) × List KP) × List KP => qS x.1.1.1) st4 :=
  PT.keep (PT.pcomp (g := fun x : ((S × KP) × List KP) × List KP => x.1.1.1.2.2) (by fun_prop) rep_PT
    (PB.of_le (PB.q _) (fun x => by simp only [qS]; omega)))

def fin (y : (((S × KP) × List KP) × List KP) × List Bool) : List Bool :=
  outEnc (y.1.1.1.2, (List.range y.2.length).map (fun k => point y.1.1.1.1.1 y.1.1.1.1.2.1 y.1.1.1.2
    ((y.1.1.1.1.2.2 + P.g - 1) / P.g) y.1.1.2 y.1.2 k))

theorem fin_poly : Poly (fin P) := by
  have hpt : Poly (fun z : ((((S × KP) × List KP) × List KP) × List Bool) × ℕ =>
      point z.1.1.1.1.1.1 z.1.1.1.1.1.2.1 z.1.1.1.1.2
        ((z.1.1.1.1.1.2.2 + P.g - 1) / P.g) z.1.1.1.2 z.1.1.2 z.2) := by
    have h := Automatic.Poly.comp poly_point
      (by fun_prop : Poly (fun z : ((((S × KP) × List KP) × List KP) × List Bool) × ℕ =>
        ((((z.1.1.1.1.1.1, z.1.1.1.1.1.2.1), z.1.1.1.1.2),
          ((z.1.1.1.1.1.2.2 + P.g - 1) / P.g, (z.1.1.1.2, z.1.1.2))), z.2)))
    exact h
  have hm := Automatic.Poly.list_map (f := fun (y : (((S × KP) × List KP) × List KP) × List Bool) k =>
      point y.1.1.1.1.1 y.1.1.1.1.2.1 y.1.1.1.2 ((y.1.1.1.1.2.2 + P.g - 1) / P.g) y.1.1.2 y.1.2 k) hpt
    (RSSDTM.Poly.list_range_length (Automatic.Poly.snd (α := ((S × KP) × List KP) × List KP)
      (β := List Bool)))
  have h := Automatic.Poly.comp poly_outEnc (Automatic.Poly.pair
    (by fun_prop : Poly (fun y : (((S × KP) × List KP) × List KP) × List Bool => y.1.1.1.2)) hm)
  exact h

def full (s : S) : List Bool := fin P (st4 (st3 P (st2 P (st1 P s))))

theorem full_PT : PT qS (full P) :=
  PT.compP (PT.comp (PT.comp (PT.comp (st1_PT P) (st2_PT P) (PB.of_le (PB.q _) (fun _ => le_rfl)))
    (st3_PT P) (PB.of_le (PB.q _) (fun _ => le_rfl))) st4_PT (PB.of_le (PB.q _) (fun _ => le_rfl)))
    (g := fin P) (fin_poly P)

end Pipeline

/-! ## Correctness of the pipeline -/

section Correct
open RSSDAlg RSSDTMSpec RSListDecodingCapacity.AllRates

theorem encNat_len (k : ℕ) : (encNat k).length ≤ 2 * k + 2 := by
  unfold encNat encBits
  simp only [List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
  simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul]
  have := (Nat.digits_length_le_iff (b := 2) (k := k) (by norm_num) k).2 (Nat.lt_two_pow_self)
  omega

theorem flat_len (p : ℕ) (fc : List ℕ) (h : ∀ x ∈ fc, x < p) :
    (fc.flatMap encNat).length ≤ fc.length * (2 * p + 2) := by
  induction fc with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := encNat_len a
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h3 := h a List.mem_cons_self
    nlinarith

theorem input_len (p n : ℕ) (fc : List ℕ) (hfc : ∀ x ∈ fc, x < p) :
    (encNat p ++ encList encNat fc ++ encNat n).length ≤
      (2 * p + 2) + (2 * fc.length + 2) + fc.length * (2 * p + 2) + (2 * n + 2) := by
  unfold encList
  simp only [List.length_append]
  have := encNat_len p; have := encNat_len n; have := encNat_len fc.length; have := flat_len p fc hfc
  omega

theorem monic_length (p d deg j : ℕ) : (monicOfIdx p d deg j).length = deg + 1 := by
  simp [monicOfIdx, kpOfIdx]

theorem all_range (N : ℕ) (t : ℕ → Bool) : (List.range N).all t = decide (∀ i < N, t i = true) := by
  rw [Bool.eq_iff_iff]; simp

theorem fb_eq (t : ℕ → Bool) (N : ℕ) : RSSDTM.findBelow t N = RSSDAlg.findBelow t N :=
  RSSDTM.findBelow_eq t N

theorem hS_eq (m p : ℕ) (fc : List ℕ) : hS m (p, fc) = hSearch p fc m := by
  unfold hS hSearch
  rw [fb_eq]
  congr 2
  funext j
  simp only [hTest, irrM, isIrred, monic_length, Nat.add_sub_cancel, all_range]

theorem gam_eq (m p : ℕ) (fc : List ℕ) (hc : KP) (h : hc.length - 1 = m) (e : ℕ) :
    gam m e ((p, fc), hc) = gamSearch p fc hc e := by
  unfold gam gamSearch
  rw [fb_eq, h]
  rfl

theorem del_eq (m p : ℕ) (fc : List ℕ) (hc : KP) (h : hc.length - 1 = m) (R E e : ℕ) :
    del R e m (((p, fc), hc), E) = delSearch p fc hc e R E := by
  unfold del delSearch
  rw [fb_eq, h]
  congr 2
  funext j
  simp only [dTest, spM, dIdx, sparseOK, all_range]
  congr 1

theorem full_eq (P : Params) (s : S) : full P s = outEnc (construct P s.1 s.2.1 s.2.2) := by
  obtain ⟨p, fc, n⟩ := s
  have hl : (hSearch p fc P.m).length - 1 = P.m := by rw [hSearch, monic_length]; simp
  simp only [full, fin, st1, st2, st3, st4, construct, hS_eq, List.length_replicate, blk,
    gam_eq P.m p fc _ hl, del_eq P.m p fc _ hl]

end Correct

end RSSDTMC

namespace RSSDTMSpec
open RSListDecodingCapacity.AllRates RSSDAlg RSSDTMC

theorem construct_TM (P : Params) (hm : 1 ≤ P.m) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      ∀ (p : ℕ) (fc : List ℕ) (n : ℕ), 2 ≤ p → 1 ≤ dg fc → (∀ x ∈ fc, x < p) →
        n ≤ p ^ dg fc →
        HMBinPacking.OutputsWithin M (encNat p ++ encList encNat fc ++ encNat n)
          (outEnc (construct P p fc n)) ((p ^ dg fc) ^ C) := by
  obtain ⟨parse, hparse, hspec⟩ := exists_parse
  have hT : PT (fun w => qS (parse w)) (fun w => full P (parse w)) :=
    PT.pcomp hparse (full_PT P) (PB.of_le (PB.q _) (fun _ => le_rfl))
  obtain ⟨M, Pol, hM⟩ := PT.outputs hT
  obtain ⟨D, hD⟩ := eval_le_Qpow Pol 30 2
  refine ⟨M, D, fun p fc n hp hdf hfc hn => ?_⟩
  have key := hM (encNat p ++ encList encNat fc ++ encNat n) ((p ^ dg fc) ^ D) ?_
  · rwa [hspec, full_eq] at key
  · rw [hspec]
    set Q := p ^ dg fc with hQ
    have hpQ : p ≤ Q := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ Q := Nat.pow_le_pow_right (by omega) hdf
    have hdQ : dg fc < Q := (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hp _)
    have hlen : fc.length = dg fc + 1 := by have := hdf; unfold dg at this ⊢; omega
    have hin := input_len p n fc hfc
    rw [hlen] at hin
    have hQ2 : 2 ≤ Q := hp.trans hpQ
    apply hD Q _ hQ2
    simp only [qS]
    rw [← hQ]
    have h1 : (dg fc + 1) * (2 * p + 2) ≤ Q * (2 * Q + 2) := by
      apply Nat.mul_le_mul <;> omega
    nlinarith
end RSSDTMSpec


-- ===================== Main_assembly.lean

open Polynomial RSListDecodingCapacity.AllRates RSSubspaceDesign

namespace RSSDMain

/-- monotonicity of the design predicate in `τ` -/
theorem isSubspaceDesign_mono {E V : Type*} [Field E] [AddCommGroup V] [Module E V] {n : ℕ}
    {C : Submodule E (Fin n → V)} {τ τ' : ℕ → ℝ} (h : IsSubspaceDesign E C τ)
    (hτ : ∀ d, 1 ≤ d → τ d ≤ τ' d) : IsSubspaceDesign E C τ' := by
  intro d hd A hA hfin hrank
  exact (h d hd A hA hfin hrank).trans
    (mul_le_mul_of_nonneg_left (hτ d hd) (Nat.cast_nonneg _))

/-- existence of admissible parameters -/
theorem exists_valid (r g : ℕ) (hr : 2 ≤ r) (hg : 2 ≤ g) :
    ∃ Ps Qs : List ℕ, (⟨g, r, Ps, Qs⟩ : RSSDAlg.Params).Valid := by
  set L := g * 2 ^ r + (r * (2 ^ r + 1) + 2 * 2 ^ r + 7) with hL
  let pr : ℕ → ℕ := fun i => Nat.nth Nat.Prime (L + i)
  have hinf := Nat.infinite_setOfPred_prime
  have hprinj : Function.Injective pr := fun i j h => by
    have := Nat.nth_injective hinf h
    omega
  have hprge : ∀ i, L ≤ pr i := fun i =>
    (Nat.le_add_right L i).trans (Nat.le_nth (fun hf => absurd hf hinf))
  refine ⟨(List.range g).map pr, (List.range g).map (fun i => pr (g + i)), ?_⟩
  have happ : (List.range g).map pr ++ (List.range g).map (fun i => pr (g + i)) =
      (List.range (g + g)).map pr := by
    rw [List.range_add, List.map_append, List.map_map]; rfl
  refine ⟨hr, hg, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [happ, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact Nat.prime_nth_prime _
  · rw [happ]
    exact List.Nodup.map hprinj List.nodup_range
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact le_trans (by dsimp only; omega) (hprge i)
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact le_trans (by dsimp only; omega) (hprge (g + i))

theorem m_pos (P : RSSDAlg.Params) (hP : P.Valid) : 1 ≤ P.m := by
  obtain ⟨-, -, -, -, hpr, -, -, -⟩ := hP
  unfold RSSDAlg.Params.m
  apply Nat.one_le_iff_ne_zero.mpr 
  apply Nat.pos_iff_ne_zero.mp
  apply List.prod_pos
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < P.Ps.length ∧ i < P.Qs.length := by
    rw [List.length_zipWith] at hi; omega
  rw [List.getElem_zipWith]
  have h1 := (hpr _ (List.mem_append_left _ (List.getElem_mem (l := P.Ps) hi'.1))).pos
  have h2 := (hpr _ (List.mem_append_right _ (List.getElem_mem (l := P.Qs) hi'.2))).pos
  exact Nat.mul_pos h1 h2

/-- the arithmetic of `τ` -/
theorem tau_le (r g n k b d : ℕ) (ε : ℝ) (hε : 0 < ε) (hr : 2 ≤ r) (hg : 8 * (r : ℝ) / ε ≤ g)
    (hn : 8 * (r : ℝ) / ε ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hb : b = RSSDAlg.blk g n)
    (hd1 : 1 ≤ d) :
    (if d ≤ r then min 1 (((k : ℝ) - 1) / n + (b : ℝ) / n * Real.logb 2 d) else 1) ≤
      (if d ≤ r then min 1 ((k : ℝ) / n + ε / 4) else 1) := by
  split_ifs with hdr
  · apply min_le_min_left
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
    have hg0 : (0 : ℝ) < g := lt_of_lt_of_le (by positivity) hg
    -- b ≤ n/g + 1
    have hb' : (b : ℝ) ≤ n / g + 1 := by
      subst hb
      have hgpos : 0 < g := by exact_mod_cast hg0
      have h1 : RSSDAlg.blk g n * g ≤ n + g - 1 := Nat.div_mul_le_self _ _
      have h2 : ((RSSDAlg.blk g n * g : ℕ) : ℝ) ≤ n + g := by
        have : RSSDAlg.blk g n * g ≤ n + g := by omega
        exact_mod_cast this
      rw [Nat.cast_mul] at h2
      rw [div_add_one hg0.ne', le_div_iff₀ hg0]
      exact h2
    -- log₂ d ≤ r
    have hlog : Real.logb 2 d ≤ r := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have h1 : Real.logb 2 d ≤ Real.logb 2 r :=
        Real.logb_le_logb_of_le (by norm_num) hd0 (by exact_mod_cast hdr)
      have h2 : Real.logb 2 r ≤ r := by
        rw [Real.logb_le_iff_le_rpow (by norm_num) hr0, Real.rpow_natCast]
        exact_mod_cast (Nat.lt_two_pow_self).le
      linarith
    have hlog0 : 0 ≤ Real.logb 2 d :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hd1)
    have hrg : (r : ℝ) / g ≤ ε / 8 := by
      rw [div_le_iff₀ hg0]; rw [div_le_iff₀ hε] at hg; nlinarith
    have hrn : (r : ℝ) / n ≤ ε / 8 := by
      rw [div_le_iff₀ hn0]; rw [div_le_iff₀ hε] at hn; nlinarith
    have key : (b : ℝ) / n * Real.logb 2 d ≤ ε / 4 := by
      calc (b : ℝ) / n * Real.logb 2 d ≤ (n / g + 1) / n * r := by
            apply mul_le_mul (div_le_div_of_nonneg_right hb' hn0.le) hlog hlog0 (by positivity)
        _ = r / g + r / n := by field_simp
        _ ≤ ε / 4 := by linarith
    have : ((k : ℝ) - 1) / n ≤ (k : ℝ) / n := div_le_div_of_nonneg_right (by linarith) hn0.le
    linarith
  · exact le_rfl

end RSSDMain

open RSSDMain in
theorem solution :
    ∀ r : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (M : Turing.TM2ComputableAux Bool Bool) (N D C : ℕ),
        ∀ n : ℕ, N ≤ n →
        ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
          n ≤ p ^ f.natDegree →
          ∃ (hc : List (List ℕ)) (ac : List (List (List ℕ))),
            IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc ∧
            ac.length = n ∧ (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
            HMBinPacking.OutputsWithin M (encField p f ++ encNat n)
              (encList (encList encNat) hc ++ encList (encList (encList encNat)) ac)
              ((p ^ f.natDegree) ^ C) ∧
            (decPoly p f hc).Monic ∧ Irreducible (decPoly p f hc) ∧
            (decPoly p f hc).natDegree ≤ D ∧
            ∃ hα : Function.Injective fun i : Fin n =>
                AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i [])),
              ∀ k : ℕ, 1 ≤ k → k ≤ n →
              ∀ (K₀ : Type) [Field K₀] [Algebra K₀ (AdjoinRoot f)],
                IsSubspaceDesign K₀ ((ReedSolomon.code ⟨_, hα⟩ k).restrictScalars K₀)
                  fun d => if d ≤ r then min 1 ((k : ℝ) / n + ε / 4) else 1 := by
  intro r hr ε hε hε1
  set g : ℕ := ⌈8 * (r : ℝ) / ε⌉₊ + 2 with hgdef
  have hg2 : 2 ≤ g := by omega
  have hgε : 8 * (r : ℝ) / ε ≤ g := by
    rw [hgdef]; push_cast
    linarith [Nat.le_ceil (8 * (r : ℝ) / ε)]
  obtain ⟨Ps, Qs, hP⟩ := exists_valid r g hr hg2
  set P : RSSDAlg.Params := ⟨g, r, Ps, Qs⟩ with hPdef
  obtain ⟨M, C, hM⟩ := RSSDTMSpec.construct_TM P (m_pos P hP)
  refine ⟨M, max g (2 ^ r), P.m, C, ?_⟩
  intro n hn p _ f _ hf hnK
  have hng : g ≤ n := le_of_max_le_left hn
  have hnR : 2 ^ r ≤ n := le_of_max_le_right hn
  have hcor := RSSDAlg.construct_correct P hP p f hf n hng hnR hnK
  set out := RSSDAlg.construct P p (RSSDAlg.fcOf f) n with hout
  obtain ⟨hIC, hlen, hIC2, hmon, hirr, hdeg, hα, hEff⟩ := hcor
  refine ⟨out.1, out.2, hIC, hlen, hIC2, ?_, hmon, hirr, hdeg.le, hα, ?_⟩
  · -- the machine
    have hdeg1 : 1 ≤ f.natDegree := (Irreducible.natDegree_pos (Fact.out)).nat_succ_le
    have hdg : RSSDAlg.dg (RSSDAlg.fcOf f) = f.natDegree := by
      simp [RSSDAlg.dg, RSSDAlg.fcOf]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hfc : ∀ x ∈ RSSDAlg.fcOf f, x < p := by
      intro x hx
      simp only [RSSDAlg.fcOf, List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact ZMod.val_lt _
    have := hM p (RSSDAlg.fcOf f) n hp2 (hdg ▸ hdeg1) hfc (hdg ▸ hnK)
    rw [hdg] at this
    exact this
  · intro k hk1 hkn K₀ _ _
    haveI : Fact (Irreducible (decPoly p f out.1)) := ⟨hirr⟩
    haveI : Finite (AdjoinRoot f) := by
      haveI := (AdjoinRoot.powerBasis (Fact.out : Irreducible f).ne_zero).finite
      exact Module.finite_of_finite (ZMod p)
    haveI : Finite (AdjoinRoot (decPoly p f out.1)) := by
      haveI := (AdjoinRoot.powerBasis hirr.ne_zero).finite
      exact Module.finite_of_finite (AdjoinRoot f)
    have h42 := theorem_4_2 (K := AdjoinRoot f) (F := AdjoinRoot (decPoly p f out.1))
      ⟨_, hα⟩ hEff k hk1 hkn
    have h42' := isSubspaceDesign_mono h42 (fun d hd => tau_le r g n k (RSSDAlg.blk g n) d ε hε
      hr hgε (hgε.trans (by exact_mod_cast hng)) hk1 hkn rfl hd)
    have h45 := lemma_4_5 (K₀ := K₀) (K := AdjoinRoot f) (V := AdjoinRoot (decPoly p f out.1)) _ _ h42'
    rw [Submodule.restrictScalars_restrictScalars] at h45
    exact h45

