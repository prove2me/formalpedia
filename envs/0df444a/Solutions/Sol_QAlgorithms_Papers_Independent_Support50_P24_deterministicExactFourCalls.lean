-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P24.deterministicExactFourCalls
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T17:36:13.670306+00:00
-- url     : https://prove2.me/submissions/fd9de1f9-9080-4fbc-8122-1cbd2718840d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

open QAlgorithms QAlgorithms.Papers.Independent.Support50
open scoped Matrix ComplexConjugate BigOperators

namespace S190P24_aux

/-! ### `ℤ[√2, √3]` as signed natural quadruples -/

noncomputable def r2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
noncomputable def r3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

lemma r2_sq : r2 ^ 2 = 2 := by
  unfold r2; rw [← Complex.ofReal_pow]; simp
lemma r3_sq : r3 ^ 2 = 3 := by
  unfold r3; rw [← Complex.ofReal_pow]; simp
lemma r2_ne : r2 ≠ 0 := by
  intro h; have := r2_sq; rw [h] at this; norm_num at this
lemma r3_ne : r3 ≠ 0 := by
  intro h; have := r3_sq; rw [h] at this; norm_num at this
lemma star_r2 : star r2 = r2 := by simp [r2]
lemma star_r3 : star r3 = r3 := by simp [r3]

structure KN where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def KN.add (x y : KN) : KN := ⟨Nat.add x.a y.a, Nat.add x.b y.b, Nat.add x.c y.c, Nat.add x.d y.d⟩

def KN.mul (x y : KN) : KN :=
  ⟨Nat.add (Nat.add (Nat.mul x.a y.a) (Nat.mul 2 (Nat.mul x.b y.b)))
     (Nat.add (Nat.mul 3 (Nat.mul x.c y.c)) (Nat.mul 6 (Nat.mul x.d y.d))),
   Nat.add (Nat.add (Nat.mul x.a y.b) (Nat.mul x.b y.a))
     (Nat.mul 3 (Nat.add (Nat.mul x.c y.d) (Nat.mul x.d y.c))),
   Nat.add (Nat.add (Nat.mul x.a y.c) (Nat.mul x.c y.a))
     (Nat.mul 2 (Nat.add (Nat.mul x.b y.d) (Nat.mul x.d y.b))),
   Nat.add (Nat.add (Nat.mul x.a y.d) (Nat.mul x.d y.a))
     (Nat.add (Nat.mul x.b y.c) (Nat.mul x.c y.b))⟩

noncomputable def KN.toC (x : KN) : ℂ :=
  (x.a : ℂ) + (x.b : ℂ) * r2 + (x.c : ℂ) * r3 + (x.d : ℂ) * (r2 * r3)

lemma KN.toC_add (x y : KN) : (x.add y).toC = x.toC + y.toC := by
  simp only [KN.toC, KN.add, Nat.add_eq]; push_cast; ring

lemma KN.toC_mul (x y : KN) : (x.mul y).toC = x.toC * y.toC := by
  simp only [KN.toC, KN.mul, Nat.add_eq, Nat.mul_eq]
  push_cast
  linear_combination (-(x.b:ℂ) * y.b - x.d * y.d * r3 ^ 2 - (x.b * y.d + x.d * y.b) * r3) * r2_sq
    + (-(x.c:ℂ) * y.c - 2 * x.d * y.d - (x.c * y.d + x.d * y.c) * r2) * r3_sq

lemma KN.star_toC (x : KN) : star x.toC = x.toC := by
  simp only [KN.toC, star_add, star_mul', star_r2, star_r3]
  simp

structure KS where
  p : KN
  n : KN

def KS.add (x y : KS) : KS := ⟨x.p.add y.p, x.n.add y.n⟩
def KS.mul (x y : KS) : KS := ⟨(x.p.mul y.p).add (x.n.mul y.n), (x.p.mul y.n).add (x.n.mul y.p)⟩
def KS.neg (x : KS) : KS := ⟨x.n, x.p⟩

noncomputable def KS.toC (x : KS) : ℂ := x.p.toC - x.n.toC

lemma KS.toC_add (x y : KS) : (x.add y).toC = x.toC + y.toC := by
  simp only [KS.toC, KS.add, KN.toC_add]; ring
lemma KS.toC_mul (x y : KS) : (x.mul y).toC = x.toC * y.toC := by
  simp only [KS.toC, KS.mul, KN.toC_add, KN.toC_mul]; ring
lemma KS.toC_neg (x : KS) : x.neg.toC = -x.toC := by
  simp only [KS.toC, KS.neg]; ring
lemma KS.star_toC (x : KS) : star x.toC = x.toC := by
  simp only [KS.toC, star_sub, KN.star_toC]

def KS.isZero (x : KS) : Bool :=
  Nat.beq x.p.a x.n.a && Nat.beq x.p.b x.n.b && Nat.beq x.p.c x.n.c && Nat.beq x.p.d x.n.d

lemma KS.toC_of_isZero (x : KS) (h : x.isZero = true) : x.toC = 0 := by
  simp only [KS.isZero, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp [KS.toC, KN.toC, h1, h2, h3, h4]

def kZ : KS := ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
def k1 : KS := ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
def km1 : KS := ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩
def kR2 : KS := ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
def kR3 : KS := ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩

@[simp] lemma toC_kZ : kZ.toC = 0 := by simp [kZ, KS.toC, KN.toC]
@[simp] lemma toC_k1 : k1.toC = 1 := by simp [k1, KS.toC, KN.toC]
@[simp] lemma toC_km1 : km1.toC = -1 := by simp [km1, KS.toC, KN.toC]
@[simp] lemma toC_kR2 : kR2.toC = r2 := by simp [kR2, KS.toC, KN.toC]
@[simp] lemma toC_kR3 : kR3.toC = r3 := by simp [kR3, KS.toC, KN.toC]

def KS.pow (x : KS) : ℕ → KS
  | 0 => k1
  | k + 1 => (x.pow k).mul x

lemma KS.toC_pow (x : KS) (k : ℕ) : (x.pow k).toC = x.toC ^ k := by
  induction k with
  | zero => simp [KS.pow]
  | succ k ih => rw [KS.pow, KS.toC_mul, ih, pow_succ]

/-! ### Monomials in `U` entries and `φ` entries -/

structure Mono where
  e0 : ℕ
  e1 : ℕ
  e2 : ℕ
  e3 : ℕ
  f0 : ℕ
  f1 : ℕ
deriving DecidableEq

def Mono.one : Mono := ⟨0, 0, 0, 0, 0, 0⟩
def Mono.mul (m n : Mono) : Mono :=
  ⟨Nat.add m.e0 n.e0, Nat.add m.e1 n.e1, Nat.add m.e2 n.e2, Nat.add m.e3 n.e3,
    Nat.add m.f0 n.f0, Nat.add m.f1 n.f1⟩

noncomputable def Mono.ev (U : Matrix Bool Bool ℂ) (φ : Bool → ℂ) (m : Mono) : ℂ :=
  U false false ^ m.e0 * U false true ^ m.e1 * U true false ^ m.e2 * U true true ^ m.e3 *
    φ false ^ m.f0 * φ true ^ m.f1

@[simp] lemma ev_one (U φ) : Mono.ev U φ Mono.one = 1 := by simp [Mono.ev, Mono.one]
lemma ev_mul (U φ) (m n : Mono) : Mono.ev U φ (m.mul n) = Mono.ev U φ m * Mono.ev U φ n := by
  simp only [Mono.ev, Mono.mul, Nat.add_eq, pow_add]; ring

/-! ### Basis indices -/

def getB (n : Fin 128) (i : Fin 7) : Bool := n.val.testBit i.val

def toSeven (n : Fin 128) : Fin 7 → Bool := fun i => getB n i

def setB (n : Fin 128) (i : Fin 7) (b : Bool) : Fin 128 :=
  if b then ⟨n.val ||| 2 ^ i.val,
    Nat.or_lt_two_pow (n := 7) n.isLt (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩
  else ⟨n.val &&& (127 ^^^ 2 ^ i.val), lt_of_le_of_lt Nat.and_le_left n.isLt⟩

lemma setB_spec_aux (n : Fin 128) (i : Fin 7) (b : Bool) (j : Fin 7) :
    getB (setB n i b) j = (if j = i then b else getB n j) := by
  have h127 : ∀ j : Fin 7, Nat.testBit 127 j.val = true := by decide
  by_cases hji : j = i
  · subst hji
    cases b <;> simp [setB, getB, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h127]
  · have : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    cases b <;>
      simp [setB, getB, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h127, hji, this]

lemma toSeven_setB (n : Fin 128) (i : Fin 7) (b : Bool) :
    toSeven (setB n i b) = Function.update (toSeven n) i b := by
  funext j
  simp only [toSeven, setB_spec_aux, Function.update_apply]

/-! ### Polynomial-coefficient sparse vectors -/

structure Tm where
  idx : Fin 128
  mo : Mono
  co : KS

noncomputable def tval (U : Matrix Bool Bool ℂ) (φ : Bool → ℂ) (t : Tm) : ℂ :=
  t.co.toC * t.mo.ev U φ

noncomputable def interp (U : Matrix Bool Bool ℂ) (φ : Bool → ℂ) (L : List Tm) :
    (Fin 7 → Bool) → ℂ :=
  fun x => (L.map fun t => if x = toSeven t.idx then tval U φ t else 0).sum

variable (U : Matrix Bool Bool ℂ) (φ : Bool → ℂ)

@[simp] lemma interp_nil : interp U φ [] = 0 := by funext x; simp [interp]

lemma interp_cons (t : Tm) (L : List Tm) :
    interp U φ (t :: L) = Pi.single (toSeven t.idx) (tval U φ t) + interp U φ L := by
  funext x; simp [interp, Pi.single_apply]

lemma interp_append (L₁ L₂ : List Tm) :
    interp U φ (L₁ ++ L₂) = interp U φ L₁ + interp U φ L₂ := by
  funext x; simp [interp]

def scaleBy (t t' : Tm) : Tm := ⟨t'.idx, t.mo.mul t'.mo, t.co.mul t'.co⟩

lemma interp_map_scaleBy (t : Tm) (l : List Tm) :
    interp U φ (l.map (scaleBy t)) = tval U φ t • interp U φ l := by
  induction l with
  | nil => simp
  | cons t' l ih =>
    rw [List.map_cons, interp_cons, interp_cons, ih, smul_add]
    congr 1
    funext x
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul, scaleBy, tval, KS.toC_mul, ev_mul]
    split_ifs <;> ring

def applyCol (col : Fin 128 → List Tm) (L : List Tm) : List Tm :=
  L.flatMap fun t => (col t.idx).map (scaleBy t)

lemma apply_correct (M : Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ) (col : Fin 128 → List Tm)
    (s : ℂ) (hcol : ∀ n x, M x (toSeven n) = s * interp U φ (col n) x) (L : List Tm) :
    M *ᵥ interp U φ L = s • interp U φ (applyCol col L) := by
  induction L with
  | nil => simp [applyCol]
  | cons t L ih =>
    rw [interp_cons, Matrix.mulVec_add, ih]
    simp only [applyCol, List.flatMap_cons, interp_append, smul_add]
    congr 1
    rw [interp_map_scaleBy]
    funext x
    simp [hcol]
    ring

def relabel (σ : Fin 128 → Fin 128) (t : Tm) : Tm := ⟨σ t.idx, t.mo, t.co⟩

lemma perm_correct (M : Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ) (σ : Fin 128 → Fin 128)
    (hcol : ∀ n x, M x (toSeven n) = if x = toSeven (σ n) then 1 else 0) (L : List Tm) :
    M *ᵥ interp U φ L = interp U φ (L.map (relabel σ)) := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [interp_cons, Matrix.mulVec_add, ih, List.map_cons, interp_cons]
    congr 1
    funext x
    simp [hcol, relabel, Pi.single_apply, tval]

/-! ### Normalisation -/

def keyOf (t : Tm) : Fin 128 × Mono := (t.idx, t.mo)

def keyCode (t : Tm) : ℕ :=
  Nat.add t.idx.val (Nat.mul 128 (Nat.add t.mo.e0 (Nat.mul 8 (Nat.add t.mo.e1 (Nat.mul 8
    (Nat.add t.mo.e2 (Nat.mul 8 (Nat.add t.mo.e3 (Nat.mul 8 (Nat.add t.mo.f0
      (Nat.mul 8 t.mo.f1)))))))))))

def insertTm : List Tm → Tm → List Tm
  | [], t => [t]
  | s :: rest, t =>
    if (Nat.beq (keyCode s) (keyCode t) && decide (keyOf s = keyOf t)) = true then
      ⟨s.idx, s.mo, s.co.add t.co⟩ :: rest else s :: insertTm rest t

lemma interp_insertTm (acc : List Tm) (t : Tm) :
    interp U φ (insertTm acc t) = interp U φ acc + interp U φ [t] := by
  induction acc with
  | nil => simp [insertTm]
  | cons s rest ih =>
    simp only [insertTm]
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [keyOf, Prod.mk.injEq] at h
      obtain ⟨-, h1, h2⟩ := h
      simp only [interp_cons, interp_nil, tval, KS.toC_add, add_mul, Pi.single_add, ← h1, ← h2]
      abel
    · rw [interp_cons, interp_cons, ih]; abel

lemma interp_foldl_insert (acc L : List Tm) :
    interp U φ (L.foldl insertTm acc) = interp U φ acc + interp U φ L := by
  induction L generalizing acc with
  | nil => simp
  | cons t L ih =>
    rw [List.foldl_cons, ih, interp_insertTm, interp_cons (L := L), interp_cons (L := [])]
    simp only [interp_nil]; abel

def normalize (L : List Tm) : List Tm :=
  (L.foldl insertTm []).filter fun t => !t.co.isZero

lemma interp_filter (L : List Tm) :
    interp U φ (L.filter fun t => !t.co.isZero) = interp U φ L := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.filter_cons]
    by_cases h : t.co.isZero = true
    · simp [h, ih, interp_cons, tval, KS.toC_of_isZero _ h]
    · simp [h, ih, interp_cons]

lemma interp_normalize (L : List Tm) : interp U φ (normalize L) = interp U φ L := by
  rw [normalize, interp_filter, interp_foldl_insert, interp_nil, zero_add]

def scaleL (c : KS) (L : List Tm) : List Tm := L.map fun t => ⟨t.idx, t.mo, c.mul t.co⟩

lemma interp_scaleL (c : KS) (L : List Tm) : interp U φ (scaleL c L) = c.toC • interp U φ L := by
  induction L with
  | nil => simp [scaleL]
  | cons t L ih =>
    simp only [scaleL, List.map_cons] at ih ⊢
    rw [interp_cons, interp_cons, ih, smul_add]
    congr 1
    funext x
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul, tval, KS.toC_mul]
    split_ifs <;> ring

def negL (L : List Tm) : List Tm := L.map fun t => ⟨t.idx, t.mo, t.co.neg⟩

lemma interp_negL (L : List Tm) : interp U φ (negL L) = -interp U φ L := by
  induction L with
  | nil => simp [negL]
  | cons t L ih =>
    simp only [negL, List.map_cons] at ih ⊢
    rw [interp_cons, interp_cons, ih, neg_add]
    congr 1
    funext x
    simp only [Pi.single_apply, Pi.neg_apply, tval, KS.toC_neg]
    split_ifs <;> ring

def eqCheck (L₁ L₂ : List Tm) : Bool := (normalize (L₁ ++ negL L₂)).isEmpty

lemma interp_eq_of_check (L₁ L₂ : List Tm) (h : eqCheck L₁ L₂ = true) :
    interp U φ L₁ = interp U φ L₂ := by
  have h0 := interp_normalize U φ (L₁ ++ negL L₂)
  rw [List.isEmpty_iff.mp h, interp_append, interp_negL, interp_nil] at h0
  exact (sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0.symm))

/-- scaling `(1/√2)^k (1/√3)^m`. -/
noncomputable def scal (e : ℕ × ℕ) : ℂ := r2⁻¹ ^ e.1 * r3⁻¹ ^ e.2

def pw (e : ℕ × ℕ) : KS := (kR2.pow e.1).mul (kR3.pow e.2)

lemma toC_pw (e : ℕ × ℕ) : (pw e).toC = r2 ^ e.1 * r3 ^ e.2 := by
  simp [pw, KS.toC_mul, KS.toC_pow]

lemma final_eq (e₁ e₂ : ℕ × ℕ) (L R : List Tm)
    (h : eqCheck (scaleL (pw e₂) L) (scaleL (pw e₁) R) = true) :
    scal e₁ • interp U φ L = scal e₂ • interp U φ R := by
  have h0 := interp_eq_of_check U φ _ _ h
  rw [interp_scaleL, interp_scaleL, toC_pw, toC_pw] at h0
  have hc : scal e₁ * scal e₂ * (r2 ^ e₂.1 * r3 ^ e₂.2) = scal e₁ ∧
      scal e₁ * scal e₂ * (r2 ^ e₁.1 * r3 ^ e₁.2) = scal e₂ := by
    simp only [scal, inv_pow]
    constructor <;> field_simp [r2_ne, r3_ne]
  have kL : scal e₁ • interp U φ L =
      (scal e₁ * scal e₂) • ((r2 ^ e₂.1 * r3 ^ e₂.2) • interp U φ L) := by rw [smul_smul, hc.1]
  have kR : scal e₂ • interp U φ R =
      (scal e₁ * scal e₂) • ((r2 ^ e₁.1 * r3 ^ e₁.2) • interp U φ R) := by rw [smul_smul, hc.2]
  rw [kL, kR, h0]

/-! ### Gates -/

def ctrlB (cs : List (Fin 7 × Bool)) (n : Fin 128) : Bool := cs.all fun p => getB n p.1 == p.2

lemma ctrlB_iff (cs : List (Fin 7 × Bool)) (n : Fin 128) :
    ctrlB cs n = true ↔ ∀ c ∈ cs, toSeven n c.1 = c.2 := by
  simp [ctrlB, toSeven]

/-- scale classes: `1`, `1/√2`, `1/√3`. -/
inductive Sc where
  | one
  | i2
  | i3

def Sc.e : Sc → ℕ × ℕ
  | .one => (0, 0)
  | .i2 => (1, 0)
  | .i3 => (0, 1)

def Sc.idc : Sc → KS
  | .one => k1
  | .i2 => kR2
  | .i3 => kR3

lemma Sc.scal_idc (s : Sc) : scal s.e * s.idc.toC = 1 := by
  cases s <;> simp [scal, Sc.e, Sc.idc, r2_ne, r3_ne]

inductive GS where
  | cg (cs : List (Fin 7 × Bool)) (t : Fin 7) (A : Bool → Bool → Mono × KS) (s : Sc)
  | cx (cs : List (Fin 7 × Bool)) (t : Fin 7)
  | sw (cs : List (Fin 7 × Bool)) (a b : Fin 7)

def colCG (cs : List (Fin 7 × Bool)) (t : Fin 7) (A : Bool → Bool → Mono × KS) (s : Sc)
    (n : Fin 128) : List Tm :=
  if ctrlB cs n then
      [⟨setB n t false, (A false (getB n t)).1, (A false (getB n t)).2⟩,
       ⟨setB n t true, (A true (getB n t)).1, (A true (getB n t)).2⟩]
    else [⟨n, Mono.one, s.idc⟩]

def sigCX (cs : List (Fin 7 × Bool)) (t : Fin 7) (n : Fin 128) : Fin 128 :=
  if ctrlB cs n then setB n t (!getB n t) else n

def sigSW (cs : List (Fin 7 × Bool)) (a b : Fin 7) (n : Fin 128) : Fin 128 :=
  if ctrlB cs n then setB (setB n a (getB n b)) b (getB n a) else n

noncomputable def evM (A : Bool → Bool → Mono × KS) : Matrix Bool Bool ℂ :=
  fun a b => (A a b).2.toC * (A a b).1.ev U φ

noncomputable def denote : GS → Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ
  | .cg cs t A s => P24.controlledGate cs t (scal s.e • evM U φ A)
  | .cx cs t => P24.controlledGate cs t P24.bitFlip
  | .sw cs a b => P24.sevenControlledSwap cs a b

lemma agree_split (x y : Fin 7 → Bool) (t : Fin 7) (F : Bool → ℂ) :
    (if ∀ i, i ≠ t → x i = y i then F (x t) else 0) =
      (if x = Function.update y t false then F false else 0) +
      (if x = Function.update y t true then F true else 0) := by
  by_cases h : ∀ i, i ≠ t → x i = y i
  · have hx : x = Function.update y t (x t) := by
      funext i; by_cases hi : i = t
      · subst hi; simp
      · simp [hi, h i hi]
    rw [if_pos h]
    cases hxt : x t
    · rw [hxt] at hx
      rw [if_pos hx, if_neg]; · simp
      intro h'; have := congrFun h' t; simp [hxt] at this
    · rw [hxt] at hx
      rw [if_pos hx, if_neg]; · simp
      intro h'; have := congrFun h' t; simp [hxt] at this
  · rw [if_neg h, if_neg, if_neg]; · simp
    all_goals
      rintro rfl
      exact h (fun i hi => by simp [hi])

lemma agree_eq (x y : Fin 7 → Bool) (t : Fin 7) :
    (if ∀ i, i ≠ t → x i = y i then (if x t = y t then (1:ℂ) else 0) else 0) =
      if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    split_ifs with h1 h2
    · exact absurd (funext fun i => by
        by_cases hi : i = t
        · subst hi; exact h2
        · exact h1 i hi) hxy
    · rfl
    · rfl

lemma cg_correct (cs : List (Fin 7 × Bool)) (t : Fin 7) (A : Bool → Bool → Mono × KS) (s : Sc)
    (n : Fin 128) (x : Fin 7 → Bool) :
    denote U φ (.cg cs t A s) x (toSeven n) = scal s.e * interp U φ (colCG cs t A s n) x := by
  simp only [denote, colCG, P24.controlledGate]
  by_cases hc : ctrlB cs n = true
  · rw [if_pos hc, if_pos ((ctrlB_iff cs n).mp hc)]
    rw [agree_split x (toSeven n) t (fun a => (scal s.e • evM U φ A) a (toSeven n t))]
    simp [interp, toSeven_setB, tval, evM, toSeven]
    split_ifs <;> ring
  · rw [if_neg hc, if_neg (fun h => hc ((ctrlB_iff cs n).mpr h)), agree_eq]
    simp only [interp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval,
      ev_one, mul_one]
    split_ifs
    · rw [Sc.scal_idc]
    · simp

lemma cx_correct (cs : List (Fin 7 × Bool)) (t : Fin 7) (n : Fin 128) (x : Fin 7 → Bool) :
    denote U φ (.cx cs t) x (toSeven n) = if x = toSeven (sigCX cs t n) then 1 else 0 := by
  by_cases hc : ctrlB cs n = true
  · have hs : sigCX cs t n = setB n t (!getB n t) := by simp [sigCX, hc]
    rw [hs]
    simp only [denote, P24.controlledGate]
    rw [if_pos ((ctrlB_iff cs n).mp hc)]
    rw [agree_split x (toSeven n) t (fun a => P24.bitFlip a (toSeven n t))]
    cases hb : getB n t <;> simp [toSeven_setB, P24.bitFlip, toSeven, hb]
  · have hs : sigCX cs t n = n := by simp [sigCX, hc]
    rw [hs]
    simp only [denote, P24.controlledGate]
    rw [if_neg (fun h => hc ((ctrlB_iff cs n).mpr h)), agree_eq]

lemma sw_correct (cs : List (Fin 7 × Bool)) (a b : Fin 7) (n : Fin 128) (x : Fin 7 → Bool) :
    denote U φ (.sw cs a b) x (toSeven n) = if x = toSeven (sigSW cs a b n) then 1 else 0 := by
  by_cases hc : ctrlB cs n = true
  · have hs : sigSW cs a b n = setB (setB n a (getB n b)) b (getB n a) := by simp [sigSW, hc]
    rw [hs]
    simp only [denote, P24.sevenControlledSwap]
    rw [if_pos ((ctrlB_iff cs n).mp hc)]
    simp only [toSeven_setB]
    split_ifs <;> simp_all [toSeven]
  · have hs : sigSW cs a b n = n := by simp [sigSW, hc]
    rw [hs]
    simp only [denote, P24.sevenControlledSwap]
    rw [if_neg (fun h => hc ((ctrlB_iff cs n).mpr h))]

def step (g : GS) (L : List Tm) : List Tm :=
  match g with
  | .cg cs t A s => normalize (applyCol (colCG cs t A s) L)
  | .cx cs t => L.map (relabel (sigCX cs t))
  | .sw cs a b => L.map (relabel (sigSW cs a b))

def GS.e : GS → ℕ × ℕ
  | .cg _ _ _ s => s.e
  | _ => (0, 0)

def run (gs : List GS) (L : List Tm) : List Tm := gs.foldl (fun L g => step g L) L

def runE (gs : List GS) : ℕ × ℕ :=
  gs.foldl (fun e g => (Nat.add e.1 g.e.1, Nat.add e.2 g.e.2)) (0, 0)

lemma step_correct (g : GS) (L : List Tm) :
    denote U φ g *ᵥ interp U φ L = scal g.e • interp U φ (step g L) := by
  cases g with
  | cg cs t A s =>
    rw [apply_correct U φ _ (colCG cs t A s) (scal s.e) (cg_correct U φ cs t A s) L]
    simp only [step, GS.e, interp_normalize]
  | cx cs t =>
    rw [perm_correct U φ _ (sigCX cs t) (cx_correct U φ cs t) L]
    simp [step, GS.e, scal]
  | sw cs a b =>
    rw [perm_correct U φ _ (sigSW cs a b) (sw_correct U φ cs a b) L]
    simp [step, GS.e, scal]

lemma chron_foldl (l : List (Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ)) (A) :
    l.foldl (fun acc g => g * acc) A = P24.chronological l * A := by
  induction l generalizing A with
  | nil => simp [P24.chronological]
  | cons g l ih =>
    simp only [List.foldl_cons, P24.chronological]
    rw [ih, ih (g * 1), Matrix.mul_one, Matrix.mul_assoc]

lemma chron_nil : P24.chronological [] = 1 := rfl

lemma chron_cons (g) (l : List (Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ)) :
    P24.chronological (g :: l) = P24.chronological l * g := by
  conv_lhs => rw [P24.chronological, List.foldl_cons, chron_foldl, Matrix.mul_one]

lemma chron_append (l₁ l₂ : List (Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ)) :
    P24.chronological (l₁ ++ l₂) = P24.chronological l₂ * P24.chronological l₁ := by
  rw [P24.chronological, List.foldl_append, chron_foldl, ← P24.chronological]

lemma scal_add (e f : ℕ × ℕ) : scal (Nat.add e.1 f.1, Nat.add e.2 f.2) = scal e * scal f := by
  simp only [scal, Nat.add_eq, pow_add]; ring

lemma run_correct_aux (gs : List GS) (L : List Tm) (e : ℕ × ℕ) :
    scal e • P24.chronological (gs.map (denote U φ)) *ᵥ interp U φ L =
      scal (gs.foldl (fun e g => (Nat.add e.1 g.e.1, Nat.add e.2 g.e.2)) e) •
        interp U φ (run gs L) := by
  induction gs generalizing L e with
  | nil => simp [chron_nil, run]
  | cons g gs ih =>
    rw [List.map_cons, chron_cons, ← Matrix.mulVec_mulVec, step_correct, Matrix.mulVec_smul,
      smul_smul, ← scal_add, ih]
    rfl

lemma run_correct (gs : List GS) (L : List Tm) :
    P24.chronological (gs.map (denote U φ)) *ᵥ interp U φ L =
      scal (runE gs) • interp U φ (run gs L) := by
  have := run_correct_aux U φ gs L (0, 0)
  simp only [scal, pow_zero, mul_one, one_smul] at this
  exact this

/-! ### Concrete gate models -/

def rotP2 : Bool → Bool → Mono × KS := fun a b =>
  (Mono.one, if a = b then k1 else if a then k1 else km1)
def rotPi : Bool → Bool → Mono × KS := fun a b =>
  (Mono.one, if a = b then kZ else if a then k1 else km1)
def rotT : Bool → Bool → Mono × KS := fun a b =>
  (Mono.one, if a = b then kR2 else if a then k1 else km1)
def rotMT : Bool → Bool → Mono × KS := fun a b =>
  (Mono.one, if a = b then kR2 else if a then km1 else k1)

def monoU : Bool → Bool → Mono
  | false, false => ⟨1, 0, 0, 0, 0, 0⟩
  | false, true => ⟨0, 1, 0, 0, 0, 0⟩
  | true, false => ⟨0, 0, 1, 0, 0, 0⟩
  | true, true => ⟨0, 0, 0, 1, 0, 0⟩

def callM : Bool → Bool → Mono × KS := fun a b => (monoU a b, k1)

def adjM : Bool → Bool → Mono × KS
  | false, false => (monoU true true, k1)
  | false, true => (monoU false true, km1)
  | true, false => (monoU true false, km1)
  | true, true => (monoU false false, k1)

def cgTwoS (a b c : Fin 7) : List GS :=
  [.cx [(a,true),(b,true)] c, .cx [(b,true)] a, .cg [(c,false)] b rotP2 .i2,
   .cg [(a,false),(c,false)] b rotP2 .i2, .cx [(b,false)] a, .sw [] a b, .sw [] b c]

def cgThreeS (a b c d : Fin 7) : List GS :=
  [.cx [(a,false)] c, .cx [(c,true),(d,true)] b, .cx [(d,true)] c, .cx [(b,true)] c,
   .cg [(b,false)] d rotPi .one, .cg [(a,true),(b,false),(c,true)] d rotMT .i3,
   .cg [(a,true),(b,true),(c,true)] d rotT .i3, .cx [(d,true)] a, .cx [] a, .sw [] b c,
   .cx [] b, .cx [(a,true)] b, .sw [(a,true)] b c, .cx [(a,true),(b,true)] c]

def adjS : GS → GS
  | .cg cs t A s => .cg cs t (fun a b => A b a) s
  | g => g

def V1S : List GS :=
  [.sw [] 2 5] ++ cgTwoS 0 1 2 ++ [.cx [(0,true)] 6] ++ ((cgThreeS 3 4 5 6).map adjS).reverse ++
  [.sw [] 3 6, .sw [] 1 3]

def V2S : List GS :=
  [.sw [] 1 3] ++ cgThreeS 0 1 2 3 ++ [.sw [] 4 6, .cx [(4,true)] 3, .sw [] 5 6] ++
  ((cgTwoS 4 5 6).map adjS).reverse ++ [.sw [] 2 4, .sw [] 1 5, .sw [] 0 4]

def callS (q : Fin 7) : GS := .cg [] q callM .one

def iterS : List GS := [callS 1] ++ V1S ++ [callS 1] ++ V2S

def phiM (b : Bool) : Mono := if b then ⟨0, 0, 0, 0, 0, 1⟩ else ⟨0, 0, 0, 0, 1, 0⟩

/-- `√2 · (inputEmbedding *ᵥ φ)` -/
def vL : List Tm :=
  [⟨4, phiM false, k1⟩, ⟨2, phiM false, km1⟩, ⟨5, phiM true, k1⟩, ⟨3, phiM true, km1⟩]
/-- `√2 · (swappedEmbedding *ᵥ φ)` -/
def wL : List Tm :=
  [⟨2, phiM false, k1⟩, ⟨1, phiM false, km1⟩, ⟨6, phiM true, k1⟩, ⟨5, phiM true, km1⟩]

def detL : List (Mono × KS) := [(⟨1, 0, 0, 1, 0, 0⟩, k1), (⟨0, 1, 1, 0, 0, 0⟩, km1)]

def mulDet (L : List Tm) : List Tm :=
  L.flatMap fun t => detL.map fun p => ⟨t.idx, t.mo.mul p.1, t.co.mul p.2⟩

/-! ### Glue: matrices of the definitions as gate lists -/

lemma chron_singleton (g : Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ) :
    P24.chronological [g] = g := by
  rw [chron_cons, chron_nil, Matrix.one_mul]

lemma chron_flatten (LL : List (List (Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ))) :
    P24.chronological (LL.map P24.chronological) = P24.chronological LL.flatten := by
  induction LL with
  | nil => rfl
  | cons l LL ih => rw [List.map_cons, chron_cons, ih, List.flatten_cons, chron_append]

lemma chron_conjT (l : List (Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ)) :
    (P24.chronological l)ᴴ = P24.chronological ((l.map Matrix.conjTranspose).reverse) := by
  induction l with
  | nil => simp [chron_nil]
  | cons g l ih =>
    rw [chron_cons, Matrix.conjTranspose_mul, ih, List.map_cons, List.reverse_cons, chron_append,
      chron_singleton]

lemma cg_conjT (cs : List (Fin 7 × Bool)) (t : Fin 7) (A : Matrix Bool Bool ℂ)
    (h : ∀ p ∈ cs, p.1 ≠ t) : (P24.controlledGate cs t A)ᴴ = P24.controlledGate cs t Aᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, P24.controlledGate]
  by_cases hxy : ∀ i, i ≠ t → x i = y i
  · have hyx : ∀ i, i ≠ t → y i = x i := fun i hi => (hxy i hi).symm
    have hc : (∀ c ∈ cs, x c.1 = c.2) ↔ (∀ c ∈ cs, y c.1 = c.2) := by
      constructor
      · intro H c hc; rw [← hxy c.1 (h c hc)]; exact H c hc
      · intro H c hc; rw [hxy c.1 (h c hc)]; exact H c hc
    rw [if_pos hyx, if_pos hxy]
    by_cases hcy : ∀ c ∈ cs, y c.1 = c.2
    · rw [if_pos (hc.mpr hcy), if_pos hcy]
    · rw [if_neg (fun H => hcy (hc.mp H)), if_neg hcy]
      by_cases e : x t = y t
      · rw [if_pos e.symm, if_pos e, star_one]
      · rw [if_neg (fun e' => e e'.symm), if_neg e, star_zero]
  · rw [if_neg (fun H => hxy (fun i hi => (H i hi).symm)), if_neg hxy, star_zero]

lemma sw_conjT (cs : List (Fin 7 × Bool)) (a b : Fin 7) (hab : a ≠ b)
    (h : ∀ p ∈ cs, p.1 ≠ a ∧ p.1 ≠ b) :
    (P24.sevenControlledSwap cs a b)ᴴ = P24.sevenControlledSwap cs a b := by
  have hctrl : ∀ z : Fin 7 → Bool, (∀ c ∈ cs,
      (Function.update (Function.update z a (z b)) b (z a)) c.1 = c.2) ↔ (∀ c ∈ cs, z c.1 = c.2) := by
    intro z
    refine forall₂_congr (fun c hc => ?_)
    rw [Function.update_of_ne (h c hc).2, Function.update_of_ne (h c hc).1]
  have hss : ∀ z : Fin 7 → Bool, Function.update (Function.update
      (Function.update (Function.update z a (z b)) b (z a)) a
      ((Function.update (Function.update z a (z b)) b (z a)) b)) b
      ((Function.update (Function.update z a (z b)) b (z a)) a) = z := by
    intro z; funext i
    by_cases hia : i = a
    · subst hia; simp [Function.update_apply, hab]
    · by_cases hib : i = b
      · subst hib; simp [Function.update_apply, hab, Ne.symm hab]
      · simp [Function.update_apply, hia, hib]
  ext x y
  simp only [Matrix.conjTranspose_apply, P24.sevenControlledSwap]
  by_cases hx : ∀ c ∈ cs, x c.1 = c.2 <;> by_cases hy : ∀ c ∈ cs, y c.1 = c.2
  · rw [if_pos hx, if_pos hy]
    by_cases e : y = Function.update (Function.update x a (x b)) b (x a)
    · rw [if_pos e, if_pos (by rw [e, hss]), star_one]
    · rw [if_neg e, if_neg (by intro e'; apply e; rw [e', hss]), star_zero]
  · rw [if_pos hx, if_neg hy, if_neg (by intro e; apply hy; rw [e, hctrl]; exact hx),
      if_neg (by intro e; apply hy; rw [← e]; exact hx), star_zero]
  · rw [if_neg hx, if_pos hy, if_neg (by intro e; apply hx; rw [← e]; exact hy),
      if_neg (by intro e; apply hx; rw [e, hctrl]; exact hy), star_zero]
  · rw [if_neg hx, if_neg hy]
    by_cases e : x = y
    · rw [if_pos e.symm, if_pos e, star_one]
    · rw [if_neg (fun e' => e e'.symm), if_neg e, star_zero]

lemma bitFlip_conjT : P24.bitFlipᴴ = P24.bitFlip := by
  ext a b; cases a <;> cases b <;> simp [P24.bitFlip, Matrix.conjTranspose_apply]

def adjOK : GS → Bool
  | .cg cs t A _ => cs.all (fun p => !decide (p.1 = t)) &&
      decide ((A false false).1 = Mono.one) && decide ((A false true).1 = Mono.one) &&
      decide ((A true false).1 = Mono.one) && decide ((A true true).1 = Mono.one)
  | .cx cs t => cs.all (fun p => !decide (p.1 = t))
  | .sw cs a b => !decide (a = b) && cs.all (fun p => !decide (p.1 = a) && !decide (p.1 = b))

lemma star_scal (e : ℕ × ℕ) : star (scal e) = scal e := by
  simp [scal, star_r2, star_r3]

lemma denote_adj (g : GS) (h : adjOK g = true) : (denote U φ g)ᴴ = denote U φ (adjS g) := by
  cases g with
  | cg cs t A s =>
    simp only [adjOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, h4⟩ := h
    simp only [denote, adjS]
    rw [cg_conjT cs t _ hc]
    congr 1
    ext a b
    have hm : ∀ a b, (A a b).1 = Mono.one := by
      intro a b; cases a <;> cases b <;> assumption
    simp [Matrix.conjTranspose_apply, evM, hm, star_scal, KS.star_toC]
  | cx cs t =>
    simp only [adjOK, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp only [denote, adjS]
    rw [cg_conjT cs t _ h, bitFlip_conjT]
  | sw cs a b =>
    simp only [adjOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.not_eq_true'] at h
    obtain ⟨hab, hc⟩ := h
    simp only [denote, adjS]
    refine sw_conjT cs a b hab (fun p hp => ?_)
    exact hc p hp

lemma chron_adj (gs : List GS) (h : gs.all adjOK = true) :
    (P24.chronological (gs.map (denote U φ)))ᴴ =
      P24.chronological (((gs.map adjS).reverse).map (denote U φ)) := by
  rw [chron_conjT, List.map_map, List.map_reverse, List.map_map]
  congr 2
  apply List.map_congr_left
  intro g hg
  exact denote_adj U φ g (List.all_eq_true.mp h g hg)

/-! ### Rotations -/

lemma inv_r2 : r2⁻¹ = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  apply inv_eq_of_mul_eq_one_right
  have e : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = r2 / 2 := by simp [r2]
  rw [e]; linear_combination r2_sq / 2

lemma rotP2_eq : scal Sc.i2.e • evM U φ rotP2 = P24.rotationY (Real.pi / 2) := by
  ext a b
  simp only [P24.rotationY, show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four,
    Real.sin_pi_div_four, ← inv_r2]
  cases a <;> cases b <;> simp [evM, rotP2, scal, Sc.e]

lemma rotPi_eq : scal Sc.one.e • evM U φ rotPi = P24.rotationY Real.pi := by
  ext a b
  simp only [P24.rotationY, Real.cos_pi_div_two, Real.sin_pi_div_two]
  cases a <;> cases b <;> simp [evM, rotPi, scal, Sc.e]

lemma theta_cos : Real.cos (2 * Real.arccos (Real.sqrt (2 / 3 : ℝ)) / 2) =
    Real.sqrt 2 / Real.sqrt 3 := by
  rw [show 2 * Real.arccos (Real.sqrt (2 / 3 : ℝ)) / 2 = Real.arccos (Real.sqrt (2 / 3 : ℝ)) by ring]
  rw [Real.cos_arccos (by have := Real.sqrt_nonneg (2 / 3 : ℝ); linarith) (by
    rw [Real.sqrt_le_one]; norm_num), Real.sqrt_div (by norm_num)]

lemma theta_sin : Real.sin (2 * Real.arccos (Real.sqrt (2 / 3 : ℝ)) / 2) = 1 / Real.sqrt 3 := by
  rw [show 2 * Real.arccos (Real.sqrt (2 / 3 : ℝ)) / 2 = Real.arccos (Real.sqrt (2 / 3 : ℝ)) by ring]
  rw [Real.sin_arccos, Real.sq_sqrt (by norm_num)]
  rw [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num, Real.sqrt_div (by norm_num), Real.sqrt_one]

lemma rotT_eq : scal Sc.i3.e • evM U φ rotT =
    P24.rotationY (2 * Real.arccos (Real.sqrt (2 / 3 : ℝ))) := by
  ext a b
  simp only [P24.rotationY, theta_cos, theta_sin]
  cases a <;> cases b <;> simp [evM, rotT, scal, Sc.e, r2, r3] <;> ring

lemma rotMT_eq : scal Sc.i3.e • evM U φ rotMT =
    P24.rotationY (-(2 * Real.arccos (Real.sqrt (2 / 3 : ℝ)))) := by
  ext a b
  simp only [P24.rotationY, neg_div, Real.cos_neg, Real.sin_neg, theta_cos, theta_sin]
  cases a <;> cases b <;> simp [evM, rotMT, scal, Sc.e, r2, r3] <;> ring

lemma cgTwo_eq (a b c : Fin 7) :
    P24.cgTwo a b c = P24.chronological ((cgTwoS a b c).map (denote U φ)) := by
  simp only [P24.cgTwo, cgTwoS, List.map_cons, List.map_nil, denote, rotP2_eq]

lemma cgThree_eq (a b c d : Fin 7) :
    P24.cgThree a b c d = P24.chronological ((cgThreeS a b c d).map (denote U φ)) := by
  simp only [P24.cgThree, cgThreeS, List.map_cons, List.map_nil, denote, rotP2_eq, rotPi_eq,
    rotT_eq, rotMT_eq]

lemma firstKnown_eq : P24.firstKnown = P24.chronological (V1S.map (denote U φ)) := by
  have e : V1S.map (denote U φ) = ([[denote U φ (.sw [] 2 5)], (cgTwoS 0 1 2).map (denote U φ),
      [denote U φ (.cx [(0,true)] 6)], (((cgThreeS 3 4 5 6).map adjS).reverse).map (denote U φ),
      [denote U φ (.sw [] 3 6)], [denote U φ (.sw [] 1 3)]]).flatten := by
    simp [V1S]
  rw [e, ← chron_flatten]
  simp only [List.map_cons, List.map_nil]
  rw [← chron_adj U φ _ (by decide), ← cgThree_eq, ← cgTwo_eq]
  simp only [chron_singleton, P24.firstKnown, denote]

lemma secondKnown_eq : P24.secondKnown = P24.chronological (V2S.map (denote U φ)) := by
  have e : V2S.map (denote U φ) = ([[denote U φ (.sw [] 1 3)], (cgThreeS 0 1 2 3).map (denote U φ),
      [denote U φ (.sw [] 4 6)], [denote U φ (.cx [(4,true)] 3)], [denote U φ (.sw [] 5 6)],
      (((cgTwoS 4 5 6).map adjS).reverse).map (denote U φ),
      [denote U φ (.sw [] 2 4)], [denote U φ (.sw [] 1 5)], [denote U φ (.sw [] 0 4)]]).flatten := by
    simp [V2S]
  rw [e, ← chron_flatten]
  simp only [List.map_cons, List.map_nil]
  rw [← chron_adj U φ _ (by decide), ← cgThree_eq, ← cgTwo_eq]
  simp only [chron_singleton, P24.secondKnown, denote]

/-! ### `SU(2)` facts -/

lemma det_bool (A : Matrix Bool Bool ℂ) :
    A.det = A false false * A true true - A false true * A true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm A, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, finTwoEquiv]

lemma su2_facts (V : P24.QubitSU) :
    star (V.val false false) = V.val true true ∧ star (V.val true false) = -V.val false true ∧
    star (V.val false true) = -V.val true false ∧ star (V.val true true) = V.val false false ∧
    V.val false false * V.val true true - V.val false true * V.val true false = 1 := by
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp V.prop
  have hu' := Matrix.mem_unitaryGroup_iff'.mp hu
  have e : ∀ i j, (star V.val * V.val) i j = (1 : Matrix Bool Bool ℂ) i j := fun i j => by rw [hu']
  have h11 := e false false
  have h12 := e false true
  have h21 := e true false
  have h22 := e true true
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show false ≠ true by decide),
    Matrix.one_apply_ne (show true ≠ false by decide)] at h11 h12 h21 h22
  have hd := hdet
  rw [det_bool] at hd
  refine ⟨?_, ?_, ?_, ?_, hd⟩
  · linear_combination (-(star (V.val false false))) * hd + V.val true true * h11 -
      V.val true false * h12
  · linear_combination (-(star (V.val true false))) * hd + V.val false false * h12 -
      V.val false true * h11
  · linear_combination (-(star (V.val false true))) * hd + V.val true true * h21 -
      V.val true false * h22
  · linear_combination (-(star (V.val true true))) * hd + V.val false false * h22 -
      V.val false true * h21

lemma callM_eq (A : Matrix Bool Bool ℂ) : scal Sc.one.e • evM A φ callM = A := by
  ext a b; cases a <;> cases b <;> simp [evM, callM, monoU, Mono.ev, scal, Sc.e]

lemma adjM_eq (V : P24.QubitSU) : scal Sc.one.e • evM V.val φ adjM = V.valᴴ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := su2_facts V
  ext a b; cases a <;> cases b <;> simp [evM, adjM, monoU, Mono.ev, scal, Sc.e,
    Matrix.conjTranspose_apply, h1, h2, h3, h4]

lemma denote_call (A : Matrix Bool Bool ℂ) (q : Fin 7) :
    denote A φ (callS q) = P24.controlledGate [] q A := by
  simp only [denote, callS, callM_eq]

lemma denote_adjcall (V : P24.QubitSU) (q : Fin 7) :
    denote V.val φ (.cg [] q adjM .one) = (P24.controlledGate [] q V.val)ᴴ := by
  rw [cg_conjT _ _ _ (by simp)]
  simp only [denote, adjM_eq]

lemma interp_mulDet (L : List Tm) :
    interp U φ (mulDet L) = (U false false * U true true - U false true * U true false) •
      interp U φ L := by
  induction L with
  | nil => simp [mulDet]
  | cons t L ih =>
    simp only [mulDet, List.flatMap_cons, interp_append] at ih ⊢
    rw [ih, interp_cons U φ t L, smul_add]
    congr 1
    funext x
    simp only [detL, List.map_cons, List.map_nil, interp_cons, interp_nil, add_zero, Pi.add_apply,
      Pi.single_apply, Pi.smul_apply, smul_eq_mul, tval, KS.toC_mul, ev_mul]
    split_ifs
    · simp [Mono.ev]; ring
    · simp

/-! ### Embeddings -/

lemma toSeven_inj {n m : Fin 128} (h : toSeven n = toSeven m) : n = m := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 7
  · exact congrFun h ⟨i, hi⟩
  · have h1 : n.val < 2 ^ i := lt_of_lt_of_le n.isLt (by
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : m.val < 2 ^ i := lt_of_lt_of_le m.isLt (by
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

lemma toSeven_inj_iff (n m : Fin 128) : toSeven n = toSeven m ↔ n = m :=
  ⟨toSeven_inj, fun h => h ▸ rfl⟩

lemma toSeven_surj (x : Fin 7 → Bool) : ∃ n, toSeven n = x := by
  have hb : Function.Bijective toSeven :=
    (Fintype.bijective_iff_injective_and_card toSeven).mpr ⟨fun _ _ h => toSeven_inj h, by simp⟩
  exact hb.2 x

lemma small_of_rest : ∀ n : Fin 128, (∀ i : Fin 7, 3 ≤ i.val → getB n i = false) → n.val < 8 := by
  decide

lemma rest_of_small : ∀ k : Fin 128, k.val < 8 → ∀ i : Fin 7, 3 ≤ i.val → toSeven k i = false := by
  decide

lemma interp_small_zero (L : List Tm) (hL : L.all (fun t => decide (t.idx.val < 8)) = true)
    (n : Fin 128) (hn : ¬ n.val < 8) : interp U φ L (toSeven n) = 0 := by
  simp only [interp]
  apply List.sum_eq_zero
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨t, ht, rfl⟩ := hc
  rw [if_neg]
  intro e
  have := List.all_eq_true.mp hL t ht
  rw [toSeven_inj e] at hn
  simp at this
  exact hn this

lemma interp_toSeven (L : List Tm) (n : Fin 128) :
    interp U φ L (toSeven n) = (L.map fun t => if n = t.idx then tval U φ t else 0).sum := by
  simp only [interp, toSeven_inj_iff]

lemma inputEmb_apply (x : Fin 7 → Bool) : (P24.inputEmbedding *ᵥ φ) x =
    if (∀ i : Fin 7, 3 ≤ i.val → x i = false) then P24.sourceSinglet (x 1) (x 2) * φ (x 0)
    else 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool, P24.inputEmbedding]
  by_cases hr : ∀ i : Fin 7, 3 ≤ i.val → x i = false
  · cases h0 : x 0 <;> simp [hr]
  · simp [hr]

lemma swappedEmb_apply (x : Fin 7 → Bool) : (P24.swappedEmbedding *ᵥ φ) x =
    if (∀ i : Fin 7, 3 ≤ i.val → x i = false) then P24.sourceSinglet (x 0) (x 1) * φ (x 2)
    else 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool, P24.swappedEmbedding]
  by_cases hr : ∀ i : Fin 7, 3 ≤ i.val → x i = false
  · cases h0 : x 2 <;> simp [hr]
  · simp [hr]

/-- generic embedding check: a function supported on the first three wires. -/
lemma emb_eq (f : (Fin 7 → Bool) → ℂ) (L : List Tm) (c : ℂ)
    (hL : L.all (fun t => decide (t.idx.val < 8)) = true)
    (hf : ∀ x, ¬ (∀ i : Fin 7, 3 ≤ i.val → x i = false) → f x = 0)
    (hsmall : ∀ k : Fin 128, k.val < 8 → f (toSeven k) = c * interp U φ L (toSeven k)) :
    f = c • interp U φ L := by
  funext x
  obtain ⟨n, rfl⟩ := toSeven_surj x
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hr : ∀ i : Fin 7, 3 ≤ i.val → getB n i = false
  · exact hsmall n (small_of_rest n hr)
  · rw [hf _ (by simpa [toSeven] using hr)]
    rw [interp_small_zero U φ L hL n (fun h => hr ?_), mul_zero]
    intro i hi
    have := small_of_rest
    revert i
    revert h
    revert n
    decide

lemma inputEmb_eq : P24.inputEmbedding *ᵥ φ = scal (1, 0) • interp U φ vL := by
  refine emb_eq U φ _ _ _ (by decide) (fun x hx => by rw [inputEmb_apply, if_neg hx]) ?_
  intro k hk
  rw [inputEmb_apply, if_pos (rest_of_small k hk), interp_toSeven]
  obtain ⟨k, hk'⟩ := k
  simp only at hk
  interval_cases k <;>
    simp [toSeven, getB, Nat.testBit, P24.sourceSinglet,
      QAlgorithms.Papers.Independent.Frontier18.P14.singlet, vL, tval, phiM, Mono.ev, scal, r2, Fin.ext_iff]

lemma swappedEmb_eq : P24.swappedEmbedding *ᵥ φ = scal (1, 0) • interp U φ wL := by
  refine emb_eq U φ _ _ _ (by decide) (fun x hx => by rw [swappedEmb_apply, if_neg hx]) ?_
  intro k hk
  rw [swappedEmb_apply, if_pos (rest_of_small k hk), interp_toSeven]
  obtain ⟨k, hk'⟩ := k
  simp only at hk
  interval_cases k <;>
    simp [toSeven, getB, Nat.testBit, P24.sourceSinglet,
      QAlgorithms.Papers.Independent.Frontier18.P14.singlet, wL, tval, phiM, Mono.ev, scal, r2, Fin.ext_iff]

/-! ### Unitarity of the fixed blocks -/

lemma single_eq_interp (n : Fin 128) :
    Pi.single (toSeven n) (1 : ℂ) = interp U φ [⟨n, Mono.one, k1⟩] := by
  rw [interp_cons, interp_nil, add_zero]
  simp [tval]

lemma eq_one_of_basis (M : Matrix (Fin 7 → Bool) (Fin 7 → Bool) ℂ)
    (h : ∀ n : Fin 128, M *ᵥ Pi.single (toSeven n) 1 = Pi.single (toSeven n) 1) : M = 1 := by
  ext x y
  obtain ⟨n, rfl⟩ := toSeven_surj y
  have := congrFun (h n) x
  rw [Matrix.mulVec_single] at this
  simp only [Pi.smul_apply, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    mul_one] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

lemma chron_eq_one_of_check (gs : List GS)
    (h : ∀ n : Fin 128, eqCheck (scaleL (pw (0, 0)) (run gs [⟨n, Mono.one, k1⟩]))
      (scaleL (pw (runE gs)) [⟨n, Mono.one, k1⟩]) = true) :
    P24.chronological (gs.map (denote U φ)) = 1 := by
  apply eq_one_of_basis
  intro n
  rw [single_eq_interp U φ, run_correct, final_eq U φ (runE gs) (0, 0) _ _ (h n)]
  simp [scal]

lemma unitary_check1 : ∀ n : Fin 128,
    eqCheck (scaleL (pw (0, 0)) (run (V1S ++ (V1S.map adjS).reverse) [⟨n, Mono.one, k1⟩]))
      (scaleL (pw (runE (V1S ++ (V1S.map adjS).reverse))) [⟨n, Mono.one, k1⟩]) = true := by
  decide +kernel

lemma unitary_check2 : ∀ n : Fin 128,
    eqCheck (scaleL (pw (0, 0)) (run (V2S ++ (V2S.map adjS).reverse) [⟨n, Mono.one, k1⟩]))
      (scaleL (pw (runE (V2S ++ (V2S.map adjS).reverse))) [⟨n, Mono.one, k1⟩]) = true := by
  decide +kernel

lemma firstKnown_unitary : star P24.firstKnown * P24.firstKnown = 1 := by
  rw [Matrix.star_eq_conjTranspose, firstKnown_eq 1 (fun _ => 0), chron_adj _ _ _ (by decide),
    ← chron_append, ← List.map_append]
  exact chron_eq_one_of_check _ _ _ unitary_check1

lemma secondKnown_unitary : star P24.secondKnown * P24.secondKnown = 1 := by
  rw [Matrix.star_eq_conjTranspose, secondKnown_eq 1 (fun _ => 0), chron_adj _ _ _ (by decide),
    ← chron_append, ← List.map_append]
  exact chron_eq_one_of_check _ _ _ unitary_check2

/-! ### Circuits -/

lemma iter_eq (V : P24.QubitSU) :
    P24.evaluateCalls P24.iteration V = P24.chronological (iterS.map (denote V.val φ)) := by
  have e : iterS.map (denote V.val φ) = [[denote V.val φ (callS 1)], V1S.map (denote V.val φ),
      [denote V.val φ (callS 1)], V2S.map (denote V.val φ)].flatten := by
    simp [iterS]
  simp only [P24.evaluateCalls, P24.iteration, List.map_cons, List.map_nil]
  rw [e, ← chron_flatten]
  simp only [List.map_cons, List.map_nil, chron_singleton, denote_call]
  rw [← firstKnown_eq, ← secondKnown_eq]

lemma eval_append (a b : List P24.CallGate) (V : P24.QubitSU) :
    P24.evaluateCalls (a ++ b) V = P24.evaluateCalls b V * P24.evaluateCalls a V := by
  simp only [P24.evaluateCalls, List.map_append, chron_append]

def fourS : List GS := iterS ++ iterS

lemma four_eq (V : P24.QubitSU) :
    P24.evaluateCalls P24.fourCircuit V = P24.chronological (fourS.map (denote V.val φ)) := by
  rw [P24.fourCircuit, eval_append, iter_eq, fourS, List.map_append, chron_append]

lemma runE_four : runE fourS = (8, 8) := by decide

/-! ### Output embedding -/

def outL : List Tm :=
  [⟨2, ⟨1, 0, 0, 1, 1, 0⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨3, ⟨0, 0, 1, 1, 1, 0⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨6, ⟨1, 0, 1, 0, 1, 0⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨7, ⟨0, 0, 2, 0, 1, 0⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨0, ⟨0, 1, 0, 1, 1, 0⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨1, ⟨0, 0, 0, 2, 1, 0⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨4, ⟨0, 1, 1, 0, 1, 0⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨5, ⟨0, 0, 1, 1, 1, 0⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨2, ⟨1, 1, 0, 0, 0, 1⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨3, ⟨0, 1, 1, 0, 0, 1⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨6, ⟨2, 0, 0, 0, 0, 1⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨7, ⟨1, 0, 1, 0, 0, 1⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨0, ⟨0, 2, 0, 0, 0, 1⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨1, ⟨0, 1, 0, 1, 0, 1⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩,
  ⟨4, ⟨1, 1, 0, 0, 0, 1⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩,
  ⟨5, ⟨1, 0, 0, 1, 0, 1⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩]

lemma outEmb_apply (V : P24.QubitSU) (x : Fin 7 → Bool) :
    ((P24.outputEmbedding V * V.valᴴ) *ᵥ φ) x =
    if (∀ i : Fin 7, 3 ≤ i.val → x i = false) then
      P24.catalyst V (x 0) (x 1) * (V.valᴴ *ᵥ φ) (x 2) else 0 := by
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool, P24.outputEmbedding]
  by_cases hr : ∀ i : Fin 7, 3 ≤ i.val → x i = false
  · cases h0 : x 2 <;> simp [hr, Matrix.mulVec, dotProduct]
  · simp [hr]

lemma outEmb_eq (V : P24.QubitSU) :
    (P24.outputEmbedding V * V.valᴴ) *ᵥ φ = scal (1, 0) • interp V.val φ outL := by
  obtain ⟨h1, h2, h3, h4, -⟩ := su2_facts V
  have g1 : (starRingEnd ℂ) (V.val false false) = V.val true true := h1
  have g2 : (starRingEnd ℂ) (V.val true false) = -V.val false true := h2
  have g3 : (starRingEnd ℂ) (V.val false true) = -V.val true false := h3
  have g4 : (starRingEnd ℂ) (V.val true true) = V.val false false := h4
  refine emb_eq V.val φ _ _ _ (by decide) (fun x hx => by rw [outEmb_apply, if_neg hx]) ?_
  intro k hk
  rw [outEmb_apply, if_pos (rest_of_small k hk), interp_toSeven]
  obtain ⟨k, hk'⟩ := k
  simp only at hk
  interval_cases k <;>
    simp [toSeven, getB, Nat.testBit, P24.catalyst, P24.sourceSinglet, Fintype.sum_bool,
      QAlgorithms.Papers.Independent.Frontier18.P14.singlet, outL, tval, Mono.ev, scal, r2,
      Fin.ext_iff, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, h1, h2, h3, h4,
      g1, g2, g3, g4, KS.toC, KN.toC] <;> ring

lemma check2 : eqCheck (scaleL (pw (1, 0)) (run fourS vL))
    (scaleL (pw (9, 8)) (mulDet (negL outL))) = true := by decide +kernel

lemma scal_19 : scal (1, 0) * scal (8, 8) = scal (9, 8) := by
  simp only [scal]; ring

lemma physical_iteration : P24.PhysicalCalls P24.iteration := by
  intro gate hg
  simp only [P24.iteration, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · trivial
  · exact Matrix.mem_unitaryGroup_iff'.mpr firstKnown_unitary
  · trivial
  · exact Matrix.mem_unitaryGroup_iff'.mpr secondKnown_unitary

lemma physical_append (a b : List P24.CallGate) (ha : P24.PhysicalCalls a)
    (hb : P24.PhysicalCalls b) : P24.PhysicalCalls (a ++ b) := by
  intro gate hg
  rcases List.mem_append.mp hg with h | h
  · exact ha gate h
  · exact hb gate h

lemma physical_four : P24.PhysicalCalls P24.fourCircuit :=
  physical_append _ _ physical_iteration physical_iteration

lemma calls_four : P24.calls P24.fourCircuit = 4 := by
  norm_num [P24.calls, P24.fourCircuit, P24.iteration]

lemma four_output (V : P24.QubitSU) :
    (P24.evaluateCalls P24.fourCircuit V) *ᵥ (P24.inputEmbedding *ᵥ φ) =
      -((P24.outputEmbedding V * V.valᴴ) *ᵥ φ) := by
  have hdet := (su2_facts V).2.2.2.2
  rw [four_eq φ V, inputEmb_eq V.val φ, Matrix.mulVec_smul, run_correct, smul_smul, runE_four,
    scal_19, final_eq _ _ (9, 8) (1, 0) _ _ check2, interp_mulDet, hdet, one_smul, interp_negL,
    outEmb_eq φ V, smul_neg]

/-! ### Matrix-level consequences -/

lemma mat_ext_mulVec (M₁ M₂ : Matrix (Fin 7 → Bool) Bool ℂ) (h : ∀ ψ, M₁ *ᵥ ψ = M₂ *ᵥ ψ) :
    M₁ = M₂ := by
  ext x b
  have := congrFun (h (Pi.single b 1)) x
  simpa [Matrix.mulVec_single] using this

lemma conjSuperop_neg (X : Matrix (Fin 7 → Bool) Bool ℂ) (A : Matrix Bool Bool ℂ) :
    conjSuperop (-X) A = conjSuperop X A := by
  simp [conjSuperop, Matrix.conjTranspose_neg]

lemma call_mulVec (V : Matrix Bool Bool ℂ) (L : List Tm) :
    P24.controlledGate [] 1 V *ᵥ interp V φ L = interp V φ (run [callS 1] L) := by
  have := run_correct V φ [callS 1] L
  rw [List.map_cons, List.map_nil, chron_singleton, denote_call] at this
  rw [this]
  have : runE [callS 1] = (0, 0) := rfl
  rw [this]
  simp [scal]

lemma four_matrix (V : P24.QubitSU) :
    P24.evaluateCalls P24.fourCircuit V * P24.inputEmbedding = -(P24.outputEmbedding V * V.valᴴ) := by
  apply mat_ext_mulVec
  intro ψ
  rw [← Matrix.mulVec_mulVec, four_output ψ V, Matrix.neg_mulVec]

/-! ### Target: deterministic exact four calls -/

lemma toSeven_bij : Function.Bijective toSeven :=
  (Fintype.bijective_iff_injective_and_card toSeven).mpr ⟨fun _ _ h => toSeven_inj h, by simp⟩

lemma small4 : ∀ n : Fin 128, n.val < 4 →
    (toSeven n 2 = false ∧ ∀ i : Fin 7, 3 ≤ i.val → toSeven n i = false) := by decide

lemma lt4_of : ∀ n : Fin 128,
    (toSeven n 2 = false ∧ ∀ i : Fin 7, 3 ≤ i.val → toSeven n i = false) → n.val < 4 := by
  decide

lemma O_entry (V : P24.QubitSU) (env : Fin 7 → Bool) (a c : Bool) :
    P24.outputEmbedding V (Function.update env 2 a) c =
      if a = c ∧ (∀ i : Fin 7, 3 ≤ i.val → env i = false) then P24.catalyst V (env 0) (env 1)
      else 0 := by
  have hR : (∀ i : Fin 7, 3 ≤ i.val → Function.update env 2 a i = false) ↔
      (∀ i : Fin 7, 3 ≤ i.val → env i = false) := by
    refine forall₂_congr (fun i hi => ?_)
    rw [Function.update_of_ne (by intro h; subst h; simp at hi)]
  simp only [P24.outputEmbedding, Function.update_self, hR,
    Function.update_of_ne (show (0 : Fin 7) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 7) ≠ 2 by decide)]

lemma O_pos (V : P24.QubitSU) (env : Fin 7 → Bool) (a c : Bool)
    (hR : ∀ i : Fin 7, 3 ≤ i.val → env i = false) :
    P24.outputEmbedding V (Function.update env 2 a) c =
      if a = c then P24.catalyst V (env 0) (env 1) else 0 := by
  rw [O_entry]
  by_cases h : a = c
  · rw [if_pos ⟨h, hR⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma O_neg (V : P24.QubitSU) (env : Fin 7 → Bool) (a c : Bool)
    (hR : ¬ ∀ i : Fin 7, 3 ≤ i.val → env i = false) :
    P24.outputEmbedding V (Function.update env 2 a) c = 0 := by
  rw [O_entry, if_neg (fun h' => hR h'.2)]

lemma discard_O (V : P24.QubitSU) (B : Matrix Bool Bool ℂ) :
    P24.discardExcept 2 (P24.outputEmbedding V * B * (P24.outputEmbedding V)ᴴ) = B := by
  obtain ⟨hu, -⟩ := Matrix.mem_specialUnitaryGroup_iff.mp V.prop
  have hu' := Matrix.mem_unitaryGroup_iff'.mp hu
  have e : ∀ i j, (star V.val * V.val) i j = (1 : Matrix Bool Bool ℂ) i j := fun i j => by rw [hu']
  have h11 := e false false
  have h22 := e true true
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply_eq] at h11 h22
  ext a b
  simp only [P24.discardExcept]
  have key : ∀ env : Fin 7 → Bool,
      (if env 2 = false then (P24.outputEmbedding V * B * (P24.outputEmbedding V)ᴴ)
        (Function.update env 2 a) (Function.update env 2 b) else 0) =
      if (env 2 = false ∧ ∀ i : Fin 7, 3 ≤ i.val → env i = false) then
        star (P24.catalyst V (env 0) (env 1)) * P24.catalyst V (env 0) (env 1) * B a b
      else 0 := by
    intro env
    by_cases h2 : env 2 = false
    · by_cases hR : ∀ i : Fin 7, 3 ≤ i.val → env i = false
      · rw [if_pos h2, if_pos (And.intro h2 hR)]
        simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, O_pos V env _ _ hR]
        cases a <;> cases b <;> simp <;> ring
      · rw [if_pos h2, if_neg (fun h => hR h.2)]
        simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, O_neg V env _ _ hR]
    · simp [h2]
  rw [Finset.sum_congr rfl (fun env _ => key env), ← toSeven_bij.sum_comp]
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1, 2, 3} : Finset (Fin 128))) (by
    intro n _ hn
    rw [if_neg]
    intro h
    apply hn
    have := lt4_of n h
    obtain ⟨k, hk⟩ := n
    simp only at this
    interval_cases k <;> simp)]
  rw [Finset.sum_congr rfl (fun n hn => if_pos (small4 n (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide)))]
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1 / 2 := by
    have := r2_sq
    unfold r2 at this
    rw [inv_pow, this]
    norm_num
  have h11' : (starRingEnd ℂ) (V.val true false) * V.val true false +
      (starRingEnd ℂ) (V.val false false) * V.val false false = 1 := h11
  have h22' : (starRingEnd ℂ) (V.val true true) * V.val true true +
      (starRingEnd ℂ) (V.val false true) * V.val false true = 1 := h22
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [toSeven, getB, Nat.testBit, P24.catalyst, P24.sourceSinglet, Fintype.sum_bool,
    QAlgorithms.Papers.Independent.Frontier18.P14.singlet]
  linear_combination (B a b / 2) * (h11' + h22') + (B a b) * ((starRingEnd ℂ) (V.val false true) *
    V.val false true + (starRingEnd ℂ) (V.val true true) * V.val true true +
    (starRingEnd ℂ) (V.val false false) * V.val false false +
    (starRingEnd ℂ) (V.val true false) * V.val true false) * hs

lemma exact_four (V : P24.QubitSU) (A : Matrix Bool Bool ℂ) :
    P24.discardExcept 2 (conjSuperop (P24.evaluateCalls P24.fourCircuit V * P24.inputEmbedding) A) =
      conjSuperop V.valᴴ A := by
  rw [four_matrix, conjSuperop_neg]
  have : conjSuperop (P24.outputEmbedding V * V.valᴴ) A =
      P24.outputEmbedding V * conjSuperop V.valᴴ A * (P24.outputEmbedding V)ᴴ := by
    simp only [conjSuperop, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, discard_O]

end S190P24_aux

section
open QAlgorithms MeasureTheory
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

open QAlgorithms.Papers.Independent.Support50.P24 in
theorem solution :
    ∃ gates : List CallGate, PhysicalCalls gates ∧ calls gates = 4 ∧ ExactInverter gates := by
  refine ⟨fourCircuit, ?_, S190P24_aux.calls_four, fun U A => ?_⟩
  · convert S190P24_aux.physical_four
  · exact S190P24_aux.exact_four U A

end
