-- Prove2me | solution 1 for RandomInvolutions.tendsto_mul_expFixK_sub_first_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:49:29.034885+00:00
-- url     : https://prove2.me/submissions/4c4f538f-d9db-4edc-af34-1f465aec12d1

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_RandomInvolutions
import Theorems.Thm_BordenaveCollins_tendsto_expFix

section
/-!
# Strong convergence of uniform random involutions: definitions

Shared definitions for the proof of `ZigZagStrong.ZigZag.involution_strong_convergence`.
NEVER EDIT (the Blueprint and all Parts build on this file).

The group is `Γ_r = Z₂^{*r}`, in the encoding `BordenaveCollins.G 0 r` (no free generators, `r`
involutions `m_i = genL (Sum.inr i)`), so that the published Bordenave–Collins statements
(`exists_linearization`, `norm_sum_cfun_mul_trace_Bprod_le`, `tendsto_expFix`,
`tendsto_re_trTau_pow_rpow`) apply verbatim with `r := 0`, `s := r`.

* `homI τ : G 0 r →* Perm (Fin N)` for a tuple of involutions `τ`.
* The conditional model `OmK r N κ`: the `i`-th involution has exactly `κ i` fixed points;
  admissible sizes `AdmK N κ` (`κ i ≤ N`, `κ i ≡ N mod 2`), the filter `admF κ` of admissible
  sizes, the weight `lam κ = 1 + ∑ κ i`.
* Expected fixed points `expFixOn`, `expFixK`; the compressed model operator `perpOp`; the
  spectral functional `specE` of any finite family of representations.
* Colourings with loops of the closed path of a word, and their weights `wtF`, `wtK`.
* The coefficient counts `Bcount` (conjugates of `m_i`) and `C2count` (the two-loop shapes
  `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`).
* `toAlg`: a scalar `*`-polynomial as an element of the group algebra.
-/

open Finset BordenaveCollins

noncomputable section

namespace RandomInvolutions.Dev

/-! ## The group `Γ_r = G 0 r` and its words -/

/-- The inverse letter. -/
def bar {r s : ℕ} : Lt r s → Lt r s
  | Sum.inl (i, b) => Sum.inl (i, !b)
  | Sum.inr j => Sum.inr j

/-- A reduced word: no letter is followed by its inverse. -/
def Red {r s : ℕ} (u : List (Lt r s)) : Prop := u.IsChain (fun a b => b ≠ bar a)

/-- `u` is cyclically reduced: no letter is followed (cyclically) by its inverse. A one-letter
word `[m_j]` is not cyclically reduced in this sense; the empty word is. -/
def CycRed {r s : ℕ} (u : List (Lt r s)) : Prop :=
  ∀ t : Fin u.length,
    u.get ⟨(t.val + 1) % u.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ bar (u.get t)

/-! ## Involutions and the representation they define -/

/-- The permutation of a letter (the free letters `Sum.inl _` do not occur in `Lt 0 r`). -/
def letterPermI {r N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) :
    Lt 0 r → Equiv.Perm (Fin N)
  | Sum.inl _ => 1
  | Sum.inr i => (τ i).1

/-- The permutation of a word (product in the order the letters appear). -/
def wordPermI {r N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (u : List (Lt 0 r)) :
    Equiv.Perm (Fin N) :=
  (u.map (letterPermI τ)).prod

/-! ## The conditional model `M(N, κ)` -/

/-! ## Expected fixed points -/

/-! ## Operators -/

/-! ## Colourings with loops of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPermI τ (u.drop t) y`). Step `t` with letter `m_i` is a *loop* of colour `i` at
`x t` when `x t = x (t+1)` (that vertex is fixed by `τ_i`), and a *pair* `{x t, x (t+1)}` of
`τ_i` otherwise. -/

section Colour

variable {r : ℕ} (u : List (Lt 0 r))

/-- A finite set of unordered pairs is a partial matching: no loops, pairwise disjoint. -/
def PMat {α : Type*} (E : Finset (Sym2 α)) : Prop :=
  (∀ p ∈ E, ¬ p.IsDiag) ∧ ∀ p ∈ E, ∀ q ∈ E, (∃ a, a ∈ p ∧ a ∈ q) → p = q

/-- The vertices forced to be fixed points of `τ_i` (loops of colour `i`). -/
def Ls {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) : Finset α :=
  (univ.filter fun t : Fin u.length => u.get t = Sum.inr i ∧ x t.castSucc = x t.succ).image
    fun t => x t.castSucc

/-- The unordered pairs forced to be 2-cycles of `τ_i`. -/
def Ps {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) :
    Finset (Sym2 α) :=
  (univ.filter fun t : Fin u.length => u.get t = Sum.inr i ∧ x t.castSucc ≠ x t.succ).image
    fun t => s(x t.castSucc, x t.succ)

/-- A closed path consistent with involutions: under each colour the pairs form a partial
matching and no loop vertex lies on a pair. -/
def GoodL {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) : Prop :=
  (∀ i, PMat (Ps u x i)) ∧ (∀ i, ∀ a ∈ Ls u x i, ∀ p ∈ Ps u x i, a ∉ p) ∧
    x 0 = x (Fin.last _)

/-- The first position where `x` takes the value `x t`. -/
def canon {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

/-- The number of values of a path. -/
def nv {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) : ℕ := (univ.image x).card

/-- Canonical good colourings (with loops) of the closed path of `u`. -/
def CGL : Finset (Fin (u.length + 1) → Fin (u.length + 1)) := by
  classical exact (univ.filter fun c => canon c = c).filter (GoodL u)

/-- The number `e_i` of pairs of colour `i`. -/
def eK (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) : ℕ := (Ps u c i).card

/-- The number `f_i` of loops of colour `i`. -/
def fK (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) : ℕ := (Ls u c i).card

/-- `e = ∑ e_i`. -/
def Ecount (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℕ := ∑ i, eK u c i

/-- `f = ∑ f_i`. -/
def Fcount (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℕ := ∑ i, fK u c i

end Colour

/-- The weight of a colouring with `v` vertices, `e i` pairs and `f i` loops of colour `i`:
`[N]_v ∏_i [κ_i]_{f_i} ∏_{l < e_i} (N - κ_i - 2l) / [N]_{f_i + 2 e_i}`. The `i`-th factor is the
probability that an involution with `κ_i` fixed points fixes `f_i` given points and contains
`e_i` given disjoint pairs (on `f_i + 2 e_i` distinct points). -/
def wtF {r : ℕ} (N : ℕ) (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) : ℝ :=
  (N.descFactorial v : ℝ) *
    ∏ i, ((((κ i).descFactorial (f i) : ℝ) *
        ∏ l ∈ range (e i), ((N : ℝ) - κ i - 2 * l)) / (N.descFactorial (f i + 2 * e i) : ℝ))

/-- The weight of a colouring of `u`. -/
def wtK {r : ℕ} (u : List (Lt 0 r)) (N : ℕ) (κ : Fin r → ℕ)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ :=
  wtF N κ (nv c) (eK u c) (fK u c)

/-! ## The coefficient counts -/

/-! ## Scalar polynomials as group-algebra elements -/

end RandomInvolutions.Dev

end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-!
# Part F: normal forms in `Γ_r = G 0 r` and the coefficient counts on special elements
-/
/-! ## More words -/
theorem gid_self {H : Type*} [Group H] (x : H) : x = x * x * x⁻¹ := by group

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
/-!
# Part K2, analytic half: the expansion of the weights `wtF` in `1/N`
-/
lemma hd_prod {ι : Type*} (S : Finset ι) (g : ι → ℝ → ℝ) (d : ι → ℝ)
    (h1 : ∀ i ∈ S, g i 0 = 1) (hd : ∀ i ∈ S, HasDerivAt (g i) (d i) 0) :
    HasDerivAt (fun s => ∏ i ∈ S, g i s) (∑ i ∈ S, d i) 0 := by
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | insert a S ha ih =>
    have ih' := ih (fun i hi => h1 i (mem_insert_of_mem hi))
      (fun i hi => hd i (mem_insert_of_mem hi))
    have h := (hd a (mem_insert_self a S)).mul ih'
    have e1 : (fun s => ∏ i ∈ insert a S, g i s) = g a * fun s => ∏ i ∈ S, g i s := by
      funext s; simp [prod_insert ha]
    rw [e1, sum_insert ha]
    refine h.congr_deriv ?_
    rw [h1 a (mem_insert_self a S), prod_congr rfl (fun i hi => h1 i (mem_insert_of_mem hi))]
    simp

lemma hd_lin (a : ℝ) : HasDerivAt (fun s : ℝ => 1 - a * s) (-a) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_sub 1

/-- The correction factor of a weight, as a function of `s = 1/N`. -/
def Rf (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) (s : ℝ) : ℝ :=
  (∏ j ∈ range v, (1 - (j : ℝ) * s)) *
    ∏ i, ((∏ l ∈ range (e i), (1 - ((κ i : ℝ) + 2 * l) * s)) /
      ∏ j ∈ range (f i + 2 * e i), (1 - (j : ℝ) * s))

/-- The `κ`-free part of the derivative of `Rf` at `0`. -/
def c0f (v : ℕ) (e f : Fin r → ℕ) : ℝ :=
  -(∑ j ∈ range v, (j : ℝ)) +
    ∑ i, ((∑ j ∈ range (f i + 2 * e i), (j : ℝ)) - ∑ l ∈ range (e i), 2 * (l : ℝ))

lemma Rf_zero (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) : Rf κ v e f 0 = 1 := by
  simp [Rf]

lemma Rf_deriv (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) :
    HasDerivAt (Rf κ v e f) (c0f v e f - ∑ i, (e i : ℝ) * κ i) 0 := by
  have hP : HasDerivAt (fun s : ℝ => ∏ j ∈ range v, (1 - (j : ℝ) * s))
      (∑ j ∈ range v, -(j : ℝ)) 0 :=
    hd_prod _ _ _ (fun i _ => by simp) (fun i _ => hd_lin _)
  have hQ : ∀ i : Fin r, HasDerivAt
      (fun s : ℝ => (∏ l ∈ range (e i), (1 - ((κ i : ℝ) + 2 * l) * s)) /
        ∏ j ∈ range (f i + 2 * e i), (1 - (j : ℝ) * s))
      ((∑ l ∈ range (e i), -((κ i : ℝ) + 2 * l)) - ∑ j ∈ range (f i + 2 * e i), -(j : ℝ)) 0 := by
    intro i
    have hn : HasDerivAt (fun s : ℝ => ∏ l ∈ range (e i), (1 - ((κ i : ℝ) + 2 * l) * s))
        (∑ l ∈ range (e i), -((κ i : ℝ) + 2 * l)) 0 :=
      hd_prod _ _ _ (fun i _ => by simp) (fun i _ => hd_lin _)
    have hdn : HasDerivAt (fun s : ℝ => ∏ j ∈ range (f i + 2 * e i), (1 - (j : ℝ) * s))
        (∑ j ∈ range (f i + 2 * e i), -(j : ℝ)) 0 :=
      hd_prod _ _ _ (fun i _ => by simp) (fun i _ => hd_lin _)
    have h := hn.div hdn (by simp)
    refine h.congr_deriv ?_
    simp
  have hQQ := hd_prod (univ : Finset (Fin r)) _ _ (fun i _ => by simp) (fun i _ => hQ i)
  have h := hP.mul hQQ
  have e1 : Rf κ v e f = (fun s : ℝ => ∏ j ∈ range v, (1 - (j : ℝ) * s)) *
      fun s => ∏ i, ((∏ l ∈ range (e i), (1 - ((κ i : ℝ) + 2 * l) * s)) /
        ∏ j ∈ range (f i + 2 * e i), (1 - (j : ℝ) * s)) := by
    funext s; rfl
  rw [e1]
  refine h.congr_deriv ?_
  have h2 : ∀ i : Fin r, (∑ l ∈ range (e i), -((κ i : ℝ) + 2 * l)) =
      -((e i : ℝ) * κ i) - ∑ l ∈ range (e i), 2 * (l : ℝ) := by
    intro i
    simp [sum_add_distrib, sum_neg_distrib]
    ring
  simp only [h2, c0f, sum_neg_distrib, sum_sub_distrib, mul_zero, sub_zero, prod_const_one,
    div_one, mul_one, one_mul]
  ring

lemma cast_desc (N m : ℕ) (hN : 1 ≤ N) (hm : m ≤ N) :
    (N.descFactorial m : ℝ) = (N : ℝ) ^ m * ∏ j ∈ range m, (1 - (j : ℝ) * (1 / (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show (N : ℝ) ^ m = ∏ _j ∈ range m, (N : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj : j < m := mem_range.1 hj
  rw [Nat.cast_sub (by omega)]
  field_simp

lemma cast_pairs (N k e : ℕ) (hN : 1 ≤ N) :
    (∏ l ∈ range e, ((N : ℝ) - k - 2 * l)) =
      (N : ℝ) ^ e * ∏ l ∈ range e, (1 - ((k : ℝ) + 2 * l) * (1 / (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show (N : ℝ) ^ e = ∏ _j ∈ range e, (N : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  field_simp
  ring

lemma alg_fac (K a b Q D : ℝ) (ha : a ≠ 0) :
    K * (a * Q) / (a * b * D) = K * (Q / D) * b⁻¹ := by
  have ha' : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
  linear_combination (K * Q * b⁻¹ * D⁻¹) * ha'

lemma wtF_eq (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) (N : ℕ) (hN : 1 ≤ N) (hv : v ≤ N)
    (hm : ∀ i, f i + 2 * e i ≤ N) :
    wtF N κ v e f = (N : ℝ) ^ v * ((N : ℝ) ^ (∑ i, e i + ∑ i, f i))⁻¹ *
      (∏ i, ((κ i).descFactorial (f i) : ℝ)) * Rf κ v e f (1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold wtF Rf
  rw [cast_desc N v hN hv]
  have hfac : ∀ i : Fin r,
      (((κ i).descFactorial (f i) : ℝ) * ∏ l ∈ range (e i), ((N : ℝ) - κ i - 2 * l)) /
          (N.descFactorial (f i + 2 * e i) : ℝ) =
        ((κ i).descFactorial (f i) : ℝ) *
          ((∏ l ∈ range (e i), (1 - ((κ i : ℝ) + 2 * l) * (1 / (N : ℝ)))) /
            ∏ j ∈ range (f i + 2 * e i), (1 - (j : ℝ) * (1 / (N : ℝ)))) *
          ((N : ℝ) ^ (e i + f i))⁻¹ := by
    intro i
    rw [cast_desc N _ hN (hm i), cast_pairs N (κ i) (e i) hN]
    have h1 : (N : ℝ) ^ (f i + 2 * e i) = (N : ℝ) ^ (e i) * (N : ℝ) ^ (e i + f i) := by
      rw [← pow_add]; congr 1; omega
    rw [h1]
    exact alg_fac _ _ _ _ _ (pow_ne_zero _ hN0)
  rw [prod_congr rfl fun i _ => hfac i, prod_mul_distrib, prod_mul_distrib, prod_inv_distrib,
    prod_pow_eq_pow_sum, sum_add_distrib]
  ring

lemma tendsto_Rf_one (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) :
    Tendsto (fun N : ℕ => Rf κ v e f (1 / (N : ℝ))) atTop (𝓝 1) := by
  have h := (Rf_deriv κ v e f).continuousAt.tendsto.comp
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rwa [Rf_zero] at h

lemma tendsto_Rf_slope (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (Rf κ v e f (1 / (N : ℝ)) - 1)) atTop
      (𝓝 (c0f v e f - ∑ i, (e i : ℝ) * κ i)) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.1 (Rf_deriv κ v e f)
  have h2 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp [hN0]
  refine (h.comp h2).congr fun N => ?_
  simp only [Function.comp_apply, zero_add, Rf_zero, one_div, inv_inv, smul_eq_mul]

/-- `N^a / N^b → 0` for `a < b`. -/
lemma tendsto_pow_mul_inv (a b : ℕ) (hab : a < b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a * ((N : ℝ) ^ b)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) ^ (b - a))⁻¹) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by omega : b - a ≠ 0)).comp
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [pow_sub₀ _ hN0 hab.le]
  field_simp

lemma ev_big (v : ℕ) (e f : Fin r → ℕ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ v ≤ N ∧ ∀ i, f i + 2 * e i ≤ N := by
  filter_upwards [eventually_ge_atTop (1 + v + ∑ i, (f i + 2 * e i))] with N hN
  refine ⟨by omega, by omega, fun i => ?_⟩
  have := single_le_sum (f := fun i => f i + 2 * e i) (fun i _ => Nat.zero_le _) (mem_univ i)
  omega

theorem wtF_tendsto_zero (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ)
    (h : v + 2 ≤ ∑ i, e i + ∑ i, f i) :
    Tendsto (fun N : ℕ => (N : ℝ) * wtF N κ v e f) atTop (𝓝 0) := by
  have h1 := ((tendsto_pow_mul_inv (v + 1) (∑ i, e i + ∑ i, f i) (by omega)).mul_const
    (∏ i, ((κ i).descFactorial (f i) : ℝ))).mul (tendsto_Rf_one κ v e f)
  rw [zero_mul, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [ev_big v e f] with N hN
  rw [wtF_eq κ v e f N hN.1 hN.2.1 hN.2.2]
  ring

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
theorem wtF_tendsto_one (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ)
    (h : v + 1 = ∑ i, e i + ∑ i, f i) :
    Tendsto (fun N : ℕ => (N : ℝ) * wtF N κ v e f) atTop
      (𝓝 (∏ i, ((κ i).descFactorial (f i) : ℝ))) := by
  have h1 := (tendsto_Rf_one κ v e f).const_mul (∏ i, ((κ i).descFactorial (f i) : ℝ))
  rw [mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [ev_big v e f] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [wtF_eq κ v e f N hN.1 hN.2.1 hN.2.2, ← h, pow_succ]
  field_simp

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
/-!
# Part K2: the expansion of expected fixed points to second order along a ray

`tendsto_mul_expFixK_sub_first_order` and `expFixK_le`, from the stubs of Parts F, C2, W, the limits of the weights
(`PartK2_Wt`) and the published `BordenaveCollins.tendsto_expFix` (at `κ = 0`).
-/
/-! ## Fixed points: conjugation, torsion, crude bound -/
lemma fixCount_conj {N : ℕ} (p q : Equiv.Perm (Fin N)) :
    fixCount (p * q * p⁻¹) = fixCount q := by
  unfold fixCount
  refine (card_bij' (fun x _ => p⁻¹ x) (fun x _ => p x) ?_ ?_ ?_ ?_).trans rfl
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    have h := congrArg (fun y => p⁻¹ y) hx.2
    simpa using h
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    simp [hx.2]
  · intro x _; simp
  · intro x _; simp

lemma fixCount_hom_conj {H : Type*} [Group H] {N : ℕ} (φ : H →* Equiv.Perm (Fin N)) (a w : H) :
    fixCount (φ (a * w * a⁻¹)) = fixCount (φ w) := by
  rw [map_mul, map_mul, map_inv, fixCount_conj]

lemma expFixK_conj (N : ℕ) (κ : Fin r → ℕ) (a w : G 0 r) :
    expFixK r N κ (a * w * a⁻¹) = expFixK r N κ w := by
  unfold expFixK expFixOn
  congr 1
  refine sum_congr rfl fun τ _ => ?_
  exact congrArg _ (fixCount_hom_conj (homK τ) a w)

lemma wprod_single (i : Fin r) : (wprod [Sum.inr i] : G 0 r) = mI i := by
  simp [wprod, genL, mI]

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-!
# Part X: mixing over the fixed-point counts

* `mixture`: the uniform law on tuples of involutions is the mixture of the conditional models.
* `fixCount_exp_le`: `E[#fix] ≤ √N + 1`. In fact `E[#fix²] = N` exactly (`sum_fix_sq`): multiplying
  by the transposition `(x y)` is a bijection between involutions fixing `x ≠ y` and involutions
  swapping them, so `E[f (f - 1)] = E[N - f]`; then Cauchy–Schwarz gives `E[#fix] ≤ √N`.
* `mix_affine`: a conditional bound `a * lam κ + b` integrates to `a (1 + r (√N + 1)) + b`.
* `expFix_unif_le`, `upper_unif`.
-/
abbrev Inv (N : ℕ) := ZigZagStrong.ZigZag.Involution N

/-! ## Generic finite probability -/

/-! ## The mixture -/

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-! ## The second moment of the number of fixed points -/

instance (N : ℕ) : Nonempty (Inv N) := ⟨⟨1, fun _ => rfl⟩⟩

end RandomInvolutions.Dev.PartX
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-!
# Part C2, counting: involutions with `k` fixed points containing given fixed points and pairs

A constraint set `E : Finset (Sym2 (Fin N))` encodes fixed points as diagonal pairs `s(a, a)` and
2-cycles as off-diagonal pairs. The number `cnt N k E` of involutions with exactly `k` fixed
points satisfying the constraints is computed by a double count:
`cnt (dg A ∪ P) * [N]_{f + 2e} = #InvK * [k]_f * ∏_{l<e} (N - k - 2l)`.
-/
lemma desc_succ_real (N n : ℕ) :
    (N.descFactorial (n + 1) : ℝ) = ((N : ℝ) - n) * N.descFactorial n := by
  rw [Nat.descFactorial_succ]
  rcases Nat.lt_or_ge N n with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]; simp
  · rw [Nat.cast_mul, Nat.cast_sub h]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {N k : ℕ}
/-- The involution `τ` satisfies the constraints of `E`. -/
def Cont (E : Finset (Sym2 (Fin N))) (τ : InvK N k) : Prop :=
  ∀ a b, s(a, b) ∈ E → τ.1.1 a = b

/-- The number of involutions with `k` fixed points satisfying `E`. -/
def cnt (N k : ℕ) (E : Finset (Sym2 (Fin N))) : ℕ :=
  (univ.filter fun τ : InvK N k => Cont E τ).card

lemma cnt_empty : cnt N k ∅ = Fintype.card (InvK N k) := by
  simp [cnt, Cont]

lemma cont_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (τ : InvK N k) :
    Cont (insert s(a, b) E) τ ↔ τ.1.1 a = b ∧ Cont E τ := by
  constructor
  · intro h
    exact ⟨h a b (mem_insert_self _ _), fun x y hxy => h x y (mem_insert_of_mem hxy)⟩
  · rintro ⟨hab, h⟩ x y hxy
    rcases mem_insert.1 hxy with e | e
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · rw [← hab]; exact τ.1.2 y
    · exact h x y e

lemma cont_mono {E F : Finset (Sym2 (Fin N))} (h : E ⊆ F) (τ : InvK N k) (hτ : Cont F τ) :
    Cont E τ := fun a b hab => hτ a b (h hab)

lemma cnt_eq_sum (E : Finset (Sym2 (Fin N))) (a : Fin N) :
    cnt N k E = ∑ b, cnt N k (insert s(a, b) E) := by
  unfold cnt
  rw [card_eq_sum_card_fiberwise (f := fun τ : InvK N k => τ.1.1 a) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  ext τ
  simp only [mem_filter, mem_univ, true_and, cont_insert]
  tauto

/-! ### Conjugation -/
lemma fixCount_conj (π σ : Equiv.Perm (Fin N)) : fixCount (π * σ * π⁻¹) = fixCount σ := by
  unfold fixCount
  refine card_nbij' (fun x => π⁻¹ x) (fun x => π x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    have := congrArg (fun y => π⁻¹ y) hx
    simpa using this
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    simp [hx]
  · intro x _; simp
  · intro x _; simp

/-- Conjugation of an involution with `k` fixed points. -/
def conjK (π : Equiv.Perm (Fin N)) (τ : InvK N k) : InvK N k :=
  ⟨⟨π * τ.1.1 * π⁻¹, fun x => by simp [Equiv.Perm.mul_apply, τ.1.2]⟩, by
    show fixCount (π * τ.1.1 * π⁻¹) = k
    rw [fixCount_conj]; exact τ.2⟩

lemma conjK_apply (π : Equiv.Perm (Fin N)) (τ : InvK N k) (x : Fin N) :
    (conjK π τ).1.1 x = π (τ.1.1 (π⁻¹ x)) := rfl

lemma conjK_inv (π : Equiv.Perm (Fin N)) (τ : InvK N k) : conjK π⁻¹ (conjK π τ) = τ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [conjK_apply, conjK_apply]
  simp

lemma cont_conj (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) (τ : InvK N k)
    (h : Cont E τ) : Cont (E.image (Sym2.map π)) (conjK π τ) := by
  intro a b hab
  obtain ⟨p, hp, e⟩ := mem_image.1 hab
  induction p using Sym2.inductionOn with
  | hf x y =>
    rw [Sym2.map_mk, Sym2.eq_iff] at e
    rw [conjK_apply]
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [h x y hp]
    · have : τ.1.1 y = x := by rw [← h x y hp]; exact τ.1.2 x
      simp [this]

lemma cnt_image_le (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) :
    cnt N k E ≤ cnt N k (E.image (Sym2.map π)) := by
  unfold cnt
  refine card_le_card_of_injOn (conjK π) ?_ ?_
  · intro τ hτ
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hτ ⊢
    exact cont_conj E π τ hτ
  · intro τ _ τ' _ h
    rw [← conjK_inv π τ, ← conjK_inv π τ', h]

lemma cnt_image (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) :
    cnt N k (E.image (Sym2.map π)) = cnt N k E := by
  refine le_antisymm ?_ (cnt_image_le E π)
  have h := cnt_image_le (k := k) (E.image (Sym2.map π)) π⁻¹
  have e : (E.image (Sym2.map π)).image (Sym2.map ⇑π⁻¹) = E := by
    rw [image_image]
    have : (Sym2.map ⇑π⁻¹ ∘ Sym2.map ⇑π) = id := by
      funext p
      induction p using Sym2.inductionOn with
      | hf x y => simp
    rw [this, image_id]
  rwa [e] at h

/-! ### Supports -/
/-- The points covered by `E`. -/
def supp (E : Finset (Sym2 (Fin N))) : Finset (Fin N) :=
  univ.filter fun x => ∃ y, s(x, y) ∈ E

lemma mem_supp (E : Finset (Sym2 (Fin N))) (x : Fin N) : x ∈ supp E ↔ ∃ y, s(x, y) ∈ E := by
  simp [supp]

lemma supp_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) :
    supp (insert s(a, b) E) = insert a (insert b (supp E)) := by
  ext x
  simp only [mem_supp, mem_insert]
  constructor
  · rintro ⟨y, e | e⟩
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨y, e⟩)
  · rintro (rfl | rfl | ⟨y, hy⟩)
    · exact ⟨b, Or.inl rfl⟩
    · exact ⟨a, Or.inl Sym2.eq_swap⟩
    · exact ⟨y, Or.inr hy⟩

lemma supp_union (E F : Finset (Sym2 (Fin N))) : supp (E ∪ F) = supp E ∪ supp F := by
  ext x
  simp only [mem_supp, mem_union, exists_or]

lemma image_fix (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N))
    (h : ∀ x ∈ supp E, π x = x) : E.image (Sym2.map π) = E := by
  have key : ∀ p ∈ E, Sym2.map π p = id p := by
    intro p hp
    induction p using Sym2.inductionOn with
    | hf x y =>
      rw [Sym2.map_mk, h x ((mem_supp E x).2 ⟨y, hp⟩),
        h y ((mem_supp E y).2 ⟨x, by rw [Sym2.eq_swap]; exact hp⟩)]
      rfl
  rw [image_congr key, image_id]

lemma cnt_move (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) (p : Sym2 (Fin N))
    (h : ∀ x ∈ supp E, π x = x) :
    cnt N k (insert (Sym2.map π p) E) = cnt N k (insert p E) := by
  rw [← cnt_image (insert p E) π, image_insert, image_fix E π h]

lemma cnt_bad (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E) (hb : b ∈ supp E) :
    cnt N k (insert s(a, b) E) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ h
  rw [cont_insert] at h
  obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
  have h1 : τ.1.1 b = y := h.2 b y hy
  have h2 : τ.1.1 b = a := by rw [← h.1]; exact τ.1.2 a
  apply ha
  rw [mem_supp]
  refine ⟨b, ?_⟩
  have : y = a := h1.symm.trans h2
  subst this
  rw [Sym2.eq_swap]; exact hy

/-! ### The two recursions -/
/-- The number of fixed-point constraints. -/
def dcount (E : Finset (Sym2 (Fin N))) : ℕ := ((supp E).filter fun a => s(a, a) ∈ E).card

lemma cnt_diag_supp (E : Finset (Sym2 (Fin N))) (a : Fin N) (ha : a ∈ supp E) :
    cnt N k (insert s(a, a) E) = if s(a, a) ∈ E then cnt N k E else 0 := by
  split_ifs with h
  · rw [insert_eq_of_mem h]
  · unfold cnt
    rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    rw [cont_insert] at hτ
    obtain ⟨y, hy⟩ := (mem_supp E a).1 ha
    have : y = a := by rw [← hτ.2 a y hy]; exact hτ.1
    subst this
    exact h hy

lemma sum_diag (E : Finset (Sym2 (Fin N))) :
    ∑ a : Fin N, cnt N k (insert s(a, a) E) = k * cnt N k E := by
  have h : ∀ a : Fin N, cnt N k (insert s(a, a) E) =
      ∑ τ ∈ univ.filter (fun τ : InvK N k => Cont E τ), if τ.1.1 a = a then 1 else 0 := by
    intro a
    unfold cnt
    rw [← card_filter, filter_filter]
    congr 1
    ext τ
    simp only [mem_filter, mem_univ, true_and, cont_insert]
    tauto
  simp only [h]
  rw [sum_comm, sum_congr rfl (g := fun _ => k)]
  · rw [sum_const, smul_eq_mul, mul_comm]; rfl
  · intro τ _
    rw [← card_filter]; exact τ.2

lemma fix_step_nat (E : Finset (Sym2 (Fin N))) (a : Fin N) (ha : a ∉ supp E) :
    (N - (supp E).card) * cnt N k (insert s(a, a) E) + dcount E * cnt N k E =
      k * cnt N k E := by
  rw [← sum_diag E, ← sum_sdiff (subset_univ (supp E))]
  congr 1
  · rw [sum_congr rfl (g := fun _ => cnt N k (insert s(a, a) E))]
    · rw [sum_const, smul_eq_mul, card_sdiff_of_subset (subset_univ _), card_univ,
        Fintype.card_fin]
    · intro a' ha'
      have ha' : a' ∉ supp E := (mem_sdiff.1 ha').2
      have := cnt_move (k := k) E (Equiv.swap a a') s(a, a) (fun x hx =>
        Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact ha hx) (by rintro rfl; exact ha' hx))
      rw [Sym2.map_mk, Equiv.swap_apply_left] at this
      exact this
  · rw [sum_congr rfl (fun a' ha' => cnt_diag_supp E a' ha'), sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul]
    rfl

lemma pair_step_nat (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E)
    (hb : b ∉ supp E) (hab : a ≠ b) :
    cnt N k E = cnt N k (insert s(a, a) E) +
      (N - ((supp E).card + 1)) * cnt N k (insert s(a, b) E) := by
  rw [cnt_eq_sum E a, ← sum_sdiff (subset_univ (insert a (supp E))), add_comm]
  congr 1
  · rw [sum_insert ha, sum_eq_zero (fun b' hb' => cnt_bad E a b' ha hb'), add_zero]
  · rw [sum_congr rfl (g := fun _ => cnt N k (insert s(a, b) E))]
    · rw [sum_const, smul_eq_mul, card_sdiff_of_subset (subset_univ _), card_univ,
        Fintype.card_fin, card_insert_of_notMem ha]
    · intro b' hb'
      simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_or] at hb'
      have := cnt_move (k := k) E (Equiv.swap b b') s(a, b) (fun x hx =>
        Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hb hx)
          (by rintro rfl; exact hb'.2 hx))
      rw [Sym2.map_mk, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hb'.1)] at this
      exact this

lemma fix_step (E : Finset (Sym2 (Fin N))) (a : Fin N) (ha : a ∉ supp E) :
    ((N : ℝ) - (supp E).card) * cnt N k (insert s(a, a) E) =
      ((k : ℝ) - dcount E) * cnt N k E := by
  have h := fix_step_nat (k := k) E a ha
  have hle : (supp E).card ≤ N := (card_le_univ _).trans (Fintype.card_fin N).le
  have h' : (((N - (supp E).card : ℕ) : ℝ)) * cnt N k (insert s(a, a) E) +
      (dcount E : ℝ) * cnt N k E = (k : ℝ) * cnt N k E := by exact_mod_cast h
  rw [Nat.cast_sub hle] at h'
  linarith

lemma pair_combine (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E)
    (hb : b ∉ supp E) (hab : a ≠ b) :
    ((N : ℝ) - (supp E).card) * ((N : ℝ) - (supp E).card - 1) * cnt N k (insert s(a, b) E) =
      ((N : ℝ) - (supp E).card - k + dcount E) * cnt N k E := by
  have h := pair_step_nat (k := k) E a b ha hb hab
  have hle : (supp E).card + 1 ≤ N := by
    have : (insert a (supp E)).card ≤ N := (card_le_univ _).trans (Fintype.card_fin N).le
    rwa [card_insert_of_notMem ha] at this
  have h' : (cnt N k E : ℝ) = cnt N k (insert s(a, a) E) +
      ((N - ((supp E).card + 1) : ℕ) : ℝ) * cnt N k (insert s(a, b) E) := by exact_mod_cast h
  rw [Nat.cast_sub hle] at h'
  push_cast at h'
  have h2 := fix_step (k := k) E a ha
  linear_combination (-((N : ℝ) - (supp E).card)) * h' - h2

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-! ### Diagonal constraints and partial matchings -/
/-- The diagonal pairs of a set of points. -/
def dg {α : Type*} [DecidableEq α] (A : Finset α) : Finset (Sym2 α) := A.image fun a => s(a, a)

lemma mem_dg {α : Type*} [DecidableEq α] (A : Finset α) (a b : α) :
    s(a, b) ∈ dg A ↔ a = b ∧ a ∈ A := by
  unfold dg
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, e⟩
    rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, hx⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {N k : ℕ}
lemma supp_dg (A : Finset (Fin N)) : supp (dg A) = A := by
  ext x
  rw [mem_supp]
  constructor
  · rintro ⟨y, hy⟩
    exact ((mem_dg A x y).1 hy).2
  · intro hx
    exact ⟨x, (mem_dg A x x).2 ⟨rfl, hx⟩⟩

lemma pmat_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (h : PMat (insert s(a, b) E))
    (hn : s(a, b) ∉ E) : PMat E ∧ a ≠ b ∧ a ∉ supp E ∧ b ∉ supp E := by
  refine ⟨⟨fun p hp => h.1 p (mem_insert_of_mem hp), fun p hp q hq =>
    h.2 p (mem_insert_of_mem hp) q (mem_insert_of_mem hq)⟩, ?_, ?_, ?_⟩
  · intro e
    exact h.1 _ (mem_insert_self _ _) (Sym2.mk_isDiag_iff.2 e)
  · intro ha
    obtain ⟨y, hy⟩ := (mem_supp E a).1 ha
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨a, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)
  · intro hb
    obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨b, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)

lemma card_supp (E : Finset (Sym2 (Fin N))) : PMat E → (supp E).card = 2 * E.card := by
  induction E using Finset.induction_on with
  | empty => intro _; simp [supp]
  | insert p E hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert E a b h hp
      rw [supp_insert, card_insert_of_notMem, card_insert_of_notMem hb, ih hE,
        card_insert_of_notMem hp]
      · ring
      · simp [hab, ha]

lemma disjoint_supp (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N)))
    (hAP : ∀ a ∈ A, ∀ p ∈ P, a ∉ p) : Disjoint A (supp P) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨y, hy⟩ := (mem_supp P x).1 hx'
  exact hAP x hx _ hy (Sym2.mem_mk_left _ _)

lemma card_union_supp (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) (hP : PMat P)
    (hAP : ∀ a ∈ A, ∀ p ∈ P, a ∉ p) : (A ∪ supp P).card = A.card + 2 * P.card := by
  rw [card_union_of_disjoint (disjoint_supp A P hAP), card_supp P hP]

lemma supp_dg_union (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) :
    supp (dg A ∪ P) = A ∪ supp P := by
  rw [supp_union, supp_dg]

lemma dcount_dg_union (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) (hP : PMat P) :
    dcount (dg A ∪ P) = A.card := by
  unfold dcount
  congr 1
  ext a
  rw [mem_filter, supp_dg_union, mem_union, mem_union, mem_dg]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h.2
    · exact absurd (Sym2.mk_isDiag_iff.2 rfl) (hP.1 _ h)
  · intro ha
    exact ⟨Or.inl ha, Or.inl ⟨rfl, ha⟩⟩

/-- Fixed points only. -/
lemma cnt_dg (A : Finset (Fin N)) :
    (cnt N k (dg A) : ℝ) * (N.descFactorial A.card : ℝ) =
      (Fintype.card (InvK N k) : ℝ) * (k.descFactorial A.card : ℝ) := by
  induction A using Finset.induction_on with
  | empty => simp [dg, cnt_empty]
  | insert a A ha ih =>
    have hs : a ∉ supp (dg A) := by rw [supp_dg]; exact ha
    have h1 := fix_step (k := k) (dg A) a hs
    have hd : dcount (dg A) = A.card := by
      have := dcount_dg_union A ∅ ⟨by simp, by simp⟩
      rwa [union_empty] at this
    rw [supp_dg, hd] at h1
    have e : dg (insert a A) = insert s(a, a) (dg A) := by
      unfold dg; rw [image_insert]
    rw [e, card_insert_of_notMem ha, desc_succ_real, desc_succ_real]
    linear_combination (N.descFactorial A.card : ℝ) * h1 + ((k : ℝ) - A.card) * ih

/-- The main count, in product form. -/
lemma cnt_mul (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) :
    PMat P → (∀ a ∈ A, ∀ p ∈ P, a ∉ p) →
    (cnt N k (dg A ∪ P) : ℝ) * (N.descFactorial (A.card + 2 * P.card) : ℝ) =
      (Fintype.card (InvK N k) : ℝ) * (k.descFactorial A.card : ℝ) *
        ∏ l ∈ range P.card, ((N : ℝ) - k - 2 * l) := by
  induction P using Finset.induction_on with
  | empty =>
    intro _ _
    simpa using cnt_dg (k := k) A
  | insert p P hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h hAP
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert P a b h hp
      have hAP' : ∀ a ∈ A, ∀ p ∈ P, a ∉ p := fun x hx p hp' => hAP x hx p (mem_insert_of_mem hp')
      have ih' := ih hE hAP'
      have haA : a ∉ A := fun h' => hAP a h' _ (mem_insert_self _ _) (Sym2.mem_mk_left _ _)
      have hbA : b ∉ A := fun h' => hAP b h' _ (mem_insert_self _ _) (Sym2.mem_mk_right _ _)
      have hsa : a ∉ supp (dg A ∪ P) := by
        rw [supp_dg_union, mem_union]; tauto
      have hsb : b ∉ supp (dg A ∪ P) := by
        rw [supp_dg_union, mem_union]; tauto
      have hc := pair_combine (k := k) (dg A ∪ P) a b hsa hsb hab
      rw [supp_dg_union, card_union_supp A P hE hAP', dcount_dg_union A P hE] at hc
      push_cast at hc
      have e1 : A.card + 2 * (P.card + 1) = (A.card + 2 * P.card) + 1 + 1 := by ring
      rw [union_insert, card_insert_of_notMem hp, e1, desc_succ_real, desc_succ_real,
        prod_range_succ]
      push_cast
      linear_combination (N.descFactorial (A.card + 2 * P.card) : ℝ) * hc +
        ((N : ℝ) - k - 2 * P.card) * ih'

/-- The main count: the number of involutions with `k` fixed points fixing the points of `A`
and containing the disjoint pairs of `P`. -/
theorem cnt_formula (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) (hP : PMat P)
    (hAP : ∀ a ∈ A, ∀ p ∈ P, a ∉ p) :
    (cnt N k (dg A ∪ P) : ℝ) = (Fintype.card (InvK N k) : ℝ) *
      (((k.descFactorial A.card : ℝ) * ∏ l ∈ range P.card, ((N : ℝ) - k - 2 * l)) /
        (N.descFactorial (A.card + 2 * P.card) : ℝ)) := by
  have hle : A.card + 2 * P.card ≤ N := by
    rw [← card_union_supp A P hP hAP]
    exact (card_le_univ _).trans (Fintype.card_fin N).le
  have hD : (N.descFactorial (A.card + 2 * P.card) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have h := cnt_mul (k := k) A P hP hAP
  rw [← mul_div_assoc, eq_div_iff hD, h]
  ring

/-- No involution contains two overlapping distinct pairs. -/
lemma cnt_not_pmat (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N)))
    (hnd : ∀ p ∈ P, ¬ p.IsDiag) (h : ¬ PMat P) : cnt N k (dg A ∪ P) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ hτ'
  have hσ : Cont P τ := cont_mono subset_union_right τ hτ'
  apply h
  refine ⟨hnd, fun p hp q hq => ?_⟩
  induction p using Sym2.inductionOn with
  | hf a b =>
    induction q using Sym2.inductionOn with
    | hf a' b' =>
      rintro ⟨x, hx, hx'⟩
      have h1 := hσ a b hp
      have h2 := hσ a' b' hq
      have h3 : τ.1.1 b = a := by rw [← h1]; exact τ.1.2 a
      have h4 : τ.1.1 b' = a' := by rw [← h2]; exact τ.1.2 a'
      rw [Sym2.eq_iff]
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rcases Sym2.mem_iff.1 hx' with rfl | rfl
      · exact Or.inl ⟨rfl, h1.symm.trans h2⟩
      · exact Or.inr ⟨rfl, h1.symm.trans h4⟩
      · exact Or.inr ⟨h3.symm.trans h2, rfl⟩
      · exact Or.inl ⟨h3.symm.trans h4, rfl⟩

/-- No involution fixes a point of one of its 2-cycles. -/
lemma cnt_meet (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N)))
    (hnd : ∀ p ∈ P, ¬ p.IsDiag) (a : Fin N) (ha : a ∈ A) (p : Sym2 (Fin N)) (hp : p ∈ P)
    (hap : a ∈ p) : cnt N k (dg A ∪ P) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ hτ
  have h1 : τ.1.1 a = a := hτ a a (mem_union_left _ ((mem_dg A a a).2 ⟨rfl, ha⟩))
  have hnd' := hnd p hp
  induction p using Sym2.inductionOn with
  | hf x y =>
    have h2 : τ.1.1 x = y := hτ x y (mem_union_right _ hp)
    rw [Sym2.mk_isDiag_iff] at hnd'
    rcases Sym2.mem_iff.1 hap with rfl | rfl
    · exact hnd' (h1.symm.trans h2)
    · apply hnd'
      have h3 : τ.1.1 a = x := by rw [← h2]; exact τ.1.2 x
      exact h3.symm.trans h1

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-! ### Existence -/
lemma nonempty_invK (N k : ℕ) (hk : k ≤ N) (hpar : k % 2 = N % 2) : Nonempty (InvK N k) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = k + (m + m) := ⟨(N - k) / 2, by omega⟩
  let e : Fin k ⊕ (Fin m ⊕ Fin m) ≃ Fin (k + (m + m)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let S : Equiv.Perm (Fin k ⊕ (Fin m ⊕ Fin m)) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)
  have hSS : ∀ y, S (S y) = y := by
    rintro (i | j | j) <;> rfl
  have hS : ∀ y, S y = y ↔ ∃ i, y = Sum.inl i := by
    rintro (i | j | j) <;> simp [S]
  let σ : Equiv.Perm (Fin (k + (m + m))) := e.symm.trans (S.trans e)
  have hσ : ∀ x, σ x = e (S (e.symm x)) := fun x => rfl
  refine ⟨⟨⟨σ, fun x => by rw [hσ, hσ, e.symm_apply_apply, hSS, e.apply_symm_apply]⟩, ?_⟩⟩
  show fixCount σ = k
  unfold fixCount
  have hinj : Function.Injective fun i : Fin k => e (Sum.inl i) :=
    fun i j h => Sum.inl.inj (e.injective h)
  have : (univ.filter fun x => σ x = x) = (univ : Finset (Fin k)).image
      fun i => e (Sum.inl i) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    rw [hσ]
    constructor
    · intro h
      have h' : S (e.symm x) = e.symm x := by
        apply e.injective; rw [h, e.apply_symm_apply]
      obtain ⟨i, hi⟩ := (hS _).1 h'
      exact ⟨i, by rw [← hi, e.apply_symm_apply]⟩
    · rintro ⟨i, rfl⟩
      rw [e.symm_apply_apply, (hS _).2 ⟨i, rfl⟩]
  rw [this, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
/-!
# Part C2: the counting formula with loops, and rationality along rays

Proofs of `RandomInvolutions.Dev.nonempty_omK`, `RandomInvolutions.Dev.expect_formulaK`, `RandomInvolutions.Dev.rationalK`.
-/
theorem nonempty_omK (N : ℕ) (κ : Fin r → ℕ) (hA : AdmK N κ) : Nonempty (OmK r N κ) :=
  ⟨fun i => (nonempty_invK N (κ i) (hA i).1 (hA i).2).some⟩

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part C2: the counting formula with loops, and rationality along rays -/
alias nonempty_omK := RandomInvolutions.Dev.PartC2.nonempty_omK

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
lemma card_invK_ne_zero (N k : ℕ) (hk : k ≤ N) (hpar : k % 2 = N % 2) :
    (Fintype.card (InvK N k) : ℝ) ≠ 0 := by
  have := nonempty_invK N k hk hpar
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ} (u : List (Lt 0 r))
/-!
# Part C2, paths: the counting formula for the expected number of fixed points of a word in the
conditional model
-/
/-! ## Paths along a word -/
/-- `τ` realises the path `x`. -/
def Rz {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (x : Fin (u.length + 1) → Fin N) :
    Prop :=
  ∀ t : Fin u.length, x t.castSucc = letterPermI τ (u.get t) (x t.succ)

/-- The path of `y` under `τ`. -/
def path {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N) :
    Fin (u.length + 1) → Fin N :=
  fun t => wordPermI τ (u.drop t) y

lemma wordPermI_cons_apply {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (l : Lt 0 r)
    (ws : List (Lt 0 r)) (y : Fin N) :
    wordPermI τ (l :: ws) y = letterPermI τ l (wordPermI τ ws y) := by
  simp [wordPermI, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N) :
    path u τ y (Fin.last _) = y := by
  simp [path, wordPermI]

lemma path_zero {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N) :
    path u τ y 0 = wordPermI τ u y := by
  simp [path]

lemma path_step {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N)
    (t : Fin u.length) :
    path u τ y t.castSucc = letterPermI τ (u.get t) (path u τ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPermI_cons_apply]
  rfl

lemma eq_path {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N)
    (x : Fin (u.length + 1) → Fin N) (hx : Rz u τ x) : x = path u τ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) :
    fixCount (wordPermI τ u) =
      (univ.filter fun x : Fin (u.length + 1) → Fin N =>
        Rz u τ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path u τ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    have := eq_path u τ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy ⊢
    exact ⟨fun t => path_step u τ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx
    exact (eq_path u τ x hx.1).symm
  · intro y _
    exact path_last u τ y

/-- The constraints of colour `i` of a path: loops as diagonal pairs, and pairs. -/
def EK {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) : Finset (Sym2 α) :=
  dg (Ls u x i) ∪ Ps u x i

lemma Ps_not_diag {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) :
    ∀ p ∈ Ps u x i, ¬ p.IsDiag := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
  rw [Sym2.mk_isDiag_iff]
  exact (mem_filter.1 ht).2.2

lemma Rz_iff {N : ℕ} {κ : Fin r → ℕ} (ω : OmK r N κ) (x : Fin (u.length + 1) → Fin N) :
    Rz u (fun i => (ω i).1) x ↔ ∀ i, Cont (EK u x i) (ω i) := by
  constructor
  · intro h i a b hab
    rcases mem_union.1 hab with hab | hab
    · obtain ⟨rfl, ha⟩ := (mem_dg _ a b).1 hab
      obtain ⟨t, ht, rfl⟩ := mem_image.1 ha
      have ht := (mem_filter.1 ht).2
      have h' := h t
      rw [ht.1] at h'
      have h'' : x t.castSucc = (ω i).1.1 (x t.succ) := h'
      rw [← ht.2] at h''
      exact h''.symm
    · obtain ⟨t, ht, e⟩ := mem_image.1 hab
      have ht := (mem_filter.1 ht).2
      have h' := h t
      rw [ht.1] at h'
      have h'' : x t.castSucc = (ω i).1.1 (x t.succ) := h'
      rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h'']; exact (ω i).1.2 _
      · exact h''.symm
  · intro h t
    rcases hl : u.get t with ⟨i, b⟩ | j
    · exact i.elim0
    · show x t.castSucc = (ω j).1.1 (x t.succ)
      by_cases hx : x t.castSucc = x t.succ
      · have hm : x t.castSucc ∈ Ls u x j :=
          mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl, hx⟩, rfl⟩
        have := h j (x t.castSucc) (x t.castSucc)
          (mem_union_left _ ((mem_dg _ _ _).2 ⟨rfl, hm⟩))
        rw [← hx, this]
      · have hm : s(x t.castSucc, x t.succ) ∈ Ps u x j :=
          mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl, hx⟩, rfl⟩
        have := h j (x t.castSucc) (x t.succ) (mem_union_right _ hm)
        rw [← this]; exact ((ω j).1.2 _).symm

lemma card_Rz {N : ℕ} (κ : Fin r → ℕ) (x : Fin (u.length + 1) → Fin N) :
    (univ.filter fun ω : OmK r N κ => Rz u (fun i => (ω i).1) x).card =
      ∏ i, cnt N (κ i) (EK u x i) := by
  have : (univ.filter fun ω : OmK r N κ => Rz u (fun i => (ω i).1) x) =
      Fintype.piFinset fun i => univ.filter fun τ : InvK N (κ i) => Cont (EK u x i) τ := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact Rz_iff u ω x
  rw [this, Fintype.card_piFinset]
  rfl

/-- The probability factor of one colour. -/
def Wf (N k f e : ℕ) : ℝ :=
  ((k.descFactorial f : ℝ) * ∏ l ∈ range e, ((N : ℝ) - k - 2 * l)) /
    (N.descFactorial (f + 2 * e) : ℝ)

/-- The weight of a path: the number of samples realising it. -/
def W (N : ℕ) (κ : Fin r → ℕ) {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) : ℝ :=
  if GoodL u x then
    ∏ i, ((Fintype.card (InvK N (κ i)) : ℝ) * Wf N (κ i) (Ls u x i).card (Ps u x i).card)
  else 0

lemma sum_fixCount (N : ℕ) (κ : Fin r → ℕ) :
    (∑ ω : OmK r N κ, (fixCount (wordPermI (fun i => (ω i).1) u) : ℝ)) =
      ∑ x : Fin (u.length + 1) → Fin N, W u N κ x := by
  have h0 : ∀ ω : OmK r N κ, (fixCount (wordPermI (fun i => (ω i).1) u) : ℝ) =
      ∑ x : Fin (u.length + 1) → Fin N,
        if Rz u (fun i => (ω i).1) x ∧ x 0 = x (Fin.last _) then (1 : ℝ) else 0 := by
    intro ω; rw [fixCount_eq, Finset.sum_boole]
  simp only [h0]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hcl : x 0 = x (Fin.last _)
  · have h1 : (∑ ω : OmK r N κ,
        if Rz u (fun i => (ω i).1) x ∧ x 0 = x (Fin.last _) then (1 : ℝ) else 0) =
        ((univ.filter fun ω : OmK r N κ => Rz u (fun i => (ω i).1) x).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine sum_congr rfl fun ω _ => ?_
      simp only [hcl, and_true]
    rw [h1, card_Rz]
    push_cast
    by_cases hg : GoodL u x
    · unfold W
      rw [if_pos hg]
      refine prod_congr rfl fun i _ => ?_
      exact cnt_formula _ _ (hg.1 i) (hg.2.1 i)
    · unfold W
      rw [if_neg hg]
      by_cases h1 : ∀ i, PMat (Ps u x i)
      · by_cases h2 : ∀ i, ∀ a ∈ Ls u x i, ∀ p ∈ Ps u x i, a ∉ p
        · exact absurd ⟨h1, h2, hcl⟩ hg
        · push Not at h2
          obtain ⟨i, a, ha, p, hp, hap⟩ := h2
          refine prod_eq_zero (mem_univ i) ?_
          have := cnt_meet (k := κ i) (Ls u x i) (Ps u x i) (Ps_not_diag u x i) a ha p hp hap
          unfold EK
          rw [this]; simp
      · push Not at h1
        obtain ⟨i, hi⟩ := h1
        refine prod_eq_zero (mem_univ i) ?_
        have := cnt_not_pmat (k := κ i) (Ls u x i) (Ps u x i) (Ps_not_diag u x i) hi
        unfold EK
        rw [this]; simp
  · unfold W
    rw [if_neg (fun h => hcl h.2.2)]
    simp [hcl]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {n : ℕ} {α : Type*} [DecidableEq α]
/-! ## Canonical representatives of kernels -/
lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
/-! ## Invariance under relabelling -/
omit [DecidableEq α] [DecidableEq β] in
lemma sym2_map_inj (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S) (p q : Sym2 β)
    (hp : ∀ a ∈ p, a ∈ S) (hq : ∀ a ∈ q, a ∈ S) (h : Sym2.map φ p = Sym2.map φ q) : p = q := by
  induction p using Sym2.inductionOn with
  | hf a b =>
    induction q using Sym2.inductionOn with
    | hf a' b' =>
      have ha := hp a (Sym2.mem_mk_left _ _)
      have hb := hp b (Sym2.mem_mk_right _ _)
      have ha' := hq a' (Sym2.mem_mk_left _ _)
      have hb' := hq b' (Sym2.mem_mk_right _ _)
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h
      rw [Sym2.eq_iff]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hφ ha ha' h1, hφ hb hb' h2⟩
      · exact Or.inr ⟨hφ ha hb' h1, hφ hb ha' h2⟩

omit [DecidableEq β] in
lemma pmat_image (E : Finset (Sym2 β)) (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S)
    (hE : ∀ p ∈ E, ∀ a ∈ p, a ∈ S) : PMat (E.image (Sym2.map φ)) ↔ PMat E := by
  unfold PMat
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine and_congr (forall₂_congr fun p hp => ?_)
    (forall₂_congr fun p hp => forall₂_congr fun q hq => ?_)
  · have := hE p hp
    induction p using Sym2.inductionOn with
    | hf a b =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mk_isDiag_iff,
        hφ.eq_iff (this a (Sym2.mem_mk_left _ _)) (this b (Sym2.mem_mk_right _ _))]
  · constructor
    · intro H y hy hy'
      exact sym2_map_inj φ S hφ p q (hE p hp) (hE q hq)
        (H (φ y) (Sym2.mem_map.2 ⟨y, hy, rfl⟩) (Sym2.mem_map.2 ⟨y, hy', rfl⟩))
    · intro H x hx hx'
      obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.1 hx
      obtain ⟨y', hy', e⟩ := Sym2.mem_map.1 hx'
      have : y' = y := hφ (hE q hq y' hy') (hE p hp y hy) e
      subst this
      rw [H _ hy hy']

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {r : ℕ} (u : List (Lt 0 r))
lemma Ls_range (c : Fin (u.length + 1) → β) (i : Fin r) (a : β) (ha : a ∈ Ls u c i) :
    a ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 ha
  exact ⟨_, rfl⟩

lemma Ps_range (c : Fin (u.length + 1) → β) (i : Fin r) (p : Sym2 β) (hp : p ∈ Ps u c i) :
    ∀ a ∈ p, a ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  intro a ha
  rcases Sym2.mem_iff.1 ha with rfl | rfl <;> exact ⟨_, rfl⟩

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {r : ℕ} (u : List (Lt 0 r))
variable (c : Fin (u.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ
lemma Ls_comp (i : Fin r) : Ls u (φ ∘ c) i = (Ls u c i).image φ := by
  have hf : (univ.filter fun t : Fin u.length =>
      u.get t = Sum.inr i ∧ (φ ∘ c) t.castSucc = (φ ∘ c) t.succ) =
      univ.filter fun t => u.get t = Sum.inr i ∧ c t.castSucc = c t.succ :=
    filter_congr fun t _ => and_congr Iff.rfl (hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩)
  unfold Ls
  rw [hf, image_image]
  rfl

lemma Ps_comp (i : Fin r) : Ps u (φ ∘ c) i = (Ps u c i).image (Sym2.map φ) := by
  have hf : (univ.filter fun t : Fin u.length =>
      u.get t = Sum.inr i ∧ (φ ∘ c) t.castSucc ≠ (φ ∘ c) t.succ) =
      univ.filter fun t => u.get t = Sum.inr i ∧ c t.castSucc ≠ c t.succ :=
    filter_congr fun t _ => and_congr Iff.rfl (not_congr (hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩))
  unfold Ps
  rw [hf, image_image]
  rfl

lemma card_Ls_comp (i : Fin r) : (Ls u (φ ∘ c) i).card = (Ls u c i).card := by
  rw [Ls_comp u c φ hφ]
  exact card_image_of_injOn fun a ha b hb hab =>
    hφ (Ls_range u c i a ha) (Ls_range u c i b hb) hab

lemma card_Ps_comp (i : Fin r) : (Ps u (φ ∘ c) i).card = (Ps u c i).card := by
  rw [Ps_comp u c φ hφ]
  exact card_image_of_injOn fun p hp q hq hpq =>
    sym2_map_inj φ _ hφ p q (Ps_range u c i p hp) (Ps_range u c i q hq) hpq

lemma good_comp : GoodL u (φ ∘ c) ↔ GoodL u c := by
  unfold GoodL
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) ?_)
  · rw [Ps_comp u c φ hφ]
    exact pmat_image _ φ _ hφ (Ps_range u c i)
  · rw [Ls_comp u c φ hφ, Ps_comp u c φ hφ]
    constructor
    · intro H a ha p hp hmem
      exact H (φ a) (mem_image_of_mem _ ha) (Sym2.map φ p) (mem_image_of_mem _ hp)
        (Sym2.mem_map.2 ⟨a, hmem, rfl⟩)
    · intro H a' ha' p' hp' hmem
      obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
      obtain ⟨b, hb, e⟩ := Sym2.mem_map.1 hmem
      have : b = a := hφ (Ps_range u c i p hp b hb) (Ls_range u c i a ha) e
      exact H a ha p hp (this ▸ hb)
  · exact hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩

lemma W_comp (N : ℕ) (κ : Fin r → ℕ) : W u N κ (φ ∘ c) = W u N κ c := by
  unfold W
  simp only [good_comp u c φ hφ, card_Ls_comp u c φ hφ, card_Ps_comp u c φ hφ]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-!
# Part F, toolkit: normal forms in `F_r * Γ_s` (van der Waerden's trick) and reduced words

Stated for `G r s`, `Lt r s` with the `RandomInvolutions.Dev` versions of `bar`, `Red`, `CycRed`; Part F uses it at
`G 0 r`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_one : (1 : G r s)⁻¹ = 1 := inv_one

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem bar_injective : Function.Injective (bar : Lt r s → Lt r s) :=
  fun a b h => by rw [← bar_bar a, h, bar_bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

theorem wprod_singleton (a : Lt r s) : wprod [a] = genL a := by simp

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem push_of_red_cons {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) :
    push a t = a :: t := by
  cases t with
  | nil => rfl
  | cons b t => exact push_cons_ne _ _ _ (red_cons_cons.1 h).1

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

theorem red_nf (g : G r s) : Red (nf g) := (hom r s g ⟨[], red_nil⟩).2

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem hom_wprod_nil (u : List (Lt r s)) (hu : Red u) :
    hom r s (wprod u) ⟨[], red_nil⟩ = ⟨u, hu⟩ := by
  induction u with
  | nil => simp
  | cons a t ih =>
    apply Subtype.ext
    rw [wprod_cons, hom_genL_mul, ih (Red.tail' hu)]
    exact push_of_red_cons hu

theorem nf_wprod' (u : List (Lt r s)) (hu : Red u) : nf (wprod u) = u :=
  congrArg Subtype.val (hom_wprod_nil u hu)

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem nf_injective : Function.Injective (nf : G r s → List (Lt r s)) := by
  intro g h e
  rw [← wprod_nf g, e, wprod_nf]

theorem nf_eq_nil_iff' (g : G r s) : nf g = [] ↔ g = 1 :=
  ⟨fun h => nf_injective (h.trans nf_one.symm), fun h => h ▸ nf_one⟩

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

theorem len_wprod_le (u : List (Lt r s)) : len (wprod u) ≤ u.length := len_le_of_wprod rfl

theorem len_wprod_of_red {u : List (Lt r s)} (hu : Red u) : len (wprod u) = u.length := by
  rw [len_eq_length_nf, nf_wprod' u hu]

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

theorem nf_genL (a : Lt r s) : nf (genL a) = [a] := by
  have := nf_wprod' [a] (List.isChain_singleton _)
  rwa [wprod_singleton] at this

/-! ## Aliases -/
theorem nf_wprod {u : List (Lt r s)} (h : Red u) : nf (wprod u) = u := nf_wprod' u h

theorem nf_eq_nil_iff {g : G r s} : nf g = [] ↔ g = 1 := nf_eq_nil_iff' g

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/
theorem gid_cancel {H : Type*} [Group H] (x a y : H) : x * (a * (a⁻¹ * y)) = x * y := by group

theorem gid_conj_inv {H : Type*} [Group H] (p X : H) : X = p⁻¹ * (p * X * p⁻¹) * p⁻¹⁻¹ := by
  group

theorem gid_conj_mul {H : Type*} [Group H] (x w u : H) :
    (x * w) * u * (x * w)⁻¹ = x * (w * u * w⁻¹) * x⁻¹ := by group

theorem gid_sq_conj {H : Type*} [Group H] (p c : H) (h : p * c * p⁻¹ * (p * c * p⁻¹) = 1) :
    c * c = 1 := by
  have : c * c = p⁻¹ * (p * c * p⁻¹ * (p * c * p⁻¹)) * p := by group
  rw [this, h]; group

theorem gid_conj_eq_one {H : Type*} [Group H] (p c : H) (h : p * c * p⁻¹ = 1) : c = 1 := by
  have : c = p⁻¹ * (p * c * p⁻¹) * p := by group
  rw [this, h]; group

theorem gid_conj_sq {H : Type*} [Group H] (p c : H) (h : c * c = 1) :
    p * c * p⁻¹ * (p * c * p⁻¹) = 1 := by
  have : p * c * p⁻¹ * (p * c * p⁻¹) = p * (c * c) * p⁻¹ := by group
  rw [this, h]; group

theorem gid_conj_pow_sq {H : Type*} [Group H] (a z : H) (k : ℕ)
    (h : a * z ^ k * a⁻¹ * (a * z ^ k * a⁻¹) = 1) : z ^ (k + k) = 1 := by
  rw [pow_add]
  exact gid_sq_conj a (z ^ k) h

theorem red_left {u v : List (Lt r s)} (h : Red (u ++ v)) : Red u := List.IsChain.left_of_append h

theorem eq_nil_of_red_of_wprod {u : List (Lt r s)} (hu : Red u) (h : wprod u = 1) : u = [] := by
  rw [← nf_wprod hu, h, nf_one]

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}

theorem getElem_congr_idx (u : List (Lt r s)) {i j : ℕ} (hi : i < u.length) (hj : j < u.length)
    (h : i = j) : u[i] = u[j] := by subst h; rfl

/-- A reduced nonempty word whose first letter is not the inverse of its last letter is
cyclically reduced. -/
theorem cycRed_of_red (u : List (Lt r s)) (hu : Red u) (hne : u ≠ [])
    (h : u.head hne ≠ bar (u.getLast hne)) : CycRed u := by
  intro t
  have hpos : 0 < u.length := List.length_pos_iff.2 hne
  simp only [List.get_eq_getElem]
  by_cases ht : t.val + 1 < u.length
  · have := (List.isChain_iff_getElem.1 hu) t.val ht
    rw [getElem_congr_idx u (Nat.mod_lt _ hpos) ht (Nat.mod_eq_of_lt ht)]
    exact this
  · have ht' : t.val = u.length - 1 := by have := t.2; omega
    have h0 : (t.val + 1) % u.length = 0 := by
      rw [ht', Nat.sub_add_cancel hpos, Nat.mod_self]
    rw [getElem_congr_idx u (Nat.mod_lt _ hpos) hpos h0,
      getElem_congr_idx u t.2 (by omega) ht']
    rw [List.head_eq_getElem, List.getLast_eq_getElem] at h
    exact h

/-- Conjugating a reduced word by a letter that cancels at neither end. -/
theorem red_conj {x : Lt r s} {W : List (Lt r s)} (hW : Red W) (hne : W ≠ [])
    (hh : W.head hne ≠ bar x) (hl : W.getLast hne ≠ x) : Red (x :: W ++ [bar x]) := by
  show List.IsChain _ ((x :: W) ++ [bar x])
  rw [List.isChain_append]
  refine ⟨List.isChain_cons.2 ⟨?_, hW⟩, List.isChain_singleton _, ?_⟩
  · intro y hy
    rw [List.head?_eq_some_head hne] at hy
    rw [← Option.some.inj hy]
    exact hh
  · intro a ha b hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    have ha' : a = W.getLast hne := by
      have h1 : (x :: W).getLast? = some (W.getLast hne) := by
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), List.getLast_cons hne]
      rw [h1] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    intro h
    exact hl (bar_injective h).symm

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

theorem ibar_cons (a : Lt r s) (u : List (Lt r s)) : ibar (a :: u) = ibar u ++ [bar a] := by
  simp [ibar]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-- A nonempty reduced word is `P ++ u ++ P⁻¹` with `u` cyclically reduced or one letter `m_j`. -/
theorem core_decomp : ∀ (n : ℕ) (w : List (Lt r s)), w.length = n → Red w → w ≠ [] →
    ∃ P u : List (Lt r s), u ≠ [] ∧ w = P ++ u ++ ibar P ∧
      (CycRed u ∨ ∃ j : Fin s, u = [Sum.inr j]) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hred hne
    by_cases hc : w.head hne ≠ bar (w.getLast hne)
    · exact ⟨[], w, hne, by simp, Or.inl (cycRed_of_red w hred hne hc)⟩
    · rw [not_not] at hc
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
      rcases List.eq_nil_or_concat' t with rfl | ⟨m, c, rfl⟩
      · rcases a with ⟨i, b⟩ | j
        · simp [bar] at hc
        · exact ⟨[], [Sum.inr j], by simp, by simp, Or.inr ⟨j, rfl⟩⟩
      · have hac : a = bar c := by simpa using hc
        subst hac
        have hmne : m ≠ [] := by
          rintro rfl
          have := (red_cons_cons.1 hred).1
          exact this (bar_bar c).symm
        have hredm : Red m := hred.infix ⟨[bar c], [c], by simp⟩
        obtain ⟨P, u, hu, hm, hcu⟩ :=
          ih m.length (by simp at hn; omega) m rfl hredm hmne
        refine ⟨bar c :: P, u, hu, ?_, hcu⟩
        rw [ibar_cons, bar_bar]
        conv_lhs => rw [hm]
        simp

/-! ## Conjugates of the involutions -/
/-- `g` has normal form `P ++ [m_j] ++ P⁻¹`. -/
def TDec (j : Fin s) (g : G r s) : Prop :=
  ∃ P : List (Lt r s), Red (P ++ [Sum.inr j] ++ ibar P) ∧
    wprod (P ++ [Sum.inr j] ++ ibar P) = g

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

theorem wprod_ibar (u : List (Lt r s)) : wprod (ibar u) = (wprod u)⁻¹ := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [ibar_cons, wprod_append, ih, wprod_cons a u, wprod_singleton, genL_bar]
    exact (mul_inv_rev (G := G r s) _ _).symm

theorem wprod_conj_cons (p : Lt r s) (W : List (Lt r s)) :
    wprod (p :: W ++ [bar p]) = genL p * wprod W * (genL p)⁻¹ := by
  rw [List.cons_append, wprod_cons, wprod_append, wprod_singleton, genL_bar]
  exact (mul_assoc _ _ _).symm

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem tdec_step {j : Fin s} {g : G r s} (x : Lt r s) (h : TDec j g) :
    TDec j (genL x * g * (genL x)⁻¹) := by
  obtain ⟨P, hred, rfl⟩ := h
  cases P with
  | cons p P =>
    by_cases hx : x = bar p
    · subst hx
      refine ⟨P, hred.infix ⟨[p], [bar p], by simp [ibar_cons]⟩, ?_⟩
      have e : (p :: P) ++ [Sum.inr j] ++ ibar (p :: P) =
          p :: (P ++ [Sum.inr j] ++ ibar P) ++ [bar p] := by simp [ibar_cons]
      rw [e, wprod_conj_cons, genL_bar]
      exact gid_conj_inv (H := G r s) _ _
    · have e : (x :: p :: P) ++ [Sum.inr j] ++ ibar (x :: p :: P) =
          x :: ((p :: P) ++ [Sum.inr j] ++ ibar (p :: P)) ++ [bar x] := by simp [ibar_cons]
      refine ⟨x :: p :: P, ?_, ?_⟩
      · rw [e]
        refine red_conj hred (by simp) ?_ ?_
        · simp only [List.cons_append, List.head_cons]
          intro h
          exact hx (by rw [h, bar_bar])
        · have e2 : (p :: P) ++ [Sum.inr j] ++ ibar (p :: P) =
              (p :: (P ++ [Sum.inr j] ++ ibar P)) ++ [bar p] := by simp [ibar_cons]
          simp only [e2, List.getLast_concat]
          intro h
          exact hx h.symm
      · rw [e, wprod_conj_cons]
  | nil =>
    by_cases hx : x = Sum.inr j
    · subst hx
      refine ⟨[], hred, ?_⟩
      simp only [ibar_nil, List.nil_append, List.append_nil, wprod_singleton]
      exact gid_self (H := G r s) _
    · have e : [x] ++ [Sum.inr j] ++ ibar [x] = x :: [Sum.inr j] ++ [bar x] := by simp [ibar]
      refine ⟨[x], ?_, ?_⟩
      · rw [e]
        refine red_conj (List.isChain_singleton _) (by simp) ?_ ?_
        · simp only [List.head_cons]
          intro h
          apply hx
          rw [← bar_bar x, ← h]
          rfl
        · simp only [List.getLast_singleton]
          exact fun h => hx h.symm
      · rw [e, wprod_conj_cons]
        simp only [ibar_nil, List.nil_append, List.append_nil, wprod_singleton]

theorem tdec_conj (j : Fin s) (a : G r s) : TDec j (a * genL (Sum.inr j) * a⁻¹) := by
  have key : ∀ w : List (Lt r s), TDec j (wprod w * genL (Sum.inr j) * (wprod w)⁻¹) := by
    intro w
    induction w with
    | nil =>
      refine ⟨[], List.isChain_singleton _, ?_⟩
      simp only [ibar_nil, List.nil_append, List.append_nil, wprod_singleton, wprod_nil]
      rw [g_inv_one, one_mul, mul_one]
    | cons x w ih =>
      have := tdec_step x ih
      convert this using 1
      rw [wprod_cons]
      exact gid_conj_mul (H := G r s) _ _ _
  have := key (nf a)
  rwa [wprod_nf] at this

/-- The normal form of a conjugate of `m_j`. -/
theorem torsion_nf (a : G r s) (j : Fin s) : ∃ P : List (Lt r s), Red P ∧
    nf (a * genL (Sum.inr j) * a⁻¹) = P ++ [Sum.inr j] ++ ibar P := by
  obtain ⟨P, hred, hw⟩ := tdec_conj j a
  refine ⟨P, red_left (red_left hred), ?_⟩
  rw [← hw]
  exact nf_wprod hred

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-! ## Non-reduced words are not shortest -/
theorem not_red_split {u : List (Lt r s)} (h : ¬ Red u) :
    ∃ x a y, u = x ++ a :: bar a :: y := by
  induction u with
  | nil => exact absurd red_nil h
  | cons a t ih =>
    cases t with
    | nil => exact absurd (List.isChain_singleton a) h
    | cons b t =>
      by_cases hb : b = bar a
      · exact ⟨[], a, t, by simp [hb]⟩
      · have : ¬ Red (b :: t) := fun h' => h (List.isChain_cons_cons.2 ⟨hb, h'⟩)
        obtain ⟨x, c, y, e⟩ := ih this
        exact ⟨a :: x, c, y, by simp [e]⟩

/-- A word of minimal length is reduced. -/
theorem red_of_length {u : List (Lt r s)} {g : G r s} (h : wprod u = g)
    (hl : u.length = len g) : Red u := by
  by_contra hr
  obtain ⟨x, a, y, rfl⟩ := not_red_split hr
  have h2 : wprod (x ++ y) = g := by
    rw [← h, wprod_append, wprod_append, wprod_cons, wprod_cons, genL_bar]
    exact (gid_cancel (H := G r s) _ _ _).symm
  have h3 := len_wprod_le (x ++ y)
  rw [h2] at h3
  simp at hl h3
  omega

/-- A word of length `len` of its product is the normal form. -/
theorem eq_nf_of_length {u : List (Lt r s)} {g : G r s} (h : wprod u = g)
    (hl : u.length = len g) : nf g = u := by
  rw [← h]
  exact nf_wprod (red_of_length h hl)

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-- The normal form of a reduced conjugate of a letter. -/
theorem nf_conj_letter {g b : G r s} {x : Lt r s} (hg : g = b * genL x * b⁻¹)
    (hl : len g = 2 * len b + 1) : nf g = nf b ++ [x] ++ ibar (nf b) := by
  apply eq_nf_of_length
  · rw [wprod_append, wprod_append, wprod_ibar, wprod_singleton, wprod_nf, hg]
  · rw [hl, len_eq_length_nf b]
    simp
    ring

theorem genL_inr_mul_self (j : Fin s) :
    genL (Sum.inr j : Lt r s) * genL (Sum.inr j) = 1 := by
  have h := genL_mul_genL_bar (r := r) (s := s) (Sum.inr j)
  exact h

theorem genL_ne_one (x : Lt r s) : genL x ≠ 1 := by
  intro h
  have := nf_genL x
  rw [h, nf_one] at this
  exact List.cons_ne_nil _ _ this.symm

/-- Uniqueness of the reduced expression of a conjugate of `m_i`. -/
theorem torsion_key {g : G r s} {P : List (Lt r s)} {i : Fin s}
    (hnf : nf g = P ++ [Sum.inr i] ++ ibar P) (b : G r s) (k : Fin s)
    (hg : g = b * genL (Sum.inr k) * b⁻¹) (hl : len g = 2 * len b + 1) :
    nf b = P ∧ k = i := by
  have e := nf_conj_letter hg hl
  rw [hnf] at e
  have hlen : P.length = (nf b).length := by
    have := congrArg List.length e
    simp at this
    omega
  rw [List.append_assoc, List.append_assoc] at e
  obtain ⟨h3, h4⟩ := List.append_inj e hlen
  refine ⟨h3.symm, ?_⟩
  have := (List.cons.inj h4).1
  exact (Sum.inr.inj this).symm

/-! ## The stubs -/

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem act_genL {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (a : Lt 0 r) :
    homI τ (genL a) = letterPermI τ a := by
  rcases a with ⟨i, b⟩ | j
  · exact i.elim0
  · simp only [homI, genL, letterPermI, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    show (τ j).1 ^ (1 : ZMod 2).val = _
    simp [ZMod.val_one]

theorem act_wprod {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (u : List (Lt 0 r)) :
    homI τ (wprod u) = wordPermI τ u := by
  induction u with
  | nil => simp [wordPermI]
  | cons a t ih =>
    rw [wprod_cons, map_mul, ih, act_genL]
    simp [wordPermI]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias act_wprod := RandomInvolutions.Dev.PartF.act_wprod

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-- Every nontrivial element is a reduced conjugate of a cyclically reduced word or of a letter
`m_i`. -/
theorem exists_cyc_rep (g : G 0 r) (hg : g ≠ 1) :
    ∃ (a : G 0 r) (u : List (Lt 0 r)), u ≠ [] ∧ g = a * wprod u * a⁻¹ ∧
      len g = 2 * len a + u.length ∧ (CycRed u ∨ ∃ i : Fin r, u = [Sum.inr i]) := by
  have hne : nf g ≠ [] := fun h => hg (nf_eq_nil_iff.1 h)
  obtain ⟨P, u, hu, hw, hcu⟩ := core_decomp _ (nf g) rfl (red_nf g) hne
  have hP : Red P := by
    have := red_nf g
    rw [hw] at this
    exact red_left (red_left this)
  refine ⟨wprod P, u, hu, ?_, ?_, hcu⟩
  · have h1 : wprod (P ++ u ++ ibar P) = g := by rw [← hw, wprod_nf]
    rw [← h1, wprod_append, wprod_append, wprod_ibar]
  · rw [len_eq_length_nf g, hw, len_wprod_of_red hP]
    simp
    omega

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias exists_cyc_rep := RandomInvolutions.Dev.PartF.exists_cyc_rep

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
lemma homK_mI {N : ℕ} {κ : Fin r → ℕ} (τ : OmK r N κ) (i : Fin r) :
    homK τ (mI i) = (τ i).1.1 := by
  have h := act_wprod (fun i => (τ i).1) [Sum.inr i]
  rw [wprod_single] at h
  simpa [homK, wordPermI, letterPermI] using h

lemma expFixK_torsion {N : ℕ} {κ : Fin r → ℕ} (hA : AdmK N κ) (a : G 0 r) (i : Fin r) :
    expFixK r N κ (a * mI i * a⁻¹) = κ i := by
  rw [expFixK_conj]
  unfold expFixK expFixOn
  have := nonempty_omK N κ hA
  have h : ∀ τ : OmK r N κ, (fixCount (homK τ (mI i)) : ℝ) = κ i := fun τ => by
    rw [homK_mI, (τ i).2]
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  have h0 : (Fintype.card (OmK r N κ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-! ## The model at `κ = 0` is the matching model -/
lemma no_fix_of_fixCount {N : ℕ} (σ : Equiv.Perm (Fin N)) (h : fixCount σ = 0) (x : Fin N) :
    σ x ≠ x := by
  unfold fixCount at h
  rw [card_eq_zero, filter_eq_empty_iff] at h
  exact h (mem_univ x)

lemma fixCount_of_no_fix {N : ℕ} (σ : Equiv.Perm (Fin N)) (h : ∀ x, σ x ≠ x) :
    fixCount σ = 0 := by
  unfold fixCount
  rw [card_eq_zero, filter_eq_empty_iff]
  exact fun x _ => h x

/-- A sample of the conditional model with no fixed points, as a sample of the matching model. -/
def toOm {N : ℕ} (τ : OmK r N (fun _ => 0)) : Om 0 r N :=
  (fun i => i.elim0,
    fun j => ⟨(τ j).1.1, fun x => ⟨(τ j).1.2 x, no_fix_of_fixCount _ (τ j).2 x⟩⟩)

def omEquiv (r N : ℕ) : OmK r N (fun _ => 0) ≃ Om 0 r N where
  toFun := toOm
  invFun ω := fun j => ⟨⟨(ω.2 j).1, fun x => ((ω.2 j).2 x).1⟩,
    fixCount_of_no_fix _ fun x => ((ω.2 j).2 x).2⟩
  left_inv τ := by
    funext j
    exact Subtype.ext (Subtype.ext rfl)
  right_inv ω := by
    refine Prod.ext (funext fun i => i.elim0) (funext fun j => Subtype.ext rfl)

lemma act_toOm {N : ℕ} (τ : OmK r N (fun _ => 0)) : act (toOm τ) = homK τ := by
  unfold act homK homI
  have h1 : FreeGroup.lift (toOm τ).1 = (1 : FreeGroup (Fin 0) →* Equiv.Perm (Fin N)) :=
    FreeGroup.ext_hom _ _ fun i => i.elim0
  have h2 : (fun j => invHom ((toOm τ).2 j)) = fun i => invHomI (τ i).1 := by
    funext j
    exact MonoidHom.ext fun a => rfl
  rw [h1, h2]

lemma expFixK_zero (N : ℕ) (g : G 0 r) :
    expFixK r N (fun _ => 0) g = expFix 0 r N g := by
  unfold expFixK expFixOn expFix
  have hc : (Fintype.card (OmK r N (fun _ => 0)) : ℝ) = (Fintype.card (Om 0 r N) : ℝ) := by
    exact_mod_cast Fintype.card_congr (omEquiv r N)
  rw [hc]
  congr 1
  refine Fintype.sum_equiv (omEquiv r N) _ _ fun τ => ?_
  show _ = ((fixCount (act (toOm τ) g) : ℕ) : ℝ)
  rw [act_toOm]

/-! ## The limit of the sum over colourings -/
/-- The limit of `N (wt c - [c first order])`. -/
def Tc (u : List (Lt 0 r)) (κ : Fin r → ℕ) (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ :=
  if nv c = Ecount u c + Fcount u c then
    c0f (nv c) (eK u c) (fK u c) - ∑ i, (eK u c i : ℝ) * κ i
  else if nv c + 1 = Ecount u c + Fcount u c then ∏ i, ((κ i).descFactorial (fK u c i) : ℝ)
  else 0

lemma tendsto_two' (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) (h : v = ∑ i, e i + ∑ i, f i) :
    Tendsto (fun N : ℕ => (N : ℝ) * (wtF N κ v e f - ∏ i, ((κ i).descFactorial (f i) : ℝ)))
      atTop (𝓝 ((∏ i, ((κ i).descFactorial (f i) : ℝ)) *
        (c0f v e f - ∑ i, (e i : ℝ) * κ i))) := by
  have h1 := (tendsto_Rf_slope κ v e f).const_mul (∏ i, ((κ i).descFactorial (f i) : ℝ))
  refine h1.congr' ?_
  filter_upwards [ev_big v e f] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [wtF_eq κ v e f N hN.1 hN.2.1 hN.2.2, ← h]
  field_simp

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-! ## The counting formula -/
theorem expect_formula_aux {r : ℕ} (u : List (Lt 0 r)) (N : ℕ) (κ : Fin r → ℕ)
    (hA : AdmK N κ) :
    expFixK r N κ (wprod u) =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) =>
        canon c = c).filter (GoodL u), wtK u N κ c := by
  have h1 : (∑ ω : OmK r N κ, (fixCount (wordPermI (fun i => (ω i).1) u) : ℝ)) =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c),
        (N.descFactorial (nv c) : ℝ) * W u N κ c := by
    rw [sum_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
      (t := univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c)
      (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
    refine sum_congr rfl fun c hc => ?_
    have hc := (mem_filter.1 hc).2
    have hG : ∀ x ∈ univ.filter fun x : Fin (u.length + 1) → Fin N => canon x = c,
        W u N κ x = W u N κ c := by
      intro x hx
      have hx := (mem_filter.1 hx).2
      rw [← hx]
      conv_lhs => rw [← comp_canon x]
      exact W_comp u (canon x) x (injOn_canon x) N κ
    rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, nsmul_eq_mul]
  have hI : (∏ i, (Fintype.card (InvK N (κ i)) : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => card_invK_ne_zero N (κ i) (hA i).1 (hA i).2
  have hcard : (Fintype.card (OmK r N κ) : ℝ) = ∏ i, (Fintype.card (InvK N (κ i)) : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
  have h2 : ∀ ω : OmK r N κ, homK ω (wprod u) = wordPermI (fun i => (ω i).1) u :=
    fun ω => RandomInvolutions.Dev.act_wprod _ u
  unfold expFixK expFixOn
  simp only [h2]
  rw [h1, sum_filter (GoodL u), sum_div, hcard]
  refine sum_congr rfl fun c _ => ?_
  by_cases hg : GoodL u c
  · rw [if_pos hg]
    unfold W wtK wtF
    rw [if_pos hg, prod_mul_distrib]
    unfold Wf eK fK
    set A := (N.descFactorial (nv c) : ℝ)
    set P := ∏ i, (Fintype.card (InvK N (κ i)) : ℝ)
    field_simp
  · rw [if_neg hg]
    unfold W
    rw [if_neg hg]
    simp

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
/-- `E_{N,κ}[fix(wprod u)] = ∑_c wt(c)` over canonical good colourings with loops. -/
theorem expect_formulaK (u : List (Lt 0 r)) (N : ℕ) (κ : Fin r → ℕ) (hN : 1 ≤ N)
    (hA : AdmK N κ) (hL : u.length ≤ N) :
    expFixK r N κ (wprod u) = ∑ c ∈ CGL u, wtK u N κ c := by
  have _ := hN
  have _ := hL
  rw [expect_formula_aux u N κ hA]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [CGL, mem_filter]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias expect_formulaK := RandomInvolutions.Dev.PartC2.expect_formulaK

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

theorem wprod_rep (Z : List (Lt r s)) (k : ℕ) : wprod (rep Z k) = wprod Z ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, wprod_append, ih, pow_succ']

theorem rep_getElem? (Z : List (Lt r s)) (k i : ℕ) (hi : i < k * Z.length) :
    (rep Z k)[i]? = Z[i % Z.length]? := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
    rw [rep_succ]
    by_cases h : i < Z.length
    · rw [List.getElem?_append_left h, Nat.mod_eq_of_lt h]
    · have h' : Z.length ≤ i := by omega
      rw [List.getElem?_append_right h', ih _ (by rw [Nat.succ_mul] at hi; omega),
        ← Nat.mod_eq_sub_mod h']

theorem rep_getElem (Z : List (Lt r s)) (k i : ℕ) (h : i < (rep Z k).length)
    (h' : i % Z.length < Z.length) : (rep Z k)[i] = Z[i % Z.length] := by
  have := rep_getElem? Z k i (by simpa using h)
  rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h'] at this
  exact Option.some.inj this

/-- If `Z ++ Z` is reduced then all powers of `Z` are reduced. -/
theorem red_rep {Z : List (Lt r s)} (h : Red (Z ++ Z)) (k : ℕ) : Red (rep Z k) := by
  by_cases hZ : Z = []
  · subst hZ
    rw [rep_nil]
    exact red_nil
  induction k with
  | zero => rw [rep_zero]; exact red_nil
  | succ k ih =>
    cases k with
    | zero => simpa [rep_succ] using red_left h
    | succ k =>
      rw [rep_succ]
      rw [Red, List.isChain_append] at h ⊢
      refine ⟨h.1, ih, ?_⟩
      intro x hx y hy
      rw [rep_succ, List.head?_append_of_ne_nil _ hZ] at hy
      exact h.2.2 x hx y hy

/-- `CycRed` gives that the square is reduced. -/
theorem red_sq_of_cycRed {u : List (Lt r s)} (hc : CycRed u) : Red (u ++ u) := by
  have e : u ++ u = rep u 2 := by simp [rep_succ]
  rw [e, Red, List.isChain_iff_getElem]
  intro i hi
  have hL : 0 < u.length := by
    rcases Nat.eq_zero_or_pos u.length with h0 | h0
    · simp [h0] at hi
    · exact h0
  have h1 := rep_getElem u 2 i (by omega) (Nat.mod_lt _ hL)
  have h2 := rep_getElem u 2 (i + 1) hi (Nat.mod_lt _ hL)
  rw [h1, h2]
  have := hc ⟨i % u.length, Nat.mod_lt _ hL⟩
  simp only [List.get_eq_getElem] at this
  convert this using 2
  simp [Nat.add_mod]

/-- If `Z ++ Z` is reduced and `Z ≠ []`, the element `wprod Z` has infinite order. -/
theorem wprod_pow_ne_one {Z : List (Lt r s)} (h : Red (Z ++ Z)) (hZ : Z ≠ []) {k : ℕ}
    (hk : k ≠ 0) : wprod Z ^ k ≠ 1 := by
  intro h1
  rw [← wprod_rep] at h1
  have := congrArg List.length (eq_nil_of_red_of_wprod (red_rep h k) h1)
  simp at this
  rcases this with h | h
  · exact hk h
  · exact hZ h

theorem nf_of_triple {g a z : G r s} {k : ℕ} (hg : g = a * z ^ k * a⁻¹)
    (hl : len g = 2 * len a + k * len z) : nf g = nf a ++ rep (nf z) k ++ ibar (nf a) := by
  apply eq_nf_of_length
  · rw [wprod_append, wprod_append, wprod_ibar, wprod_rep, wprod_nf, wprod_nf, hg]
  · rw [hl, len_eq_length_nf a, len_eq_length_nf z]
    simp
    ring

/-- In a reduced expression `g = a z^k a⁻¹` with `k ≥ 2`, the word of `z` is cyclically
reduced. -/
theorem red_sq_of_triple {g a z : G r s} {k : ℕ} (hk : 2 ≤ k) (hg : g = a * z ^ k * a⁻¹)
    (hl : len g = 2 * len a + k * len z) : Red (nf z ++ nf z) := by
  have h := red_nf g
  rw [nf_of_triple hg hl] at h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine h.infix ⟨nf a, rep (nf z) k ++ ibar (nf a), ?_⟩
  rw [show 2 + k = k + 1 + 1 by ring, rep_succ, rep_succ]
  simp

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem cfun_torsion (a : G 0 r) (i : Fin r) : cfun (a * mI i * a⁻¹) = -1 := by
  show cfun (a * genL (Sum.inr i) * a⁻¹) = -1
  have hmm : genL (Sum.inr i : Lt 0 r) * genL (Sum.inr i) = 1 := genL_inr_mul_self i
  have hm1 : genL (Sum.inr i : Lt 0 r) ≠ 1 := genL_ne_one _
  have hg1 : a * genL (Sum.inr i) * a⁻¹ ≠ 1 := fun h =>
    hm1 (gid_conj_eq_one (H := G 0 r) _ _ h)
  have hgg : a * genL (Sum.inr i) * a⁻¹ * (a * genL (Sum.inr i) * a⁻¹) = 1 :=
    gid_conj_sq (H := G 0 r) _ _ hmm
  generalize a * genL (Sum.inr i) * a⁻¹ = g at hg1 hgg ⊢
  have hempty : IsEmpty {t : ℕ × G 0 r × G 0 r // 2 ≤ t.1 ∧ t.2.1 ≠ 1 ∧
      g = t.2.2 * t.2.1 ^ t.1 * t.2.2⁻¹ ∧ len g = 2 * len t.2.2 + t.1 * len t.2.1} := ⟨by
    rintro ⟨⟨k, z, a'⟩, hk, hz, hg, hl⟩
    dsimp only at hk hz hg hl
    have h2 := red_sq_of_triple hk hg hl
    have hZ : nf z ≠ [] := fun h => hz (nf_eq_nil_iff.1 h)
    rw [hg] at hgg
    have h3 : z ^ (k + k) = 1 := gid_conj_pow_sq (H := G 0 r) a' z k hgg
    have h4 := wprod_pow_ne_one h2 hZ (k := k + k) (by omega)
    rw [wprod_nf] at h4
    exact h4 h3⟩
  unfold cfun
  rw [if_pos ⟨hg1, hgg⟩, Nat.card_of_isEmpty]
  simp

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias cfun_torsion := RandomInvolutions.Dev.PartF.cfun_torsion

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem bcount_torsion (a : G 0 r) (i k : Fin r) :
    Bcount k (a * mI i * a⁻¹) = if k = i then 1 else 0 := by
  obtain ⟨P, hP, hnf⟩ : ∃ P : List (Lt 0 r), Red P ∧
      nf (a * mI i * a⁻¹) = P ++ [Sum.inr i] ++ ibar P := torsion_nf a i
  generalize a * mI i * a⁻¹ = g at hnf ⊢
  have key : ∀ (b : G 0 r) (k : Fin r), g = b * mI k * b⁻¹ → len g = 2 * len b + 1 →
      nf b = P ∧ k = i := fun b k hg hl => torsion_key hnf b k hg hl
  unfold Bcount
  split_ifs with hk
  · subst hk
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨wprod P, ?_, ?_⟩⟩⟩
    · rw [← wprod_nf x.1, ← wprod_nf y.1, (key x.1 k x.2.1 x.2.2).1,
        (key y.1 k y.2.1 y.2.2).1]
    · have h1 : wprod (P ++ [Sum.inr k] ++ ibar P) = g := by rw [← hnf, wprod_nf]
      rw [← h1, wprod_append, wprod_append, wprod_ibar, wprod_singleton]
      rfl
    · rw [len_eq_length_nf g, hnf, len_wprod_of_red hP]
      simp
      omega
  · haveI : IsEmpty {b : G 0 r // g = b * mI k * b⁻¹ ∧ len g = 2 * len b + 1} :=
      ⟨fun x => hk (key x.1 k x.2.1 x.2.2).2⟩
    exact Nat.card_of_isEmpty

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias bcount_torsion := RandomInvolutions.Dev.PartF.bcount_torsion

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem bcount_cyc (a : G 0 r) (u : List (Lt 0 r)) (hne : u ≠ []) (hc : CycRed u)
    (hlen : len (a * wprod u * a⁻¹) = 2 * len a + u.length) (i : Fin r) :
    Bcount i (a * wprod u * a⁻¹) = 0 := by
  unfold Bcount
  haveI : IsEmpty {b : G 0 r // a * wprod u * a⁻¹ = b * mI i * b⁻¹ ∧
      len (a * wprod u * a⁻¹) = 2 * len b + 1} := ⟨by
    rintro ⟨b, hg, -⟩
    have gg : b * mI i * b⁻¹ * (b * mI i * b⁻¹) = 1 :=
      gid_conj_sq (H := G 0 r) _ _ (genL_inr_mul_self i)
    rw [← hg] at gg
    have h2 : wprod u * wprod u = 1 := gid_sq_conj (H := G 0 r) _ _ gg
    have h3 := wprod_pow_ne_one (red_sq_of_cycRed hc) hne (k := 2) (by norm_num)
    exact h3 (by rw [pow_two]; exact h2)⟩
  exact Nat.card_of_isEmpty

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias bcount_cyc := RandomInvolutions.Dev.PartF.bcount_cyc

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem c2count_torsion (a : G 0 r) (k i j : Fin r) : C2count i j (a * mI k * a⁻¹) = 0 := by
  obtain ⟨P, hP, hnf⟩ : ∃ P : List (Lt 0 r), Red P ∧
      nf (a * mI k * a⁻¹) = P ++ [Sum.inr k] ++ ibar P := torsion_nf a k
  generalize a * mI k * a⁻¹ = g at hnf ⊢
  have hodd : len g = 2 * P.length + 1 := by
    rw [len_eq_length_nf g, hnf]
    simp
    omega
  unfold C2count
  haveI : IsEmpty {p : G 0 r × G 0 r × G 0 r × ℕ // 1 ≤ p.2.2.2 ∧
      g = p.1 * (p.2.1 * mI j * p.2.1⁻¹ * (p.2.2.1 * mI i * p.2.2.1⁻¹)) ^ p.2.2.2 * p.1⁻¹ ∧
      len g = 2 * len p.1 + p.2.2.2 * (2 * len p.2.1 + 2 * len p.2.2.1 + 2)} := ⟨by
    rintro ⟨⟨b, ρ, σ, t⟩, -, -, hl⟩
    dsimp only at hl
    have e : t * (2 * len ρ + 2 * len σ + 2) = 2 * (t * (len ρ + len σ + 1)) := by ring
    omega⟩
  exact Nat.card_of_isEmpty

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias c2count_torsion := RandomInvolutions.Dev.PartF.c2count_torsion

end RandomInvolutions.Dev
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3a.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3a.F1
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3b.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3b.F1
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
/-!
# Part W, generic walks: pair graphs of periodic walks with loops

A walk is `x : ℕ → α` with colours `a : ℕ → Fin r`; step `t` is a *loop* when `x t = x (t+1)` and
a *pair* otherwise.  We count vertices against coloured pairs (`count`), and for periodic,
cyclically reduced walks whose pair graph is a tree (`TW`) we show that there are at least two
loops (`TW.two_loops`) and, when there are exactly two, that the walk goes back and forth on a
path (`TW.structure`).
-/
/-! ## Folding arithmetic -/
/-- The phase of time `τ` in a back-and-forth walk of period `2d` whose first loop is at `p`. -/
def mm (p d τ : ℕ) : ℕ := (τ + (2 * d - 1 - p)) % (2 * d)

/-- The vertex (in `[0, d)`) at time `τ`. -/
def fv (p d τ : ℕ) : ℕ := if mm p d τ < d then mm p d τ else 2 * d - 1 - mm p d τ

/-- The label (in `[0, d]`) of step `τ`: `0` and `d` are the loops, `k` joins `k - 1` and `k`. -/
def lb (p d τ : ℕ) : ℕ := if mm p d τ < d then mm p d τ + 1 else 2 * d - 1 - mm p d τ

lemma succ_mod (n M : ℕ) (hM : 0 < M) :
    (n + 1) % M = if n % M + 1 < M then n % M + 1 else 0 := by
  have h1 := Nat.div_add_mod n M
  have h2 := Nat.mod_lt n hM
  split_ifs with h
  · have e : n + 1 = (n / M) * M + (n % M + 1) := by rw [Nat.mul_comm]; omega
    rw [e, Nat.mul_add_mod_of_lt h]
  · have e : n + 1 = M * (n / M + 1) := by rw [Nat.mul_add, mul_one]; omega
    rw [e, Nat.mul_mod_right]

lemma add_mod_of_dvd {M B : ℕ} (A : ℕ) (h : M ∣ B) : (A + B) % M = A % M := by
  obtain ⟨c, rfl⟩ := h
  exact Nat.add_mul_mod_self_left A M c

lemma dvd_of_add_pred_mod {L M : ℕ} (hM : 0 < M) (h : (L + (M - 1)) % M = M - 1) : M ∣ L := by
  apply Nat.dvd_of_mod_eq_zero
  by_contra h0
  have h1 := Nat.div_add_mod L M
  have h2 := Nat.mod_lt L hM
  have e : L + (M - 1) = (L / M + 1) * M + (L % M - 1) := by
    rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega
  rw [e, Nat.mul_add_mod_of_lt (by omega)] at h
  omega

lemma mm_lt {p d τ : ℕ} (hd : 1 ≤ d) : mm p d τ < 2 * d := Nat.mod_lt _ (by omega)

lemma mm_succ {p d : ℕ} (hd : 1 ≤ d) (τ : ℕ) :
    mm p d (τ + 1) = if mm p d τ + 1 < 2 * d then mm p d τ + 1 else 0 := by
  unfold mm
  rw [show τ + 1 + (2 * d - 1 - p) = τ + (2 * d - 1 - p) + 1 by omega]
  exact succ_mod _ _ (by omega)

lemma fv_lt {p d τ : ℕ} (hd : 1 ≤ d) : fv p d τ < d := by
  have := mm_lt (p := p) (τ := τ) hd
  unfold fv; split_ifs <;> omega

lemma lb_le {p d τ : ℕ} (hd : 1 ≤ d) : lb p d τ ≤ d := by
  have := mm_lt (p := p) (τ := τ) hd
  unfold lb; split_ifs <;> omega

/-- Each step is a loop (label `0` at vertex `0`, or label `d` at vertex `d - 1`) or moves along
the pair of its label. -/
lemma fold_cases {p d : ℕ} (hd : 1 ≤ d) (τ : ℕ) :
    (fv p d τ = fv p d (τ + 1) ∧
      ((lb p d τ = 0 ∧ fv p d τ = 0) ∨ (lb p d τ = d ∧ fv p d τ = d - 1))) ∨
    (1 ≤ lb p d τ ∧ lb p d τ ≤ d - 1 ∧
      ((fv p d τ + 1 = lb p d τ ∧ fv p d (τ + 1) = lb p d τ) ∨
        (fv p d τ = lb p d τ ∧ fv p d (τ + 1) + 1 = lb p d τ))) := by
  have h1 := mm_succ (p := p) hd τ
  have h2 := mm_lt (p := p) (τ := τ) hd
  simp only [fv, lb]
  rw [h1]
  generalize mm p d τ = m at *
  split_ifs <;> omega

/-- The transition rule: the vertex and the label of the previous step determine the step. -/
lemma fold_step {p d : ℕ} (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    (fv p d n = 0 → lb p d (n - 1) ≠ 0 → lb p d n = 0 ∧ fv p d (n + 1) = fv p d n) ∧
    (fv p d n = d - 1 → lb p d (n - 1) ≠ d → lb p d n = d ∧ fv p d (n + 1) = fv p d n) ∧
    (fv p d n + 1 ≤ d - 1 → lb p d (n - 1) ≠ fv p d n + 1 →
      lb p d n = fv p d n + 1 ∧ fv p d (n + 1) = fv p d n + 1) ∧
    (1 ≤ fv p d n → lb p d (n - 1) ≠ fv p d n →
      lb p d n = fv p d n ∧ fv p d (n + 1) = fv p d n - 1) := by
  have h1 := mm_succ (p := p) hd (n - 1)
  rw [show n - 1 + 1 = n by omega] at h1
  have h2 := mm_succ (p := p) hd n
  have h3 := mm_lt (p := p) (τ := n - 1) hd
  simp only [fv, lb]
  generalize mm p d (n + 1) = m2 at *
  generalize mm p d n = m1 at *
  generalize mm p d (n - 1) = m0 at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ha hb <;> split_ifs at * <;> omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {α : Type*} [DecidableEq α]
/-! ## Walks -/
/-- The vertices visited at times `≤ k`. -/
def UU (x : ℕ → α) (k : ℕ) : Finset α := (range (k + 1)).image x

/-- The coloured pair of step `t`. -/
def pe (a : ℕ → Fin r) (x : ℕ → α) (t : ℕ) : Fin r × Sym2 α := (a t, s(x t, x (t + 1)))

/-- The coloured pairs of the non-loop steps `< k`. -/
def EE (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Finset (Fin r × Sym2 α) :=
  ((range k).filter fun t => x t ≠ x (t + 1)).image (pe a x)

/-- The coloured loops of the loop steps `< k`. -/
def LL (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Finset (Fin r × α) :=
  ((range k).filter fun t => x t = x (t + 1)).image fun t => (a t, x t)

/-- Step `k` is a closing step: a new pair to an old vertex. -/
def closing (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Prop :=
  x k ≠ x (k + 1) ∧ x (k + 1) ∈ UU x k ∧ pe a x k ∉ EE a x k

/-- `x t` was not visited before time `t`. -/
def newAt (x : ℕ → α) (t : ℕ) : Prop := ∀ s < t, x s ≠ x t

lemma mem_UU {x : ℕ → α} {k j : ℕ} (h : j ≤ k) : x j ∈ UU x k :=
  mem_image_of_mem _ (mem_range.2 (by omega))

lemma UU_succ (x : ℕ → α) (k : ℕ) : UU x (k + 1) = insert (x (k + 1)) (UU x k) := by
  simp [UU, range_add_one, image_insert]

lemma EE_succ (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) :
    EE a x (k + 1) = if x k = x (k + 1) then EE a x k else insert (pe a x k) (EE a x k) := by
  unfold EE
  rw [range_add_one, filter_insert]
  by_cases h : x k = x (k + 1)
  · rw [if_neg (not_not.2 h), if_pos h]
  · rw [if_pos h, if_neg h, image_insert]

omit [DecidableEq α] in
lemma pe_eq {a : ℕ → Fin r} {x : ℕ → α} {s t : ℕ} :
    pe a x s = pe a x t ↔ a s = a t ∧
      ((x s = x t ∧ x (s + 1) = x (t + 1)) ∨ (x s = x (t + 1) ∧ x (s + 1) = x t)) := by
  simp [pe]

lemma count (a : ℕ → Fin r) (x : ℕ → α) :
    ∀ k, (UU x k).card + ((range k).filter (closing a x)).card = (EE a x k).card + 1
  | 0 => by simp [UU, EE]
  | k + 1 => by
      have ih := count a x k
      have hk : k ∉ range k := by simp
      rw [UU_succ, EE_succ, range_add_one, filter_insert]
      by_cases hl : x k = x (k + 1)
      · have hx : x (k + 1) ∈ UU x k := hl ▸ mem_UU le_rfl
        have hc : ¬ closing a x k := fun h => h.1 hl
        rw [if_neg hc, insert_eq_of_mem hx, if_pos hl]; exact ih
      · rw [if_neg hl]
        by_cases hx : x (k + 1) ∈ UU x k
        · by_cases he : pe a x k ∈ EE a x k
          · have hc : ¬ closing a x k := fun h => h.2.2 he
            rw [if_neg hc, insert_eq_of_mem hx, insert_eq_of_mem he]; exact ih
          · have hc : closing a x k := ⟨hl, hx, he⟩
            rw [if_pos hc, insert_eq_of_mem hx, card_insert_of_notMem he,
              card_insert_of_notMem (fun h => hk (mem_filter.1 h).1)]
            omega
        · have he : pe a x k ∉ EE a x k := by
            intro h
            obtain ⟨s', hs, hse⟩ := mem_image.1 h
            have hs := mem_range.1 (mem_filter.1 hs).1
            rcases pe_eq.1 hse with ⟨-, ⟨-, h3⟩ | ⟨h3, -⟩⟩
            · exact hx (h3 ▸ mem_UU (by omega))
            · exact hx (h3 ▸ mem_UU (by omega))
          have hc : ¬ closing a x k := fun h => hx h.2.1
          rw [if_neg hc, card_insert_of_notMem hx, card_insert_of_notMem he]
          omega

/-- The pair graph is connected. -/
theorem card_UU_le (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : (UU x k).card ≤ (EE a x k).card + 1 := by
  have := count a x k
  omega

/-! ### Periodicity -/
omit [DecidableEq α] in
lemma per_mul {β : Type*} {x : ℕ → β} {L : ℕ} (h : ∀ t, x (t + L) = x t) (t q : ℕ) :
    x (t + q * L) = x t := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← add_assoc, h, ih]

omit [DecidableEq α] in
lemma per_mod {β : Type*} {x : ℕ → β} {L : ℕ} (h : ∀ t, x (t + L) = x t) (t : ℕ) :
    x t = x (t % L) := by
  have := per_mul h (t % L) (t / L)
  rw [Nat.mod_add_div'] at this
  exact this

omit [DecidableEq α] in
lemma per_mod_succ {β : Type*} {x : ℕ → β} {L : ℕ} (h : ∀ t, x (t + L) = x t) (t : ℕ) :
    x (t + 1) = x (t % L + 1) := by
  have := per_mul h (t % L + 1) (t / L)
  rw [show t % L + 1 + t / L * L = t % L + t / L * L + 1 by omega, Nat.mod_add_div'] at this
  exact this

/-- A periodic, cyclically reduced walk without closing steps (from any origin): its pair graph
is a tree. -/
structure TW (L : ℕ) (a : ℕ → Fin r) (x : ℕ → α) : Prop where
  hL : 0 < L
  px : ∀ t, x (t + L) = x t
  pa : ∀ t, a (t + L) = a t
  hcr : ∀ t, a (t + 1) ≠ a t
  hnc : ∀ s k, ¬ closing (fun t => a (s + t)) (fun t => x (s + t)) k

/-- A periodic cyclically reduced walk with `v = e + 1` is a tree walk. -/
theorem TW.mk' {L : ℕ} {a : ℕ → Fin r} {x : ℕ → α} (hL : 0 < L) (px : ∀ t, x (t + L) = x t)
    (pa : ∀ t, a (t + L) = a t) (hcr : ∀ t, a (t + 1) ≠ a t)
    (hve : ((range L).image x).card = (EE a x L).card + 1) : TW L a x := by
  refine ⟨hL, px, pa, hcr, fun s k hcl => ?_⟩
  set K := k + 1 + L + s * L with hK
  have hc := count (fun t => a (s + t)) (fun t => x (s + t)) K
  have hU : UU (fun t => x (s + t)) K = (range L).image x := by
    ext y
    simp only [UU, mem_image, mem_range]
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨(s + t) % L, Nat.mod_lt _ hL, (per_mod px _).symm⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t + s * L - s, ?_, ?_⟩
      · have : s ≤ s * L := Nat.le_mul_of_pos_right s hL
        omega
      · have : s ≤ s * L := Nat.le_mul_of_pos_right s hL
        rw [show s + (t + s * L - s) = t + s * L by omega]
        exact per_mul px t s
  have hE : EE (fun t => a (s + t)) (fun t => x (s + t)) K = EE a x L := by
    ext e
    simp only [EE, mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨t, ⟨-, hne⟩, rfl⟩
      refine ⟨(s + t) % L, ⟨Nat.mod_lt _ hL, ?_⟩, ?_⟩
      · rw [← per_mod px, ← per_mod_succ px]; exact hne
      · simp only [pe]
        rw [← per_mod px, ← per_mod_succ px, ← per_mod pa]
        rfl
    · rintro ⟨t, ⟨ht, hne⟩, rfl⟩
      have hs : s ≤ s * L := Nat.le_mul_of_pos_right s hL
      have e1 : s + (t + s * L - s) = t + s * L := by omega
      have e2 : s + (t + s * L - s + 1) = t + 1 + s * L := by omega
      refine ⟨t + s * L - s, ⟨by omega, ?_⟩, ?_⟩
      · show x (s + (t + s * L - s)) ≠ x (s + (t + s * L - s + 1))
        rw [e1, e2, per_mul px, per_mul px]; exact hne
      · simp only [pe]
        rw [e1, e2, per_mul px, per_mul px, per_mul pa]
  rw [hU, hE, hve] at hc
  have h0 : ((range K).filter (closing (fun t => a (s + t)) (fun t => x (s + t)))).card = 0 := by
    omega
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  exact h0 (mem_range.2 (by omega)) hcl

end RandomInvolutions.Dev.PartW
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {α : Type*} [DecidableEq α]
namespace TW
variable {L : ℕ} {a : ℕ → Fin r} {x : ℕ → α}
lemma shift (h : TW L a x) (s : ℕ) : TW L (fun t => a (s + t)) (fun t => x (s + t)) := by
  refine ⟨h.hL, fun t => ?_, fun t => ?_, fun t => ?_, fun s' k => ?_⟩
  · rw [← add_assoc]; exact h.px _
  · rw [← add_assoc]; exact h.pa _
  · exact h.hcr (s + t)
  · have e1 : (fun t => a (s + (s' + t))) = fun t => a (s + s' + t) := by
      funext t; rw [add_assoc]
    have e2 : (fun t => x (s + (s' + t))) = fun t => x (s + s' + t) := by
      funext t; rw [add_assoc]
    rw [e1, e2]
    exact h.hnc (s + s') k

lemma hnc0 (h : TW L a x) (k : ℕ) : ¬ closing a x k := by
  have := h.hnc 0 k
  simpa using this

/-- After a new vertex, a pair step leads to a new vertex. -/
lemma g1 (h : TW L a x) {t : ℕ} (hnew : newAt x t) (hl : x t ≠ x (t + 1)) : newAt x (t + 1) := by
  intro s hs heq
  have hin : x (t + 1) ∈ UU x t := heq ▸ mem_UU (by omega)
  have he : pe a x t ∈ EE a x t := by
    by_contra h'; exact h.hnc0 t ⟨hl, hin, h'⟩
  obtain ⟨s', hs', hse⟩ := mem_image.1 he
  rw [mem_filter, mem_range] at hs'
  rcases pe_eq.1 hse with ⟨h1, ⟨h2, -⟩ | ⟨h2, h3⟩⟩
  · exact hnew s' hs'.1 h2
  · by_cases h' : s' + 1 < t
    · exact hnew (s' + 1) h' h3
    · have : s' + 1 = t := by omega
      subst this
      exact h.hcr s' h1.symm

/-- From a new vertex, the walk visits new vertices up to the next loop step. -/
lemma g2 (h : TW L a x) {t0 T : ℕ} (hnew : newAt x t0) (hT : t0 ≤ T) (hTl : x T = x (T + 1)) :
    ∃ t', t0 ≤ t' ∧ t' ≤ T ∧ x t' = x (t' + 1) ∧ (∀ k, t0 ≤ k → k < t' → x k ≠ x (k + 1)) ∧
      ∀ k, t0 ≤ k → k ≤ t' → newAt x k := by
  have hex : ∃ t, t0 ≤ t ∧ x t = x (t + 1) := ⟨T, hT, hTl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hT, hTl⟩,
    (Nat.find_spec hex).2, fun k hk hk' hkl => Nat.find_min hex hk' ⟨hk, hkl⟩, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact hnew
  | succ k hk ih =>
    intro hk'
    exact h.g1 (ih (by omega)) (fun hkl => Nat.find_min hex (by omega) ⟨hk, hkl⟩)

lemma exists_loop (h : TW L a x) : ∃ T, x T = x (T + 1) := by
  by_contra hno
  push Not at hno
  have : ∀ k, newAt x k := by
    intro k
    induction k with
    | zero => intro s hs; omega
    | succ k ih => exact h.g1 ih (hno k)
  have h1 := this L 0 h.hL
  have h2 := h.px 0
  rw [zero_add] at h2
  exact h1 h2.symm

/-- The first loop step: the walk is injective up to it. -/
lemma first_loop (h : TW L a x) :
    ∃ D, x D = x (D + 1) ∧ (∀ k < D, x k ≠ x (k + 1)) ∧ ∀ k ≤ D, newAt x k := by
  obtain ⟨T, hT⟩ := h.exists_loop
  obtain ⟨t', -, -, h1, h2, h3⟩ := h.g2 (t0 := 0) (fun s hs => by omega) (Nat.zero_le T) hT
  exact ⟨t', h1, fun k hk => h2 k (Nat.zero_le _) hk, fun k hk => h3 k (Nat.zero_le _) hk⟩

/-- A tree walk has at least two loops. -/
theorem two_loops (h : TW L a x) (F : Finset (Fin r × α))
    (hF : ∀ t, x t = x (t + 1) → (a t, x t) ∈ F) : 2 ≤ F.card := by
  obtain ⟨D0, hD0, -, -⟩ := h.first_loop
  obtain ⟨D1, hD1, -, hn1⟩ := (h.shift (D0 + 1)).first_loop
  have m0 := hF D0 hD0
  have m1 := hF (D0 + 1 + D1) hD1
  have hne : (a D0, x D0) ≠ (a (D0 + 1 + D1), x (D0 + 1 + D1)) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    rcases Nat.eq_zero_or_pos D1 with h0 | hpos
    · subst h0
      exact h.hcr D0 heq.1.symm
    · have := hn1 D1 le_rfl 0 hpos
      simp only [add_zero] at this
      exact this (hD0 ▸ heq.2)
  exact Finset.one_lt_card.2 ⟨_, m0, _, m1, hne⟩

/-- Structure of a tree walk with exactly two loops, read from a loop step. -/
theorem structure0 (h : TW L a x) (h0 : x 0 = x 1) (F : Finset (Fin r × α))
    (hF : ∀ t, x t = x (t + 1) → (a t, x t) ∈ F) (hcard : F.card = 2) :
    ∃ d, 1 ≤ d ∧ (∀ v w, v < d → w < d → x (1 + v) = x (1 + w) → v = w) ∧
      ∀ τ, x τ = x (1 + fv 0 d τ) ∧ a τ = a (lb 0 d τ) := by
  obtain ⟨D, hD, -, hnD⟩ := (h.shift 1).first_loop
  set d := D + 1 with hd
  have hd1 : 1 ≤ d := by omega
  have hinj' : ∀ v w, v < w → w < d → x (1 + v) ≠ x (1 + w) := fun v w hvw hw =>
    hnD w (by omega) v hvw
  have hinj : ∀ v w, v < d → w < d → x (1 + v) = x (1 + w) → v = w := by
    intro v w hv hw he
    rcases Nat.lt_trichotomy v w with hlt | heq | hgt
    · exact absurd he (hinj' v w hlt hw)
    · exact heq
    · exact absurd he.symm (hinj' w v hgt hv)
  have hxd : x d = x (d + 1) := by
    convert hD using 2 <;> omega
  -- the two loops
  have m0 : (a 0, x 0) ∈ F := hF 0 h0
  have m1 : (a d, x d) ∈ F := hF d hxd
  have hne : (a 0, x 0) ≠ (a d, x d) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    rcases Nat.eq_zero_or_pos D with hz | hpos
    · have : d = 0 + 1 := by omega
      rw [this] at heq
      exact h.hcr 0 heq.1.symm
    · have := hinj 0 D (by omega) (by omega)
        (by rw [add_zero, ← h0, heq.2]; congr 1; omega)
      omega
  have hFeq : ∀ e ∈ F, e = (a 0, x 0) ∨ e = (a d, x d) := by
    have hsub : ({(a 0, x 0), (a d, x d)} : Finset (Fin r × α)) ⊆ F := by
      intro e he
      rcases mem_insert.1 he with rfl | he
      · exact m0
      · rw [mem_singleton.1 he]; exact m1
    have := Finset.eq_of_subset_of_card_le hsub (by rw [card_pair hne, hcard])
    intro e he
    rw [← this] at he
    simpa using he
  -- periodicity gives late loops
  have hlate : ∀ n, ∃ T, n ≤ T ∧ x T = x (T + 1) := by
    intro n
    refine ⟨n * L, Nat.le_mul_of_pos_right n h.hL, ?_⟩
    have e1 := per_mul h.px 0 n
    have e2 := per_mul h.px 1 n
    rw [zero_add] at e1
    rw [e1, show n * L + 1 = 1 + n * L by omega, e2]; exact h0
  -- the induction
  have key : ∀ n, d + 1 ≤ n →
      (∀ τ ≤ n, x τ = x (1 + fv 0 d τ)) ∧ (∀ τ < n, a τ = a (lb 0 d τ)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have hmm : ∀ τ, 1 ≤ τ → τ ≤ d + 1 → mm 0 d τ = τ - 1 := by
        intro τ h1 h2
        unfold mm
        rw [show τ + (2 * d - 1 - 0) = τ - 1 + 2 * d by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      have hmm0 : mm 0 d 0 = 2 * d - 1 := by
        unfold mm
        rw [zero_add, Nat.sub_zero, Nat.mod_eq_of_lt (by omega)]
      constructor
      · intro τ hτ
        rcases Nat.eq_zero_or_pos τ with hz | hpos
        · subst hz
          have : fv 0 d 0 = 0 := by unfold fv; rw [hmm0]; split_ifs <;> omega
          rw [this]; exact h0
        · have hm := hmm τ hpos hτ
          by_cases hτd : τ ≤ d
          · have : fv 0 d τ = τ - 1 := by unfold fv; rw [hm]; split_ifs <;> omega
            rw [this]; congr 1; omega
          · have hτe : τ = d + 1 := by omega
            have : fv 0 d τ = d - 1 := by unfold fv; rw [hm]; split_ifs <;> omega
            rw [this, hτe, ← hxd]; congr 1; omega
      · intro τ hτ
        rcases Nat.eq_zero_or_pos τ with hz | hpos
        · subst hz
          have : lb 0 d 0 = 0 := by unfold lb; rw [hmm0]; split_ifs <;> omega
          rw [this]
        · have hm := hmm τ hpos (by omega)
          have : lb 0 d τ = τ := by unfold lb; rw [hm]; split_ifs <;> omega
          rw [this]
    | succ n hn ih =>
      obtain ⟨ihx, iha⟩ := ih
      set v := fv 0 d n with hv
      have hvd : v < d := fv_lt hd1
      have hxn : x n = x (1 + v) := ihx n le_rfl
      have hkey : ∀ w, w < d → x (1 + w) = x n → w = v := fun w hw he =>
        hinj w v hw hvd (he.trans hxn)
      -- the possible outcomes of step `n`
      have hout : (x (n + 1) = x n ∧ v = 0 ∧ a n = a 0) ∨
          (x (n + 1) = x n ∧ v = d - 1 ∧ a n = a d) ∨
          (v + 1 ≤ d - 1 ∧ x (n + 1) = x (1 + (v + 1)) ∧ a n = a (v + 1)) ∨
          (1 ≤ v ∧ x (n + 1) = x (1 + (v - 1)) ∧ a n = a v) := by
        by_cases hl : x n = x (n + 1)
        · rcases hFeq _ (hF n hl) with he | he
          · rw [Prod.mk.injEq] at he
            have : 0 = v := hkey 0 (by omega) (by rw [add_zero, ← h0]; exact he.2.symm)
            exact Or.inl ⟨hl.symm, this.symm, he.1⟩
          · rw [Prod.mk.injEq] at he
            have : d - 1 = v := hkey (d - 1) (by omega)
              (by rw [he.2]; congr 1; omega)
            exact Or.inr (Or.inl ⟨hl.symm, this.symm, he.1⟩)
        · by_cases hin : x (n + 1) ∈ UU x n
          · have he : pe a x n ∈ EE a x n := by
              by_contra h'; exact h.hnc0 n ⟨hl, hin, h'⟩
            obtain ⟨s, hs, hse⟩ := mem_image.1 he
            rw [mem_filter, mem_range] at hs
            obtain ⟨hsn, hsl⟩ := hs
            have hxs := ihx s (by omega)
            have hxs1 := ihx (s + 1) (by omega)
            have has := iha s hsn
            have hfs := fv_lt (p := 0) (τ := s) hd1
            have hfs1 := fv_lt (p := 0) (τ := s + 1) hd1
            rcases fold_cases (p := 0) hd1 s with ⟨hc, -⟩ | ⟨hk1, hk2, hc⟩
            · exact absurd (by rw [hxs, hxs1, hc]) hsl
            · rcases pe_eq.1 hse with ⟨hcol, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩
              · have hv1 := hkey _ hfs (hxs ▸ e1)
                rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
                · refine Or.inr (Or.inr (Or.inl ⟨by omega, ?_, ?_⟩))
                  · rw [← e2, hxs1, c2, ← c1, hv1]
                  · rw [← hcol, has, ← c1, hv1]
                · refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_, ?_⟩))
                  · rw [← e2, hxs1]; congr 2; omega
                  · rw [← hcol, has, ← c1, hv1]
              · have hv1 := hkey _ hfs1 (hxs1 ▸ e2)
                rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
                · refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_, ?_⟩))
                  · rw [← e1, hxs]; congr 2; omega
                  · rw [← hcol, has, ← c2, hv1]
                · refine Or.inr (Or.inr (Or.inl ⟨by omega, ?_, ?_⟩))
                  · rw [← e1, hxs]; congr 2; omega
                  · rw [← hcol, has]; congr 1; omega
          · exfalso
            have hnew : newAt x (n + 1) := by
              intro s hs heq
              exact hin (heq ▸ mem_UU (by omega))
            obtain ⟨T, hT, hTl⟩ := hlate (n + 1)
            obtain ⟨t', ht', -, htl, -, hnt⟩ := h.g2 hnew hT hTl
            have hnt' := hnt t' ht' le_rfl
            rcases hFeq _ (hF t' htl) with he | he
            · rw [Prod.mk.injEq] at he
              exact hnt' 0 (by omega) he.2.symm
            · rw [Prod.mk.injEq] at he
              exact hnt' d (by omega) he.2.symm
      have hprev : a n ≠ a (lb 0 d (n - 1)) := by
        have h1 := h.hcr (n - 1)
        rw [show n - 1 + 1 = n by omega, iha (n - 1) (by omega)] at h1
        exact h1
      obtain ⟨s1, s2, s3, s4⟩ := fold_step (p := 0) hd1 n (by omega)
      have hres : a n = a (lb 0 d n) ∧ x (n + 1) = x (1 + fv 0 d (n + 1)) := by
        rcases hout with ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩
        · obtain ⟨r1, r2⟩ := s1 o2 (fun hh => hprev (by rw [o3, hh]))
          exact ⟨by rw [r1, o3], by rw [r2, o1, hxn]⟩
        · obtain ⟨r1, r2⟩ := s2 o2 (fun hh => hprev (by rw [o3, hh]))
          exact ⟨by rw [r1, o3], by rw [r2, o1, hxn]⟩
        · obtain ⟨r1, r2⟩ := s3 o1 (fun hh => hprev (by rw [o3, hh]))
          exact ⟨by rw [r1, o3], by rw [r2, o2]⟩
        · obtain ⟨r1, r2⟩ := s4 o1 (fun hh => hprev (by rw [o3, hh]))
          exact ⟨by rw [r1, o3], by rw [r2, o2]⟩
      constructor
      · intro τ hτ
        rcases Nat.lt_or_ge τ (n + 1) with hlt | hge
        · exact ihx τ (by omega)
        · have : τ = n + 1 := by omega
          rw [this]; exact hres.2
      · intro τ hτ
        rcases Nat.lt_or_ge τ n with hlt | hge
        · exact iha τ hlt
        · have : τ = n := by omega
          rw [this]; exact hres.1
  refine ⟨d, hd1, hinj, fun τ => ?_⟩
  obtain ⟨k1, k2⟩ := key (τ + d + 1) (by omega)
  exact ⟨k1 τ (by omega), k2 τ (by omega)⟩

/-- Structure of a tree walk with exactly two loops: it goes back and forth on a path of `d`
vertices `x (p + 1 + v)`, `v < d`, with the loops at the two ends; `p` is the first loop step. -/
theorem structure1 (h : TW L a x) (F : Finset (Fin r × α))
    (hF : ∀ t, x t = x (t + 1) → (a t, x t) ∈ F) (hcard : F.card = 2) :
    ∃ p d, p < d ∧ 2 * d ∣ L ∧
      (∀ v w, v < d → w < d → x (p + 1 + v) = x (p + 1 + w) → v = w) ∧
      ∀ τ, x τ = x (p + 1 + fv p d τ) ∧ a τ = a (p + lb p d τ) := by
  obtain ⟨T, hT⟩ := h.exists_loop
  have hex : ∃ t, x t = x (t + 1) := ⟨T, hT⟩
  have hpl : x (Nat.find hex) = x (Nat.find hex + 1) := Nat.find_spec hex
  have hmin : ∀ t < Nat.find hex, x t ≠ x (t + 1) := fun t ht => Nat.find_min hex ht
  generalize Nat.find hex = p at hpl hmin
  obtain ⟨d, hd1, hinj0, hstr0⟩ := (h.shift p).structure0 hpl F (fun t ht => hF (p + t) ht) hcard
  have hinj : ∀ v w, v < d → w < d → x (p + 1 + v) = x (p + 1 + w) → v = w := by
    intro v w hv hw he
    refine hinj0 v w hv hw ?_
    show x (p + (1 + v)) = x (p + (1 + w))
    rw [← add_assoc, ← add_assoc]; exact he
  have hstr : ∀ τ, x (p + τ) = x (p + 1 + fv 0 d τ) ∧ a (p + τ) = a (p + lb 0 d τ) := by
    intro τ
    obtain ⟨h1, h2⟩ := hstr0 τ
    refine ⟨?_, h2⟩
    rw [add_assoc]; exact h1
  -- `2 d ∣ L`
  have hdvd : 2 * d ∣ L := by
    have e1 : x (p + L) = x p := h.px p
    have e2 : x (p + (L + 1)) = x (p + 1) := by
      rw [show p + (L + 1) = p + 1 + L by omega]; exact h.px _
    have hfe : fv 0 d L = fv 0 d (L + 1) := by
      refine hinj _ _ (fv_lt hd1) (fv_lt hd1) ?_
      rw [← (hstr L).1, ← (hstr (L + 1)).1, e1, e2]; exact hpl
    rcases fold_cases (p := 0) hd1 L with ⟨-, hc | hc⟩ | ⟨_, _, hc⟩
    · have hm := mm_lt (p := 0) (τ := L) hd1
      have hlb := hc.1
      unfold lb at hlb
      have hm2 : mm 0 d L = 2 * d - 1 := by split_ifs at hlb; omega
      unfold mm at hm2
      rw [Nat.sub_zero] at hm2
      exact dvd_of_add_pred_mod (by omega) hm2
    · exfalso
      have ha : a p = a (p + d) := by rw [← h.pa p, (hstr L).2, hc.1]
      have hx : x p = x (p + 1 + (d - 1)) := by rw [← e1, (hstr L).1, hc.2]
      rcases Nat.lt_or_ge 1 d with hd2 | hd2
      · have := hinj 0 (d - 1) (by omega) (by omega) (by rw [add_zero, ← hpl]; exact hx)
        omega
      · have hd' : d = 1 := by omega
        rw [hd'] at ha
        exact h.hcr p ha.symm
    · omega
  have hL2 : 2 * d ≤ L := Nat.le_of_dvd h.hL hdvd
  -- `p < d`
  have hpd : p < d := by
    by_contra hge
    have hm1 : mm 0 d (L - d) = d - 1 := by
      unfold mm
      rw [show L - d + (2 * d - 1 - 0) = (d - 1) + L by omega, add_mod_of_dvd _ hdvd,
        Nat.mod_eq_of_lt (by omega)]
    have hm2 : mm 0 d (L - d + 1) = d := by
      rw [mm_succ hd1, hm1, if_pos (by omega)]; omega
    have hf1 : fv 0 d (L - d) = d - 1 := by unfold fv; rw [hm1]; split_ifs <;> omega
    have hf2 : fv 0 d (L - d + 1) = d - 1 := by unfold fv; rw [hm2]; split_ifs <;> omega
    have e : x (p + (L - d)) = x (p + (L - d + 1)) := by
      rw [(hstr _).1, (hstr _).1, hf1, hf2]
    rw [show p + (L - d) = p - d + L by omega, show p + (L - d + 1) = p - d + 1 + L by omega,
      h.px, h.px] at e
    exact hmin (p - d) (by omega) e
  refine ⟨p, d, hpd, hdvd, hinj, fun τ => ?_⟩
  have hpL : p ≤ p * L := Nat.le_mul_of_pos_right p h.hL
  obtain ⟨σ, hσ⟩ : ∃ σ, p + σ = τ + p * L := ⟨τ + p * L - p, by omega⟩
  have hmm : mm 0 d σ = mm p d τ := by
    unfold mm
    rw [show σ + (2 * d - 1 - 0) = τ + (2 * d - 1 - p) + p * L by omega,
      add_mod_of_dvd _ (Dvd.dvd.mul_left hdvd p)]
  have hfv : fv 0 d σ = fv p d τ := by unfold fv; rw [hmm]
  have hlb : lb 0 d σ = lb p d τ := by unfold lb; rw [hmm]
  obtain ⟨h1, h2⟩ := hstr σ
  rw [hσ, per_mul h.px, hfv] at h1
  rw [hσ, per_mul h.pa, hlb] at h2
  exact ⟨h1, h2⟩

end TW
end RandomInvolutions.Dev.PartW
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {α : Type*} [DecidableEq α]
omit [DecidableEq α] in
/-- Explicit phases. -/
lemma mm_lo {p d t : ℕ} (hpd : p < d) (ht : t ≤ p) : mm p d t = t + (2 * d - 1 - p) := by
  unfold mm; exact Nat.mod_eq_of_lt (by omega)

omit [DecidableEq α] in
lemma mm_hi {p d t : ℕ} (hpd : p < d) (ht : p < t) (ht' : t ≤ p + 2 * d) :
    mm p d t = t - p - 1 := by
  unfold mm
  rw [show t + (2 * d - 1 - p) = t - p - 1 + 2 * d by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

omit [DecidableEq α] in
lemma mm_per {p d L : ℕ} (hdvd : 2 * d ∣ L) (t : ℕ) : mm p d (t + L) = mm p d t := by
  unfold mm
  rw [show t + L + (2 * d - 1 - p) = t + (2 * d - 1 - p) + L by omega, add_mod_of_dvd _ hdvd]

lemma mem_LL_of_loop {L : ℕ} {a : ℕ → Fin r} {x : ℕ → α} (hL : 0 < L)
    (px : ∀ t, x (t + L) = x t) (pa : ∀ t, a (t + L) = a t) {t : ℕ} (ht : x t = x (t + 1)) :
    (a t, x t) ∈ LL a x L := by
  refine mem_image.2 ⟨t % L, mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ hL), ?_⟩, ?_⟩
  · rw [← per_mod px, ← per_mod_succ px]; exact ht
  · rw [← per_mod px, ← per_mod pa]

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {n : ℕ} {α : Type*} [DecidableEq α]
/-!
# Part W, bridge: colourings with loops as periodic walks

A closed colouring `c` of a nonempty word `u` is read as the periodic walk `Xc c` with colours
`ac u`; `nv`, `Ecount`, `Fcount` become the numbers of vertices, coloured pairs and coloured
loops of that walk.  This gives `v ≤ e + 1`, and for cyclically reduced words `v ≤ e + f` with
equality only if `f = 0`.
-/
/-! ## Canonical representatives of kernels -/
lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
lemma card_image_ker {ι β γ : Type*} [DecidableEq β] [DecidableEq γ] (S : Finset ι)
    (φ : ι → β) (ψ : ι → γ) (h : ∀ s ∈ S, ∀ t ∈ S, φ s = φ t ↔ ψ s = ψ t) :
    (S.image φ).card = (S.image ψ).card := by
  refine Finset.card_bij (fun y hy => ψ (Classical.choose (mem_image.1 hy))) ?_ ?_ ?_
  · intro y hy
    exact mem_image_of_mem _ (Classical.choose_spec (mem_image.1 hy)).1
  · intro y hy y' hy' he
    have s1 := Classical.choose_spec (mem_image.1 hy)
    have s2 := Classical.choose_spec (mem_image.1 hy')
    rw [← s1.2, ← s2.2]
    exact (h _ s1.1 _ s2.1).2 he
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hz
    refine ⟨φ t, mem_image_of_mem _ ht, ?_⟩
    have s1 := Classical.choose_spec (mem_image.1 (mem_image_of_mem φ ht))
    exact (h _ s1.1 _ ht).1 s1.2

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-! ## Letters of `Lt 0 r` -/
/-- The colour of a letter. -/
def colr : Lt 0 r → Fin r
  | Sum.inl p => p.1.elim0
  | Sum.inr j => j

lemma inr_colr (l : Lt 0 r) : Sum.inr (colr l) = l := by
  rcases l with ⟨i, _⟩ | j
  · exact i.elim0
  · rfl

lemma eq_inr_iff (l : Lt 0 r) (k : Fin r) : l = Sum.inr k ↔ colr l = k := by
  constructor
  · rintro rfl; rfl
  · rintro rfl; exact (inr_colr l).symm

lemma colr_inj {l l' : Lt 0 r} (h : colr l = colr l') : l = l' := by
  rw [← inr_colr l, ← inr_colr l', h]

lemma bar_eq (l : Lt 0 r) : bar l = l := by
  rcases l with ⟨i, _⟩ | j
  · exact i.elim0
  · rfl

/-! ## Periodic readings -/
/-- The colours of a nonempty word, read cyclically. -/
def ac (u : List (Lt 0 r)) (hne : u ≠ []) (t : ℕ) : Fin r :=
  colr (u.get ⟨t % u.length, Nat.mod_lt _ (List.length_pos_iff.2 hne)⟩)

/-- A colouring read cyclically. -/
def Xc {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : ℕ) : β := c ⟨min (t % L) L, by omega⟩

lemma ac_per (u : List (Lt 0 r)) (hne : u ≠ []) (t : ℕ) :
    ac u hne (t + u.length) = ac u hne t := by
  unfold ac; congr 2; exact Fin.ext (by simp)

lemma ac_get (u : List (Lt 0 r)) (hne : u ≠ []) (t : Fin u.length) :
    colr (u.get t) = ac u hne t.val := by
  unfold ac; congr 2; exact Fin.ext (by simp [Nat.mod_eq_of_lt t.2])

lemma ac_cr (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u) (t : ℕ) :
    ac u hne (t + 1) ≠ ac u hne t := by
  intro h
  have hL := List.length_pos_iff.2 hne
  refine hcr ⟨t % u.length, Nat.mod_lt _ hL⟩ ?_
  rw [bar_eq]
  apply colr_inj
  have e1 : colr (u.get ⟨(t % u.length + 1) % u.length, Nat.mod_lt _ hL⟩) = ac u hne (t + 1) := by
    unfold ac; congr 2; exact Fin.ext (by simp)
  exact e1.trans h

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
variable {L : ℕ} {β : Type*}
lemma Xc_per (c : Fin (L + 1) → β) (t : ℕ) : Xc c (t + L) = Xc c t := by
  unfold Xc; congr 1; exact Fin.ext (by simp)

lemma Xc_lt (c : Fin (L + 1) → β) {t : ℕ} (ht : t < L) : Xc c t = c ⟨t, by omega⟩ := by
  unfold Xc; congr 1; refine Fin.ext ?_
  simp only [Nat.mod_eq_of_lt ht]; omega

lemma Xc_L (c : Fin (L + 1) → β) : Xc c L = c 0 := by
  unfold Xc; congr 1; exact Fin.ext (by simp)

lemma Xc_cs (c : Fin (L + 1) → β) (t : Fin L) : c t.castSucc = Xc c t.val := by
  rw [Xc_lt c t.2]; rfl

lemma Xc_succ (c : Fin (L + 1) → β) (hcl : c 0 = c (Fin.last L)) (t : Fin L) :
    c t.succ = Xc c (t.val + 1) := by
  rcases Nat.lt_or_ge (t.val + 1) L with h | h
  · rw [Xc_lt c h]; rfl
  · have ht : t.val + 1 = L := by have := t.2; omega
    rw [ht, Xc_L, hcl]; congr 1; exact Fin.ext (by simp [ht])

lemma nv_eq [DecidableEq β] (hL : 0 < L) (c : Fin (L + 1) → β) (hcl : c 0 = c (Fin.last L)) :
    nv c = ((range L).image (Xc c)).card := by
  unfold nv
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    rcases Nat.lt_or_ge t.val L with h | h
    · exact ⟨t.val, h, Xc_lt c h⟩
    · refine ⟨0, hL, ?_⟩
      rw [Xc_lt c hL]
      have : t = Fin.last L := Fin.ext (by have := t.2; simp; omega)
      rw [this, ← hcl]; rfl
  · rintro ⟨t, -, rfl⟩; exact ⟨_, rfl⟩

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
variable {β : Type*} [DecidableEq β] (u : List (Lt 0 r)) (hne : u ≠ [])
  (c : Fin (u.length + 1) → β) (hcl : c 0 = c (Fin.last _))
/-! ## Pairs and loops of a colouring as pairs and loops of the walk -/
include hcl in
lemma mem_Ps (k : Fin r) (q : Sym2 β) :
    q ∈ Ps u c k ↔ ∃ t < u.length, ac u hne t = k ∧ Xc c t ≠ Xc c (t + 1) ∧
      q = s(Xc c t, Xc c (t + 1)) := by
  unfold Ps
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    refine ⟨t.val, t.2, ?_, ?_, ?_⟩
    · rw [← ac_get]; exact (eq_inr_iff _ _).1 h1
    · rw [← Xc_cs c t, ← Xc_succ c hcl t]; exact h2
    · rw [← Xc_cs c t, ← Xc_succ c hcl t]
  · rintro ⟨t, ht, h1, h2, rfl⟩
    refine ⟨⟨t, ht⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [eq_inr_iff, ac_get u hne ⟨t, ht⟩]; exact h1
    · rw [Xc_cs c ⟨t, ht⟩, Xc_succ c hcl ⟨t, ht⟩]; exact h2
    · rw [Xc_cs c ⟨t, ht⟩, Xc_succ c hcl ⟨t, ht⟩]

include hcl in
lemma mem_Ls (k : Fin r) (w : β) :
    w ∈ Ls u c k ↔ ∃ t < u.length, ac u hne t = k ∧ Xc c t = Xc c (t + 1) ∧ w = Xc c t := by
  unfold Ls
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    refine ⟨t.val, t.2, ?_, ?_, ?_⟩
    · rw [← ac_get]; exact (eq_inr_iff _ _).1 h1
    · rw [← Xc_cs c t, ← Xc_succ c hcl t]; exact h2
    · rw [← Xc_cs c t]
  · rintro ⟨t, ht, h1, h2, rfl⟩
    refine ⟨⟨t, ht⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [eq_inr_iff, ac_get u hne ⟨t, ht⟩]; exact h1
    · rw [Xc_cs c ⟨t, ht⟩, Xc_succ c hcl ⟨t, ht⟩]; exact h2
    · rw [Xc_cs c ⟨t, ht⟩]

include hcl in
lemma EE_fiber (k : Fin r) :
    (EE (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k) =
      (Ps u c k).image (Prod.mk k) := by
  ext ⟨k', q⟩
  simp only [mem_filter, mem_image, EE, mem_range, pe, Prod.mk.injEq, mem_Ps u hne c hcl]
  constructor
  · rintro ⟨⟨t, ⟨ht, hne'⟩, h1, h2⟩, rfl⟩
    exact ⟨q, ⟨t, ht, h1, hne', h2.symm⟩, rfl, rfl⟩
  · rintro ⟨q', ⟨t, ht, h1, h2, rfl⟩, rfl, rfl⟩
    exact ⟨⟨t, ⟨ht, h2⟩, h1, rfl⟩, rfl⟩

include hcl in
lemma LL_fiber (k : Fin r) :
    (LL (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k) =
      (Ls u c k).image (Prod.mk k) := by
  ext ⟨k', w⟩
  simp only [mem_filter, mem_image, LL, mem_range, Prod.mk.injEq, mem_Ls u hne c hcl]
  constructor
  · rintro ⟨⟨t, ⟨ht, hne'⟩, h1, h2⟩, rfl⟩
    exact ⟨w, ⟨t, ht, h1, hne', h2.symm⟩, rfl, rfl⟩
  · rintro ⟨w', ⟨t, ht, h1, h2, rfl⟩, rfl, rfl⟩
    exact ⟨⟨t, ⟨ht, h2⟩, h1, rfl⟩, rfl⟩

include hcl in
lemma card_Ps_eq (k : Fin r) :
    (Ps u c k).card = ((EE (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k)).card := by
  rw [EE_fiber u hne c hcl, card_image_of_injective _ (Prod.mk_right_injective k)]

include hcl in
lemma card_Ls_eq (k : Fin r) :
    (Ls u c k).card = ((LL (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k)).card := by
  rw [LL_fiber u hne c hcl, card_image_of_injective _ (Prod.mk_right_injective k)]

include hcl in
lemma sum_card_Ps : ∑ k, (Ps u c k).card = (EE (ac u hne) (Xc c) u.length).card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  exact sum_congr rfl fun k _ => card_Ps_eq u hne c hcl k

include hcl in
lemma sum_card_Ls : ∑ k, (Ls u c k).card = (LL (ac u hne) (Xc c) u.length).card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  exact sum_congr rfl fun k _ => card_Ls_eq u hne c hcl k

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
lemma mem_CGL {u : List (Lt 0 r)} {c : Fin (u.length + 1) → Fin (u.length + 1)} :
    c ∈ CGL u ↔ canon c = c ∧ GoodL u c := by
  unfold CGL
  simp only [mem_filter, mem_univ, true_and]

lemma Ecount_eq (u : List (Lt 0 r)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _)) :
    Ecount u c = (EE (ac u hne) (Xc c) u.length).card := by
  rw [← sum_card_Ps u hne c hcl]; rfl

lemma Fcount_eq (u : List (Lt 0 r)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _)) :
    Fcount u c = (LL (ac u hne) (Xc c) u.length).card := by
  rw [← sum_card_Ls u hne c hcl]; rfl

/-- `v ≤ e + 1` for every closed colouring. -/
theorem nv_le_succ (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hcl : c 0 = c (Fin.last _)) : nv c ≤ Ecount u c + 1 := by
  by_cases hne : u = []
  · subst hne
    have : nv c ≤ (univ : Finset (Fin 1)).card := by
      unfold nv; exact card_le_card (subset_univ _)
    simp at this
    omega
  · have hL := List.length_pos_iff.2 hne
    rw [nv_eq hL c hcl, Ecount_eq u hne c hcl]
    refine le_trans (card_le_card ?_) (card_UU_le (ac u hne) (Xc c) u.length)
    exact image_subset_image (range_mono (by omega))

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-!
# Part W: colourings with loops of cyclically reduced words

* `nv_le_ecount_succ`: the pair graph is connected (`PartW_Walk`, `count`).
* `nv_le_ecount_add_fcount`, `fcount_eq_zero`: a tree walk of a cyclically reduced word has at
  least two loops (`TW.two_loops`).
* `card_second_order`: tree walks with exactly two loops go back and forth on a path
  (`TW.structure1`), so they are the fold colourings (`card_second_eq`), which correspond to the
  tuples of `C2count` by uniqueness of normal forms (`c2count_eq`).
-/
/-- The pair graph is connected: `v ≤ e + 1` (any word). -/
theorem nv_le_ecount_succ (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hc : c ∈ CGL u) : nv c ≤ Ecount u c + 1 :=
  nv_le_succ u c (mem_CGL.1 hc).2.2.2

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part W: colourings with loops of cyclically reduced words -/
alias nv_le_ecount_succ := RandomInvolutions.Dev.PartW.nv_le_ecount_succ

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- A closed colouring of a cyclically reduced word with `v = e + 1` is a tree walk. -/
theorem tw_of_eq (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _))
    (h : nv c = Ecount u c + 1) : TW u.length (ac u hne) (Xc c) := by
  have hL := List.length_pos_iff.2 hne
  refine TW.mk' hL (Xc_per c) (ac_per u hne) (ac_cr u hne hcr) ?_
  rw [← nv_eq hL c hcl, ← Ecount_eq u hne c hcl]; exact h

/-- A tree colouring of a cyclically reduced word has at least two loops. -/
theorem two_le_fcount (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _))
    (h : nv c = Ecount u c + 1) : 2 ≤ Fcount u c := by
  have hL := List.length_pos_iff.2 hne
  rw [Fcount_eq u hne c hcl]
  exact (tw_of_eq u hne hcr c hcl h).two_loops _
    (fun t ht => mem_LL_of_loop hL (Xc_per c) (ac_per u hne) ht)

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- No leaves except at loops: `v ≤ e + f` for cyclically reduced words. -/
theorem nv_le_ecount_add_fcount (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CGL u) :
    nv c ≤ Ecount u c + Fcount u c := by
  have hcl := (mem_CGL.1 hc).2.2.2
  have h1 := nv_le_succ u c hcl
  by_cases h : nv c = Ecount u c + 1
  · have := two_le_fcount u hne hcr c hcl h
    omega
  · omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias nv_le_ecount_add_fcount := RandomInvolutions.Dev.PartW.nv_le_ecount_add_fcount

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- First-order colourings of cyclically reduced words have no loops. -/
theorem fcount_eq_zero (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CGL u)
    (h : nv c = Ecount u c + Fcount u c) : Fcount u c = 0 := by
  have hcl := (mem_CGL.1 hc).2.2.2
  have h1 := nv_le_succ u c hcl
  by_contra h0
  have h2 : nv c = Ecount u c + 1 := by omega
  have := two_le_fcount u hne hcr c hcl h2
  omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias fcount_eq_zero := RandomInvolutions.Dev.PartW.fcount_eq_zero

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
lemma sum_tendsto (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u) (κ : Fin r → ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (∑ c ∈ CGL u, wtK u N κ c -
        (((CGL u).filter fun c => nv c = Ecount u c + Fcount u c).card : ℝ))) atTop
      (𝓝 (∑ c ∈ CGL u, Tc u κ c)) := by
  have hT : ∀ c ∈ CGL u, Tendsto (fun N : ℕ => (N : ℝ) * (wtK u N κ c -
      (if nv c = Ecount u c + Fcount u c then 1 else 0))) atTop (𝓝 (Tc u κ c)) := by
    intro c hc
    unfold Tc wtK
    by_cases h0 : nv c = Ecount u c + Fcount u c
    · simp only [if_pos h0]
      have hF := fcount_eq_zero u hne hcr c hc h0
      have hf : ∀ i, fK u c i = 0 := fun i => (sum_eq_zero_iff.1 hF) i (mem_univ i)
      have h := tendsto_two' κ (nv c) (eK u c) (fK u c) h0
      simp only [hf, Nat.descFactorial_zero, Nat.cast_one, prod_const_one, one_mul] at h
      exact h
    · simp only [if_neg h0, sub_zero]
      by_cases h1 : nv c + 1 = Ecount u c + Fcount u c
      · simp only [if_pos h1]
        exact wtF_tendsto_one κ _ _ _ h1
      · simp only [if_neg h1]
        refine wtF_tendsto_zero κ _ _ _ ?_
        have h2 := nv_le_ecount_add_fcount u hne hcr c hc
        unfold Ecount Fcount at h0 h1 h2
        omega
  have h := tendsto_finsetSum (CGL u) hT
  refine h.congr fun N => ?_
  rw [← mul_sum, sum_sub_distrib, sum_boole]

lemma S0_card (a : G 0 r) (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (hg : a * wprod u * a⁻¹ ≠ 1) :
    (((CGL u).filter fun c => nv c = Ecount u c + Fcount u c).card : ℝ) =
      (cfun (a * wprod u * a⁻¹) : ℝ) + 1 := by
  have hr : r ≠ 0 := by
    rintro rfl
    cases u with
    | nil => exact hne rfl
    | cons x _ => rcases x with ⟨i, _⟩ | i <;> exact i.elim0
  have h1 := sum_tendsto u hne hcr (fun _ => 0)
  have h2 : Tendsto (fun N : ℕ => ∑ c ∈ CGL u, wtK u N (fun _ => 0) c -
      (((CGL u).filter fun c => nv c = Ecount u c + Fcount u c).card : ℝ)) atTop (𝓝 0) := by
    have h := h1.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  have hst : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) tendsto_id
  have h3 : Tendsto (fun n : ℕ => expFixK r (2 * n) (fun _ => 0) (a * wprod u * a⁻¹)) atTop
      (𝓝 (((CGL u).filter fun c => nv c = Ecount u c + Fcount u c).card : ℝ)) := by
    have h4 := (h2.comp hst).add_const
      (((CGL u).filter fun c => nv c = Ecount u c + Fcount u c).card : ℝ)
    rw [zero_add] at h4
    refine h4.congr' ?_
    filter_upwards [hst.eventually (eventually_ge_atTop (max 1 u.length))] with n hn
    simp only [Function.comp_apply, sub_add_cancel]
    rw [expFixK_conj]
    exact (expect_formulaK u _ _ (le_of_max_le_left hn) (fun i => ⟨Nat.zero_le _, by simp⟩)
      (le_of_max_le_right hn)).symm
  have h5 := BordenaveCollins.tendsto_expFix (a * wprod u * a⁻¹) hg
  have hs : stp r = 2 := by simp [stp, hr]
  rw [hs] at h5
  simp only [← expFixK_zero] at h5
  exact tendsto_nhds_unique h3 h5

/-! ## Falling factorial products for at most two loops -/
lemma exists_peel (f : Fin r → ℕ) (n : ℕ) (h : ∑ i, f i = n + 1) :
    ∃ i0, ∃ f' : Fin r → ℕ, (∀ k, f k = (if k = i0 then 1 else 0) + f' k) ∧ ∑ i, f' i = n := by
  have h0 : ∃ i0, f i0 ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h
  obtain ⟨i0, hi0⟩ := h0
  have hk : ∀ k, f k = (if k = i0 then 1 else 0) + (f k - (if k = i0 then 1 else 0)) := by
    intro k
    by_cases hk : k = i0
    · subst hk; simp; omega
    · simp [hk]
  refine ⟨i0, fun k => f k - (if k = i0 then 1 else 0), hk, ?_⟩
  have h' := h
  rw [sum_congr rfl fun k _ => hk k, sum_add_distrib] at h'
  simp only [sum_ite_eq', mem_univ, if_true] at h'
  show ∑ i, (f i - if i = i0 then 1 else 0) = n
  omega

lemma desc_two (k : ℕ) : ((k.descFactorial 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 - k := by
  cases k with
  | zero => simp
  | succ m =>
    simp [Nat.descFactorial]
    ring

lemma prod_le_one (κ f : Fin r → ℕ) (h : ∑ i, f i ≤ 1) :
    (∏ i, ((κ i).descFactorial (f i) : ℝ)) =
      1 - ∑ i, (f i : ℝ) + ∑ i, (κ i : ℝ) * f i := by
  rcases Nat.lt_or_ge (∑ i, f i) 1 with h0 | h1
  · have hf : ∀ i, f i = 0 := fun i =>
      (sum_eq_zero_iff.1 (by omega : ∑ i, f i = 0)) i (mem_univ i)
    simp [hf]
  · obtain ⟨i0, f', hf, hf'⟩ := exists_peel f 0 (by omega)
    have hf'0 : ∀ i, f' i = 0 := fun i => (sum_eq_zero_iff.1 hf') i (mem_univ i)
    have hf2 : ∀ k, f k = if k = i0 then 1 else 0 := fun k => by rw [hf k, hf'0]; simp
    simp only [hf2]
    rw [prod_eq_single i0 (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ _) h)]
    simp

/-- The quadratic weight of a pair of loop colours. -/
def wq (κ : Fin r → ℕ) (i j : Fin r) : ℝ :=
  if i = j then (κ i : ℝ) ^ 2 - κ i else (κ i : ℝ) * κ j / 2

lemma delta_class (i j i0 j0 : Fin r) :
    (∀ k : Fin r, ((if k = i0 then 1 else 0) + (if k = j0 then 1 else 0) : ℕ) =
        (if k = i then 1 else 0) + (if k = j then 1 else 0)) ↔
      (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) := by
  constructor
  · intro h
    have hi : i = i0 ∨ i = j0 := by
      by_contra hc
      rw [not_or] at hc
      have := h i
      simp [hc.1, hc.2] at this
      split_ifs at this <;> omega
    have hj : j = i0 ∨ j = j0 := by
      by_contra hc
      rw [not_or] at hc
      have := h j
      simp [hc.1, hc.2] at this
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have d := h j0
      rw [hi, hj] at d
      by_cases e : j0 = i0
      · exact Or.inl ⟨hi, hj.trans e.symm⟩
      · simp [e] at d
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨hi, hj⟩
    · have c := h i0
      rw [hi, hj] at c
      by_cases e : i0 = j0
      · exact Or.inr ⟨hi, hj.trans e.symm⟩
      · simp [e] at c
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) k
    · rfl
    · exact add_comm _ _

lemma sum_pair (F : Fin r → Fin r → ℝ) (a b : Fin r) :
    (∑ i, ∑ j, if i = a ∧ j = b then F i j else 0) = F a b := by
  rw [sum_eq_single a (fun i _ hi => sum_eq_zero fun j _ => if_neg fun h => hi h.1)
      (fun h => absurd (mem_univ _) h),
    sum_eq_single b (fun j _ hj => if_neg fun h => hj h.2) (fun h => absurd (mem_univ _) h),
    if_pos ⟨rfl, rfl⟩]

lemma prod_two (κ f : Fin r → ℕ) (h : ∑ i, f i = 2) :
    (∏ i, ((κ i).descFactorial (f i) : ℝ)) =
      ∑ i, ∑ j, if (∀ k, f k = (if k = i then 1 else 0) + (if k = j then 1 else 0))
        then wq κ i j else 0 := by
  obtain ⟨i0, f1, hf1, h1⟩ := exists_peel f 1 h
  obtain ⟨j0, f2, hf2, h2⟩ := exists_peel f1 0 h1
  have hf20 : ∀ i, f2 i = 0 := fun i => (sum_eq_zero_iff.1 h2) i (mem_univ i)
  have hf : ∀ k, f k = (if k = i0 then 1 else 0) + (if k = j0 then 1 else 0) := fun k => by
    rw [hf1, hf2, hf20, add_zero]
  have hP : ∀ i j, (∀ k, f k = (if k = i then 1 else 0) + (if k = j then 1 else 0)) ↔
      (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) := by
    intro i j
    rw [← delta_class]
    constructor
    · intro hh k; rw [← hf k]; exact hh k
    · intro hh k; rw [hf k]; exact hh k
  simp only [hP]
  by_cases hij : i0 = j0
  · subst hij
    simp only [or_self]
    rw [sum_pair (fun i j => wq κ i j)]
    have hfk : ∀ k, f k = if k = i0 then 2 else 0 := fun k => by
      rw [hf k]; split_ifs <;> rfl
    simp only [hfk]
    rw [prod_eq_single i0 (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ _) h)]
    simp only [if_true, wq]
    exact desc_two _
  · have hsplit : ∀ i j : Fin r,
        (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then wq κ i j else 0) =
          (if i = i0 ∧ j = j0 then wq κ i j else 0) +
            (if i = j0 ∧ j = i0 then wq κ i j else 0) := by
      intro i j
      by_cases hA : i = i0 ∧ j = j0
      · have hB : ¬ (i = j0 ∧ j = i0) := fun hB => hij (hA.1.symm.trans hB.1)
        rw [if_pos (Or.inl hA), if_pos hA, if_neg hB, add_zero]
      · by_cases hB : i = j0 ∧ j = i0
        · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB, zero_add]
        · rw [if_neg (not_or.2 ⟨hA, hB⟩), if_neg hA, if_neg hB, zero_add]
    simp only [hsplit, sum_add_distrib]
    rw [sum_pair (fun i j => wq κ i j), sum_pair (fun i j => wq κ i j)]
    simp only [hf]
    rw [prod_eq_mul i0 j0 hij (fun c _ hc => by simp [hc.1, hc.2])
      (fun h => absurd (mem_univ _) h) (fun h => absurd (mem_univ _) h)]
    have hji : j0 ≠ i0 := fun h => hij h.symm
    simp only [wq, if_neg hij, if_neg hji, if_true, add_zero, zero_add,
      Nat.descFactorial_one]
    ring

lemma sum_two_of_delta (f : Fin r → ℕ) (i j : Fin r)
    (h : ∀ k, f k = (if k = i then 1 else 0) + (if k = j then 1 else 0)) : ∑ k, f k = 2 := by
  simp [h, sum_add_distrib]

/-! ## The coefficients -/
/-- The predicate of `card_second_order`. -/
def PcC (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1)) (i j : Fin r) : Prop :=
  nv c + 1 = Ecount u c + Fcount u c ∧
    ∀ k, fK u c k = (if k = i then 1 else 0) + (if k = j then 1 else 0)

def alphaC (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ :=
  if nv c = Ecount u c + Fcount u c then c0f (nv c) (eK u c) (fK u c)
  else if nv c + 1 = Ecount u c + Fcount u c ∧ Fcount u c ≤ 1 then 1 - ∑ i, (fK u c i : ℝ)
  else 0

def betaC (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) : ℝ :=
  if nv c = Ecount u c + Fcount u c then -(eK u c i : ℝ)
  else if nv c + 1 = Ecount u c + Fcount u c ∧ Fcount u c ≤ 1 then (fK u c i : ℝ)
  else 0

lemma Tc_eq (u : List (Lt 0 r)) (κ : Fin r → ℕ) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hc : c ∈ CGL u) :
    Tc u κ c = alphaC u c + ∑ i, (κ i : ℝ) * betaC u c i +
      ∑ i, ∑ j, if PcC u c i j then wq κ i j else 0 := by
  by_cases h0 : nv c = Ecount u c + Fcount u c
  · have hP : ∀ i j, PcC u c i j ↔ False := fun i j =>
      iff_false_intro fun h => by have := h.1; omega
    simp only [Tc, alphaC, betaC, if_pos h0, hP, if_false, sum_const_zero, add_zero]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    exact sum_congr rfl fun i _ => by ring
  · by_cases h1 : nv c + 1 = Ecount u c + Fcount u c
    · have hF2 : Fcount u c ≤ 2 := by
        have := nv_le_ecount_succ u c hc
        omega
      by_cases hF1 : Fcount u c ≤ 1
      · have hP : ∀ i j, PcC u c i j ↔ False := fun i j =>
          iff_false_intro fun h => by
            have := sum_two_of_delta (fK u c) i j h.2
            unfold Fcount at hF1
            omega
        simp only [Tc, alphaC, betaC, if_neg h0, if_pos h1, if_pos (And.intro h1 hF1), hP,
          if_false, sum_const_zero, add_zero]
        exact prod_le_one κ (fK u c) hF1
      · have hF : Fcount u c = 2 := by omega
        have hn : ¬ (nv c + 1 = Ecount u c + Fcount u c ∧ Fcount u c ≤ 1) := fun h => hF1 h.2
        simp only [Tc, alphaC, betaC, if_neg h0, if_pos h1, if_neg hn, mul_zero,
          sum_const_zero, add_zero, zero_add]
        rw [prod_two κ (fK u c) hF]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        by_cases hk : ∀ k, fK u c k = (if k = i then 1 else 0) + (if k = j then 1 else 0)
        · rw [if_pos hk, if_pos (show PcC u c i j from ⟨h1, hk⟩)]
        · rw [if_neg hk, if_neg (fun h : PcC u c i j => hk h.2)]
    · have hP : ∀ i j, PcC u c i j ↔ False := fun i j => iff_false_intro fun h => h1 h.1
      have hn : ¬ (nv c + 1 = Ecount u c + Fcount u c ∧ Fcount u c ≤ 1) := fun h => h1 h.1
      simp only [Tc, alphaC, betaC, if_neg h0, if_neg h1, if_neg hn, hP, if_false, mul_zero,
        sum_const_zero, add_zero]

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
/-!
# Part W: second-order two-loop colourings are the fold colourings

The colourings of a cyclically reduced word `u` with `v + 1 = e + f` and two loops are exactly
the colourings `canon (fx L p d)` of the back-and-forth walks on a path with `d` vertices whose
first loop is read at time `p`, for the pairs `(p, d)` such that the letters of `u` factor through
the labels `lb p d` (`Qp`).
-/
/-! ## The fold at explicit times -/
lemma fv_p {p d : ℕ} (hpd : p < d) : fv p d p = 0 := by
  unfold fv; rw [mm_lo hpd le_rfl]; split_ifs <;> omega

lemma fv_at {p d w : ℕ} (hpd : p < d) (hw : w < d) : fv p d (p + 1 + w) = w := by
  unfold fv; rw [mm_hi hpd (by omega) (by omega)]; split_ifs <;> omega

lemma fv_p1 {p d : ℕ} (hpd : p < d) : fv p d (p + 1) = 0 := fv_at hpd (w := 0) (by omega)

lemma fv_pd {p d : ℕ} (hpd : p < d) : fv p d (p + d) = d - 1 := by
  have := fv_at hpd (w := d - 1) (by omega)
  rwa [show p + 1 + (d - 1) = p + d by omega] at this

lemma fv_pd1 {p d : ℕ} (hpd : p < d) : fv p d (p + d + 1) = d - 1 := by
  unfold fv; rw [mm_hi hpd (by omega) (by omega)]; split_ifs <;> omega

lemma lb_at {p d κ : ℕ} (hpd : p < d) (hκ : κ ≤ d) : lb p d (p + κ) = κ := by
  unfold lb
  rcases Nat.eq_zero_or_pos κ with rfl | h
  · rw [add_zero, mm_lo hpd le_rfl]; split_ifs <;> omega
  · rw [mm_hi hpd (by omega) (by omega)]; split_ifs <;> omega

lemma fv_per {p d L : ℕ} (hdvd : 2 * d ∣ L) (t : ℕ) : fv p d (t + L) = fv p d t := by
  unfold fv; rw [mm_per hdvd]

lemma fv_noloop_lo {p d t : ℕ} (hpd : p < d) (ht : t < p) : fv p d t ≠ fv p d (t + 1) := by
  unfold fv; rw [mm_lo hpd (by omega), mm_lo hpd (by omega)]; split_ifs <;> omega

lemma fv_noloop_mid {p d t : ℕ} (hpd : p < d) (h1 : p < t) (h2 : t < p + d) :
    fv p d t ≠ fv p d (t + 1) := by
  unfold fv; rw [mm_hi hpd (by omega) (by omega), mm_hi hpd (by omega) (by omega)]
  split_ifs <;> omega

lemma pair_form {p d : ℕ} (hd : 1 ≤ d) (t : ℕ) (h : fv p d t ≠ fv p d (t + 1)) :
    1 ≤ lb p d t ∧ lb p d t ≤ d - 1 ∧
      s(fv p d t, fv p d (t + 1)) = s(lb p d t - 1, lb p d t) := by
  rcases fold_cases (p := p) hd t with ⟨hc, -⟩ | ⟨h1, h2, ⟨c1, c2⟩ | ⟨c1, c2⟩⟩
  · exact absurd hc h
  · refine ⟨h1, h2, ?_⟩
    rw [c2, ← c1, Nat.add_sub_cancel]
  · refine ⟨h1, h2, ?_⟩
    rw [c1, ← c2, Nat.add_sub_cancel]
    exact Sym2.eq_swap

lemma loop_form {p d : ℕ} (hd : 1 ≤ d) (t : ℕ) (h : fv p d t = fv p d (t + 1)) :
    (lb p d t = 0 ∧ fv p d t = 0) ∨ (lb p d t = d ∧ fv p d t = d - 1) := by
  rcases fold_cases (p := p) hd t with ⟨-, hc⟩ | ⟨h1, h2, hc⟩
  · exact hc
  · omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {β γ : Type*} [DecidableEq β] [DecidableEq γ] (u : List (Lt 0 r))
  (c : Fin (u.length + 1) → β) (x : Fin (u.length + 1) → γ)
  (hk : ∀ s t, c s = c t ↔ x s = x t)
/-! ## Invariance under the kernel -/
include hk in
lemma nv_ker : nv c = nv x := by
  unfold nv
  exact card_image_ker _ _ _ (fun s _ t _ => hk s t)

include hk in
lemma card_Ps_ker (k : Fin r) : (Ps u c k).card = (Ps u x k).card := by
  unfold Ps
  have hfilt : (univ.filter fun t : Fin u.length =>
      u.get t = Sum.inr k ∧ c t.castSucc ≠ c t.succ) =
      univ.filter fun t => u.get t = Sum.inr k ∧ x t.castSucc ≠ x t.succ := by
    ext t; simp only [mem_filter, mem_univ, true_and, ne_eq, hk]
  rw [hfilt]
  apply card_image_ker
  intro s _ t _
  simp only [Sym2.eq_iff, hk]

include hk in
lemma card_Ls_ker (k : Fin r) : (Ls u c k).card = (Ls u x k).card := by
  unfold Ls
  have hfilt : (univ.filter fun t : Fin u.length =>
      u.get t = Sum.inr k ∧ c t.castSucc = c t.succ) =
      univ.filter fun t => u.get t = Sum.inr k ∧ x t.castSucc = x t.succ := by
    ext t; simp only [mem_filter, mem_univ, true_and, hk]
  rw [hfilt]
  apply card_image_ker
  intro s _ t _
  exact hk _ _

include hk in
lemma goodL_ker (h : GoodL u x) : GoodL u c := by
  obtain ⟨h1, h2, h3⟩ := h
  have mP : ∀ k (t : Fin u.length), u.get t = Sum.inr k → c t.castSucc ≠ c t.succ →
      s(x t.castSucc, x t.succ) ∈ Ps u x k := fun k t ht hne =>
    mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, ht, fun h => hne ((hk _ _).2 h)⟩, rfl⟩
  refine ⟨fun k => ⟨?_, ?_⟩, ?_, (hk _ _).2 h3⟩
  · intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hq
    rw [Sym2.mk_isDiag_iff]
    exact (mem_filter.1 ht).2.2
  · rintro q hq q' hq' ⟨w, hw, hw'⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hq
    obtain ⟨t', ht', rfl⟩ := mem_image.1 hq'
    have ht2 := (mem_filter.1 ht).2
    have ht2' := (mem_filter.1 ht').2
    have hshare : ∃ w', w' ∈ s(x t.castSucc, x t.succ) ∧ w' ∈ s(x t'.castSucc, x t'.succ) := by
      rw [Sym2.mem_iff] at hw hw'
      rcases hw with rfl | rfl <;> rcases hw' with h | h
      · exact ⟨x t.castSucc, Sym2.mem_mk_left _ _, by rw [(hk _ _).1 h]; exact Sym2.mem_mk_left _ _⟩
      · exact ⟨x t.castSucc, Sym2.mem_mk_left _ _, by rw [(hk _ _).1 h]; exact Sym2.mem_mk_right _ _⟩
      · exact ⟨x t.succ, Sym2.mem_mk_right _ _, by rw [(hk _ _).1 h]; exact Sym2.mem_mk_left _ _⟩
      · exact ⟨x t.succ, Sym2.mem_mk_right _ _, by rw [(hk _ _).1 h]; exact Sym2.mem_mk_right _ _⟩
    have := (h1 k).2 _ (mP k t ht2.1 ht2.2) _ (mP k t' ht2'.1 ht2'.2) hshare
    rw [Sym2.eq_iff] at this ⊢
    simp only [hk]
    exact this
  · intro k w hw q hq hwq
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hw
    obtain ⟨t', ht', rfl⟩ := mem_image.1 hq
    have ht2 := (mem_filter.1 ht).2
    have ht2' := (mem_filter.1 ht').2
    have mL : x t.castSucc ∈ Ls u x k :=
      mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, ht2.1, (hk _ _).1 ht2.2⟩, rfl⟩
    refine h2 k _ mL _ (mP k t' ht2'.1 ht2'.2) ?_
    rw [Sym2.mem_iff] at hwq ⊢
    simpa only [hk] using hwq

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
lemma Xc_fin {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (hcl : c 0 = c (Fin.last L))
    (t : Fin (L + 1)) : c t = Xc c t.val := by
  rcases Nat.lt_or_ge t.val L with h | h
  · exact (Xc_lt c h).symm
  · have ht : t.val = L := by have := t.2; omega
    rw [ht, Xc_L, hcl]; congr 1; exact Fin.ext ht

/-! ## The fold colouring -/
/-- The back-and-forth walk as a path with values in `ℕ`. -/
def fx (L p d : ℕ) : Fin (L + 1) → ℕ := fun t => fv p d t.val

lemma Xc_fx {L p d : ℕ} (hL : 0 < L) (hdvd : 2 * d ∣ L) : Xc (fx L p d) = fv p d := by
  funext t
  unfold Xc fx
  simp only
  rw [show min (t % L) L = t % L from Nat.min_eq_left (Nat.mod_lt t hL).le]
  exact (per_mod (fv_per hdvd) t).symm

lemma fx_closed {L p d : ℕ} (hdvd : 2 * d ∣ L) : fx L p d 0 = fx L p d (Fin.last L) := by
  have := fv_per (p := p) hdvd 0
  rw [zero_add] at this
  exact this.symm

lemma nv_fx {L p d : ℕ} (hpd : p < d) (h2 : 2 * d ≤ L) : nv (fx L p d) = d := by
  unfold nv
  have : univ.image (fx L p d) = range d := by
    ext w
    simp only [mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨t, rfl⟩; exact fv_lt (by omega)
    · intro hw
      exact ⟨⟨p + 1 + w, by omega⟩, fv_at hpd hw⟩
  rw [this, card_range]

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
variable (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u) {p d : ℕ} (hpd : p < d)
  (hdvd : 2 * d ∣ u.length)
  (hfac : ∀ τ τ', lb p d τ = lb p d τ' → ac u hne τ = ac u hne τ')
include hpd hfac in
lemma a_lb (t : ℕ) : ac u hne t = ac u hne (p + lb p d t) :=
  hfac _ _ (lb_at hpd (lb_le (by omega))).symm

include hcr hpd hdvd hfac in
lemma goodL_fx : GoodL u (fx u.length p d) := by
  have hL := List.length_pos_iff.2 hne
  have hd : 1 ≤ d := by omega
  have hcl := fx_closed (L := u.length) (p := p) hdvd
  have hX := Xc_fx (p := p) hL hdvd
  have ha := a_lb u hne hpd hfac
  have hadj : ∀ κ, ac u hne (p + (κ + 1)) ≠ ac u hne (p + κ) := fun κ => ac_cr u hne hcr (p + κ)
  refine ⟨fun k => ⟨?_, ?_⟩, ?_, hcl⟩
  · intro q hq
    rw [mem_Ps u hne _ hcl] at hq
    obtain ⟨t, -, -, h2, rfl⟩ := hq
    rw [Sym2.mk_isDiag_iff]; exact h2
  · rintro q hq q' hq' ⟨w, hw, hw'⟩
    rw [mem_Ps u hne _ hcl] at hq hq'
    obtain ⟨t, -, h1, h2, rfl⟩ := hq
    obtain ⟨t', -, h1', h2', rfl⟩ := hq'
    rw [hX] at h2 h2' hw hw' ⊢
    obtain ⟨b1, b2, b3⟩ := pair_form hd t h2
    obtain ⟨b1', b2', b3'⟩ := pair_form hd t' h2'
    rw [b3] at hw ⊢
    rw [b3'] at hw' ⊢
    rw [Sym2.mem_iff] at hw hw'
    have e : ac u hne (p + lb p d t) = ac u hne (p + lb p d t') := by
      rw [← ha, ← ha, h1, h1']
    have : lb p d t = lb p d t' := by
      by_contra hne'
      rcases (by omega : lb p d t' = lb p d t + 1 ∨ lb p d t = lb p d t' + 1) with h | h
      · rw [h] at e; exact hadj _ e.symm
      · rw [h] at e; exact hadj _ e
    rw [this]
  · intro k w hw q hq hwq
    rw [mem_Ls u hne _ hcl] at hw
    rw [mem_Ps u hne _ hcl] at hq
    obtain ⟨t, -, h1, h2, rfl⟩ := hw
    obtain ⟨t', -, h1', h2', rfl⟩ := hq
    rw [hX] at h2 h2' hwq
    obtain ⟨b1', b2', b3'⟩ := pair_form hd t' h2'
    rw [b3', Sym2.mem_iff] at hwq
    have e : ac u hne (p + lb p d t) = ac u hne (p + lb p d t') := by
      rw [← ha, ← ha, h1, h1']
    rcases loop_form hd t h2 with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · have h3 : p + lb p d t' = p + (0 + 1) := by omega
      have h4 : p + lb p d t = p + 0 := by omega
      rw [h3, h4] at e; exact hadj 0 e.symm
    · have h3 : p + lb p d t = p + (lb p d t' + 1) := by omega
      rw [h3] at e; exact hadj _ e

include hpd hdvd hfac in
lemma EE_fx : EE (ac u hne) (fv p d) u.length =
    (Icc 1 (d - 1)).image (fun κ => (ac u hne (p + κ), s(κ - 1, κ))) := by
  have hL := List.length_pos_iff.2 hne
  have hd : 1 ≤ d := by omega
  have hL2 : 2 * d ≤ u.length := Nat.le_of_dvd hL hdvd
  have ha := a_lb u hne hpd hfac
  ext e
  simp only [EE, mem_image, mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨t, ⟨-, h2⟩, rfl⟩
    obtain ⟨b1, b2, b3⟩ := pair_form hd t h2
    refine ⟨lb p d t, ⟨b1, b2⟩, ?_⟩
    simp only [pe]
    rw [b3, ← ha t]
  · rintro ⟨κ, ⟨h1, h2⟩, rfl⟩
    have f1 : fv p d (p + κ) = κ - 1 := by
      have := fv_at hpd (w := κ - 1) (by omega)
      rwa [show p + 1 + (κ - 1) = p + κ by omega] at this
    have f2 : fv p d (p + κ + 1) = κ := by
      have := fv_at hpd (w := κ) (by omega)
      rwa [show p + 1 + κ = p + κ + 1 by omega] at this
    refine ⟨p + κ, ⟨by omega, by rw [f1, f2]; omega⟩, ?_⟩
    simp only [pe]
    rw [f1, f2]

include hpd hdvd hfac in
lemma card_EE_fx : (EE (ac u hne) (fv p d) u.length).card = d - 1 := by
  rw [EE_fx u hne hpd hdvd hfac, card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro κ hκ κ' hκ' h
    simp only [coe_Icc, Set.mem_Icc] at hκ hκ'
    simp only [Prod.mk.injEq, Sym2.eq_iff] at h
    omega

include hcr hpd in
lemma loops_ne : (ac u hne p, 0) ≠ (ac u hne (p + d), d - 1) := by
  intro h
  rw [Prod.mk.injEq] at h
  have hd : d = 1 := by omega
  rw [hd] at h
  exact ac_cr u hne hcr p h.1.symm

include hpd hdvd hfac in
lemma LL_fx : LL (ac u hne) (fv p d) u.length =
    {(ac u hne p, 0), (ac u hne (p + d), d - 1)} := by
  have hL := List.length_pos_iff.2 hne
  have hd : 1 ≤ d := by omega
  have hL2 : 2 * d ≤ u.length := Nat.le_of_dvd hL hdvd
  have ha := a_lb u hne hpd hfac
  ext e
  simp only [LL, mem_image, mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨t, ⟨-, h2⟩, rfl⟩
    rcases loop_form hd t h2 with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · left; rw [ha t, c1, c2]; rfl
    · right; rw [ha t, c1, c2]
  · rintro (rfl | rfl)
    · exact ⟨p, ⟨by omega, by rw [fv_p hpd, fv_p1 hpd]⟩, by rw [fv_p hpd]⟩
    · exact ⟨p + d, ⟨by omega, by rw [fv_pd hpd, fv_pd1 hpd]⟩, by rw [fv_pd hpd]⟩

/-- The number of loops of colour `k` among two distinct loops. -/
lemma card_filter_pair {γ : Type*} [DecidableEq γ] {e0 e1 : Fin r × γ} (hne : e0 ≠ e1)
    (k : Fin r) :
    (({e0, e1} : Finset (Fin r × γ)).filter (fun e => e.1 = k)).card =
      (if k = e0.1 then 1 else 0) + (if k = e1.1 then 1 else 0) := by
  rw [filter_insert, filter_singleton]
  by_cases h0 : e0.1 = k <;> by_cases h1 : e1.1 = k
  · rw [if_pos h0, if_pos h1, if_pos h0.symm, if_pos h1.symm, card_pair hne]
  · rw [if_pos h0, if_neg h1, if_pos h0.symm, if_neg (Ne.symm h1)]; simp
  · rw [if_neg h0, if_pos h1, if_neg (Ne.symm h0), if_pos h1.symm]; simp
  · rw [if_neg h0, if_neg h1, if_neg (Ne.symm h0), if_neg (Ne.symm h1)]; simp

include hcr hpd hdvd hfac in
/-- The fold colouring is a second-order colouring with two loops. -/
theorem fcol_mem :
    canon (fx u.length p d) ∈ CGL u ∧
      nv (canon (fx u.length p d)) + 1 =
        Ecount u (canon (fx u.length p d)) + Fcount u (canon (fx u.length p d)) ∧
      ∀ k, fK u (canon (fx u.length p d)) k =
        (if k = ac u hne p then 1 else 0) + (if k = ac u hne (p + d) then 1 else 0) := by
  have hL := List.length_pos_iff.2 hne
  have hd : 1 ≤ d := by omega
  have hL2 : 2 * d ≤ u.length := Nat.le_of_dvd hL hdvd
  have hcl := fx_closed (L := u.length) (p := p) hdvd
  have hX := Xc_fx (p := p) hL hdvd
  have hk : ∀ s t, canon (fx u.length p d) s = canon (fx u.length p d) t ↔
      fx u.length p d s = fx u.length p d t := canon_ker _
  have hF : ∀ k, (Ls u (canon (fx u.length p d)) k).card =
      (if k = ac u hne p then 1 else 0) + (if k = ac u hne (p + d) then 1 else 0) := by
    intro k
    rw [card_Ls_ker u _ _ hk, card_Ls_eq u hne _ hcl, hX, LL_fx u hne hpd hdvd hfac,
      card_filter_pair (loops_ne u hne hcr hpd)]
  have hE : Ecount u (canon (fx u.length p d)) = d - 1 := by
    have : Ecount u (canon (fx u.length p d)) = ∑ k, (Ps u (fx u.length p d) k).card :=
      sum_congr rfl fun k _ => card_Ps_ker u _ _ hk k
    rw [this, sum_card_Ps u hne _ hcl, hX, card_EE_fx u hne hpd hdvd hfac]
  have hFc : Fcount u (canon (fx u.length p d)) = 2 := by
    have : Fcount u (canon (fx u.length p d)) = ∑ k, (Ls u (fx u.length p d) k).card :=
      sum_congr rfl fun k _ => card_Ls_ker u _ _ hk k
    rw [this, sum_card_Ls u hne _ hcl, hX, LL_fx u hne hpd hdvd hfac,
      card_pair (loops_ne u hne hcr hpd)]
  refine ⟨mem_CGL.2 ⟨canon_canon _, goodL_ker u _ _ hk (goodL_fx u hne hcr hpd hdvd hfac)⟩,
    ?_, hF⟩
  rw [nv_ker u _ _ hk, nv_fx hpd hL2, hE, hFc]
  omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- The fold colouring determines `(p, d)`. -/
theorem fcol_inj {L p d p' d' : ℕ} (hpd : p < d) (hpd' : p' < d') (h2 : 2 * d ≤ L)
    (h2' : 2 * d' ≤ L) (h : canon (fx L p d) = canon (fx L p' d')) : p = p' ∧ d = d' := by
  have hk : ∀ s t, s ≤ L → t ≤ L → (fv p d s = fv p d t ↔ fv p' d' s = fv p' d' t) := by
    intro s t hs ht
    have h1 := canon_ker (fx L p d) ⟨s, by omega⟩ ⟨t, by omega⟩
    have h2 := canon_ker (fx L p' d') ⟨s, by omega⟩ ⟨t, by omega⟩
    rw [h] at h1
    exact h1.symm.trans h2
  have key : ∀ {p d p' d' : ℕ}, p < d → p' < d' → 2 * d ≤ L → 2 * d' ≤ L →
      (∀ s t, s ≤ L → t ≤ L → (fv p d s = fv p d t ↔ fv p' d' s = fv p' d' t)) →
      p' ≤ p ∧ (p = p' → d' ≤ d) := by
    intro p d p' d' hpd hpd' h2 h2' hk
    have hl : fv p d p = fv p d (p + 1) := by rw [fv_p hpd, fv_p1 hpd]
    constructor
    · by_contra hlt
      exact fv_noloop_lo hpd' (by omega) ((hk p (p + 1) (by omega) (by omega)).1 hl)
    · rintro rfl
      by_contra hlt
      have hl' : fv p d (p + d) = fv p d (p + d + 1) := by rw [fv_pd hpd, fv_pd1 hpd]
      exact fv_noloop_mid hpd' (by omega) (by omega)
        ((hk (p + d) (p + d + 1) (by omega) (by omega)).1 hl')
  obtain ⟨k1, k2⟩ := key hpd hpd' h2 h2' hk
  obtain ⟨k3, k4⟩ := key hpd' hpd h2' h2 (fun s t hs ht => (hk s t hs ht).symm)
  have hp : p = p' := by omega
  exact ⟨hp, by have := k2 hp; have := k4 hp.symm; omega⟩

lemma two_colours {i j x y : Fin r}
    (h : ∀ k : Fin r, (if k = i then 1 else 0) + (if k = j then 1 else 0) =
      (if k = x then 1 else 0) + (if k = y then 1 else 0)) :
    (x = j ∧ y = i) ∨ (x = i ∧ y = j) := by
  by_cases hxi : x = i
  · by_cases hyj : y = j
    · exact Or.inr ⟨hxi, hyj⟩
    · exfalso
      have := h y
      rw [hxi, if_neg hyj, if_pos (rfl : y = y)] at this
      omega
  · have hxj : x = j := by
      by_contra hxj
      have := h x
      rw [if_neg hxi, if_neg hxj, if_pos (rfl : x = x)] at this
      omega
    have hyi : y = i := by
      by_contra hyi
      have := h y
      rw [hxj, if_neg hyi, if_pos (rfl : y = y)] at this
      omega
    exact Or.inl ⟨hxj, hyi⟩

/-- Every second-order colouring with two loops is a fold colouring. -/
theorem exists_fold (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CGL u)
    (hve : nv c + 1 = Ecount u c + Fcount u c) (i j : Fin r)
    (hf : ∀ k, fK u c k = (if k = i then 1 else 0) + (if k = j then 1 else 0)) :
    ∃ p d, p < d ∧ 2 * d ∣ u.length ∧
      (∀ τ τ', lb p d τ = lb p d τ' → ac u hne τ = ac u hne τ') ∧
      ((ac u hne p = j ∧ ac u hne (p + d) = i) ∨ (ac u hne p = i ∧ ac u hne (p + d) = j)) ∧
      c = canon (fx u.length p d) := by
  have hL := List.length_pos_iff.2 hne
  obtain ⟨hcan, hgood⟩ := mem_CGL.1 hc
  have hcl := hgood.2.2
  have hF2 : Fcount u c = 2 := by
    unfold Fcount
    simp only [hf]
    rw [sum_add_distrib]
    simp
  have hv : nv c = Ecount u c + 1 := by omega
  have tw := tw_of_eq u hne hcr c hcl hv
  have hFm : ∀ t, Xc c t = Xc c (t + 1) →
      (ac u hne t, Xc c t) ∈ LL (ac u hne) (Xc c) u.length :=
    fun t ht => mem_LL_of_loop hL (Xc_per c) (ac_per u hne) ht
  have hcard : (LL (ac u hne) (Xc c) u.length).card = 2 := by
    rw [← Fcount_eq u hne c hcl, hF2]
  obtain ⟨p, d, hpd, hdvd, hinj, hstr⟩ := tw.structure1 _ hFm hcard
  have hd : 1 ≤ d := by omega
  have hfac : ∀ τ τ', lb p d τ = lb p d τ' → ac u hne τ = ac u hne τ' := by
    intro τ τ' h
    rw [(hstr τ).2, (hstr τ').2, h]
  -- the two loops
  have hX0 : Xc c p = Xc c (p + 1 + 0) := by
    have := (hstr p).1; rwa [fv_p hpd] at this
  have hX1 : Xc c (p + 1) = Xc c (p + 1 + 0) := rfl
  have hXd : Xc c (p + d) = Xc c (p + 1 + (d - 1)) := by
    have := (hstr (p + d)).1; rwa [fv_pd hpd] at this
  have hXd1 : Xc c (p + d + 1) = Xc c (p + 1 + (d - 1)) := by
    have := (hstr (p + d + 1)).1; rwa [fv_pd1 hpd] at this
  have m0 := hFm p (hX0.trans hX1.symm)
  have md := hFm (p + d) (hXd.trans hXd1.symm)
  have hne2 : (ac u hne p, Xc c p) ≠ (ac u hne (p + d), Xc c (p + d)) := by
    intro h
    rw [Prod.mk.injEq] at h
    rcases Nat.lt_or_ge 1 d with hd2 | hd2
    · have := hinj 0 (d - 1) (by omega) (by omega) (by rw [← hX0, ← hXd]; exact h.2)
      omega
    · have hd' : d = 1 := by omega
      rw [hd'] at h
      exact ac_cr u hne hcr p h.1.symm
  have hFeq : LL (ac u hne) (Xc c) u.length =
      {(ac u hne p, Xc c p), (ac u hne (p + d), Xc c (p + d))} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [card_pair hne2, hcard])
    intro e he
    rcases mem_insert.1 he with rfl | he
    · exact m0
    · rw [mem_singleton.1 he]; exact md
  have hfk : ∀ k, (if k = i then 1 else 0) + (if k = j then 1 else 0) =
      (if k = ac u hne p then 1 else 0) + (if k = ac u hne (p + d) then 1 else 0) := by
    intro k
    rw [← hf k]
    show (Ls u c k).card = _
    rw [card_Ls_eq u hne c hcl, hFeq, card_filter_pair hne2]
  have hcol : (ac u hne p = j ∧ ac u hne (p + d) = i) ∨
      (ac u hne p = i ∧ ac u hne (p + d) = j) := by
    exact two_colours hfk
  refine ⟨p, d, hpd, hdvd, hfac, hcol, ?_⟩
  rw [← hcan]
  apply canon_eq_of_ker
  intro s t
  rw [Xc_fin c hcl s, Xc_fin c hcl t, (hstr s.val).1, (hstr t.val).1]
  constructor
  · intro h
    exact hinj _ _ (fv_lt hd) (fv_lt hd) h
  · intro h
    show Xc c (p + 1 + fv p d s.val) = Xc c (p + 1 + fv p d t.val)
    have h' : fv p d s.val = fv p d t.val := h
    rw [h']

/-! ## The count -/
/-- The letters of `u` factor through the labels of the fold `(p, d)`, with first loop letter
`j` and second loop letter `i`. -/
def Qp (u : List (Lt 0 r)) (hne : u ≠ []) (p d : ℕ) (j i : Fin r) : Prop :=
  p < d ∧ 2 * d ∣ u.length ∧
    (∀ τ τ', lb p d τ = lb p d τ' → ac u hne τ = ac u hne τ') ∧
    ac u hne p = j ∧ ac u hne (p + d) = i

/-- The folds of `u` with first loop letter `j` and second loop letter `i`. -/
def Par (u : List (Lt 0 r)) (hne : u ≠ []) (j i : Fin r) : Finset (ℕ × ℕ) :=
  ((range u.length) ×ˢ (range (u.length + 1))).filter fun pd => Qp u hne pd.1 pd.2 j i

theorem card_second_eq (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u) (i j : Fin r) :
    ((CGL u).filter fun c => nv c + 1 = Ecount u c + Fcount u c ∧
        ∀ k, fK u c k = (if k = i then 1 else 0) + (if k = j then 1 else 0)).card =
      (Par u hne j i ∪ Par u hne i j).card := by
  have hL := List.length_pos_iff.2 hne
  symm
  refine Finset.card_bij (fun pd _ => canon (fx u.length pd.1 pd.2)) ?_ ?_ ?_
  · rintro ⟨p, d⟩ hpd
    simp only [Par, mem_union, mem_filter] at hpd
    rcases hpd with ⟨-, h1, h2, h3, h4, h5⟩ | ⟨-, h1, h2, h3, h4, h5⟩
    · obtain ⟨k1, k2, k3⟩ := fcol_mem u hne hcr h1 h2 h3
      refine mem_filter.2 ⟨k1, k2, fun k => ?_⟩
      rw [k3 k, h4, h5, add_comm]
    · obtain ⟨k1, k2, k3⟩ := fcol_mem u hne hcr h1 h2 h3
      refine mem_filter.2 ⟨k1, k2, fun k => ?_⟩
      rw [k3 k, h4, h5]
  · rintro ⟨p, d⟩ hpd ⟨p', d'⟩ hpd' heq
    have hA : p < d ∧ 2 * d ≤ u.length := by
      simp only [Par, mem_union, mem_filter] at hpd
      rcases hpd with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ <;> exact ⟨h1, Nat.le_of_dvd hL h2⟩
    have hB : p' < d' ∧ 2 * d' ≤ u.length := by
      simp only [Par, mem_union, mem_filter] at hpd'
      rcases hpd' with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ <;> exact ⟨h1, Nat.le_of_dvd hL h2⟩
    obtain ⟨e1, e2⟩ := fcol_inj hA.1 hB.1 hA.2 hB.2 heq
    rw [e1, e2]
  · intro c hc
    obtain ⟨hc1, hc2, hc3⟩ := mem_filter.1 hc
    obtain ⟨p, d, hpd, hdvd, hfac, hcol, rfl⟩ := exists_fold u hne hcr c hc1 hc2 i j hc3
    have h2 : 2 * d ≤ u.length := Nat.le_of_dvd hL hdvd
    refine ⟨(p, d), ?_, rfl⟩
    simp only [Par, mem_union, mem_filter, mem_product, mem_range]
    rcases hcol with h | h
    · exact Or.inl ⟨⟨by omega, by omega⟩, hpd, hdvd, hfac, h.1, h.2⟩
    · exact Or.inr ⟨⟨by omega, by omega⟩, hpd, hdvd, hfac, h.1, h.2⟩

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r s : ℕ}
/-!
# Part W, words: the two-loop factorizations of a cyclically reduced word and `C2count`

The first half is the reduced-word toolkit of Part F (normal forms by van der Waerden's trick),
copied here because Parts do not import each other.  The second half identifies the folds
`Par u j i` with the tuples counted by `C2count i j (a * wprod u * a⁻¹)`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

theorem wprod_singleton (a : Lt r s) : wprod [a] = genL a := by simp

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem push_of_red_cons {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) :
    push a t = a :: t := by
  cases t with
  | nil => rfl
  | cons b t => exact push_cons_ne _ _ _ (red_cons_cons.1 h).1

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

theorem red_nf (g : G r s) : Red (nf g) := (hom r s g ⟨[], red_nil⟩).2

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem hom_wprod_nil (u : List (Lt r s)) (hu : Red u) :
    hom r s (wprod u) ⟨[], red_nil⟩ = ⟨u, hu⟩ := by
  induction u with
  | nil => simp
  | cons a t ih =>
    apply Subtype.ext
    rw [wprod_cons, hom_genL_mul, ih (Red.tail' hu)]
    exact push_of_red_cons hu

theorem nf_wprod' (u : List (Lt r s)) (hu : Red u) : nf (wprod u) = u :=
  congrArg Subtype.val (hom_wprod_nil u hu)

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem nf_injective : Function.Injective (nf : G r s → List (Lt r s)) := by
  intro g h e
  rw [← wprod_nf g, e, wprod_nf]

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

theorem len_wprod_le (u : List (Lt r s)) : len (wprod u) ≤ u.length := len_le_of_wprod rfl

theorem len_wprod_of_red {u : List (Lt r s)} (hu : Red u) : len (wprod u) = u.length := by
  rw [len_eq_length_nf, nf_wprod' u hu]

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/
theorem nf_wprod {u : List (Lt r s)} (h : Red u) : nf (wprod u) = u := nf_wprod' u h

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/
theorem gid_cancel {H : Type*} [Group H] (x a y : H) : x * (a * (a⁻¹ * y)) = x * y := by group

theorem red_left {u v : List (Lt r s)} (h : Red (u ++ v)) : Red u := List.IsChain.left_of_append h

theorem red_right {u v : List (Lt r s)} (h : Red (u ++ v)) : Red v :=
  List.IsChain.right_of_append h

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

theorem ibar_cons (a : Lt r s) (u : List (Lt r s)) : ibar (a :: u) = ibar u ++ [bar a] := by
  simp [ibar]

@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

theorem wprod_ibar (u : List (Lt r s)) : wprod (ibar u) = (wprod u)⁻¹ := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [ibar_cons, wprod_append, ih, wprod_cons a u, wprod_singleton, genL_bar]
    exact (mul_inv_rev (G := G r s) _ _).symm

/-! ## Non-reduced words are not shortest -/
theorem not_red_split {u : List (Lt r s)} (h : ¬ Red u) :
    ∃ x a y, u = x ++ a :: bar a :: y := by
  induction u with
  | nil => exact absurd red_nil h
  | cons a t ih =>
    cases t with
    | nil => exact absurd (List.isChain_singleton a) h
    | cons b t =>
      by_cases hb : b = bar a
      · exact ⟨[], a, t, by simp [hb]⟩
      · have : ¬ Red (b :: t) := fun h' => h (List.isChain_cons_cons.2 ⟨hb, h'⟩)
        obtain ⟨x, c, y, e⟩ := ih this
        exact ⟨a :: x, c, y, by simp [e]⟩

/-- A word of minimal length is reduced. -/
theorem red_of_length {u : List (Lt r s)} {g : G r s} (h : wprod u = g)
    (hl : u.length = len g) : Red u := by
  by_contra hr
  obtain ⟨x, a, y, rfl⟩ := not_red_split hr
  have h2 : wprod (x ++ y) = g := by
    rw [← h, wprod_append, wprod_append, wprod_cons, wprod_cons, genL_bar]
    exact (gid_cancel (H := G r s) _ _ _).symm
  have h3 := len_wprod_le (x ++ y)
  rw [h2] at h3
  simp at hl h3
  omega

/-- A word of length `len` of its product is the normal form. -/
theorem eq_nf_of_length {u : List (Lt r s)} {g : G r s} (h : wprod u = g)
    (hl : u.length = len g) : nf g = u := by
  rw [← h]
  exact nf_wprod (red_of_length h hl)

/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

theorem rep_add (Z : List (Lt r s)) (k l : ℕ) : rep Z (k + l) = rep Z k ++ rep Z l := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.add_right_comm, rep_succ, rep_succ, ih, List.append_assoc]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

theorem wprod_rep (Z : List (Lt r s)) (k : ℕ) : wprod (rep Z k) = wprod Z ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, wprod_append, ih, pow_succ']

theorem rep_getElem? (Z : List (Lt r s)) (k i : ℕ) (hi : i < k * Z.length) :
    (rep Z k)[i]? = Z[i % Z.length]? := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
    rw [rep_succ]
    by_cases h : i < Z.length
    · rw [List.getElem?_append_left h, Nat.mod_eq_of_lt h]
    · have h' : Z.length ≤ i := by omega
      rw [List.getElem?_append_right h', ih _ (by rw [Nat.succ_mul] at hi; omega),
        ← Nat.mod_eq_sub_mod h']

theorem rep_getElem (Z : List (Lt r s)) (k i : ℕ) (h : i < (rep Z k).length)
    (h' : i % Z.length < Z.length) : (rep Z k)[i] = Z[i % Z.length] := by
  have := rep_getElem? Z k i (by simpa using h)
  rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h'] at this
  exact Option.some.inj this

/-- `CycRed` gives that the square is reduced. -/
theorem red_sq_of_cycRed {u : List (Lt r s)} (hc : CycRed u) : Red (u ++ u) := by
  have e : u ++ u = rep u 2 := by simp [rep_succ]
  rw [e, Red, List.isChain_iff_getElem]
  intro i hi
  have hL : 0 < u.length := by
    rcases Nat.eq_zero_or_pos u.length with h0 | h0
    · simp [h0] at hi
    · exact h0
  have h1 := rep_getElem u 2 i (by omega) (Nat.mod_lt _ hL)
  have h2 := rep_getElem u 2 (i + 1) hi (Nat.mod_lt _ hL)
  rw [h1, h2]
  have := hc ⟨i % u.length, Nat.mod_lt _ hL⟩
  simp only [List.get_eq_getElem] at this
  convert this using 2
  simp [Nat.add_mod]

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r s : ℕ}
open scoped Classical
variable {r : ℕ}
/-! ## Words in `Lt 0 r` -/
theorem ibar_eq (w : List (Lt 0 r)) : ibar w = w.reverse := by
  unfold ibar
  congr 1
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun x _ => bar_eq x

/-- The block `R m_j R⁻¹ S m_i S⁻¹`. -/
def Bk (R : List (Lt 0 r)) (j : Fin r) (S : List (Lt 0 r)) (i : Fin r) : List (Lt 0 r) :=
  (R ++ [Sum.inr j] ++ R.reverse) ++ (S ++ [Sum.inr i] ++ S.reverse)

theorem length_Bk (R : List (Lt 0 r)) (j : Fin r) (S : List (Lt 0 r)) (i : Fin r) :
    (Bk R j S i).length = 2 * (R.length + S.length + 1) := by
  simp [Bk]; omega

theorem wprod_Bk (R : List (Lt 0 r)) (j : Fin r) (S : List (Lt 0 r)) (i : Fin r) :
    wprod (Bk R j S i) =
      wprod R * mI j * (wprod R)⁻¹ * (wprod S * mI i * (wprod S)⁻¹) := by
  unfold Bk
  rw [← ibar_eq R, ← ibar_eq S]
  simp only [wprod_append, wprod_ibar, wprod_singleton]
  rfl

/-! ### Letters through `getElem?` -/
theorem get?_eq (u : List (Lt 0 r)) (hne : u ≠ []) {n : ℕ} (hn : n < u.length) :
    u[n]? = some (Sum.inr (ac u hne n)) := by
  rw [List.getElem?_eq_getElem hn]
  congr 1
  have := ac_get u hne ⟨n, hn⟩
  simp only at this
  rw [← this]
  exact (inr_colr _).symm

theorem ac_of_get? (u : List (Lt 0 r)) (hne : u ≠ []) {n n' : ℕ} (hn : n < u.length)
    (hn' : n' < u.length) (h : u[n]? = u[n']?) : ac u hne n = ac u hne n' := by
  rw [get?_eq u hne hn, get?_eq u hne hn'] at h
  simpa using h

theorem get?_of_ac (u : List (Lt 0 r)) (hne : u ≠ []) {n n' : ℕ} (hn : n < u.length)
    (hn' : n' < u.length) (h : ac u hne n = ac u hne n') : u[n]? = u[n']? := by
  rw [get?_eq u hne hn, get?_eq u hne hn', h]

theorem ac_of_get?_inr (u : List (Lt 0 r)) (hne : u ≠ []) {n : ℕ} (hn : n < u.length)
    {k : Fin r} (h : u[n]? = some (Sum.inr k)) : ac u hne n = k := by
  rw [get?_eq u hne hn] at h
  simpa using h

theorem ac_mod (u : List (Lt 0 r)) (hne : u ≠ []) (τ : ℕ) :
    ac u hne τ = ac u hne (τ % u.length) :=
  per_mod (ac_per u hne) τ

/-! ### Labels in one period -/
theorem lb_val {p d n : ℕ} (hpd : p < d) (hn : n < 2 * d) :
    lb p d n = if n ≤ p then p - n else if n ≤ p + d then n - p else 2 * d + p - n := by
  unfold lb
  by_cases h : n ≤ p
  · rw [mm_lo hpd h]; split_ifs <;> omega
  · rw [mm_hi hpd (by omega) (by omega)]; split_ifs <;> omega

theorem lb_mod (p d n : ℕ) : lb p d (n % (2 * d)) = lb p d n := by
  have h : ∀ t, lb p d (t + 2 * d) = lb p d t := by
    intro t; unfold lb; rw [mm_per (dvd_refl _)]
  exact (per_mod h n).symm

theorem lb_eq_cases {p d n n' : ℕ} (hpd : p < d) (hn : n < 2 * d) (hn' : n' < 2 * d)
    (h : lb p d n = lb p d n') :
    n = n' ∨ n + n' = 2 * p ∨ (2 * p + 1 ≤ n ∧ 2 * p + 1 ≤ n' ∧ n + n' = 2 * d + 2 * p) := by
  rw [lb_val hpd hn, lb_val hpd hn'] at h
  split_ifs at h <;> omega

theorem lb_refl1 {p d m : ℕ} (hpd : p < d) (hm : m ≤ 2 * p) :
    lb p d (2 * p - m) = lb p d m := by
  rw [lb_val hpd (by omega), lb_val hpd (by omega)]
  split_ifs <;> omega

theorem lb_refl2 {p d q m : ℕ} (hd : d = p + q + 1) (hm : m ≤ 2 * q) :
    lb p d (2 * p + 1 + (2 * q - m)) = lb p d (2 * p + 1 + m) := by
  rw [lb_val (by omega) (by omega), lb_val (by omega) (by omega)]
  split_ifs <;> omega

/-! ### Palindromes -/
theorem pal_get? {β : Type*} {P : List β} (hP : P.reverse = P) {m : ℕ} (hm : m < P.length) :
    P[m]? = P[P.length - 1 - m]? := by
  have := List.getElem?_reverse (l := P) hm
  rwa [hP] at this

theorem pal_split {β : Type*} (w : List β) (n : ℕ) (x : β) (hl : w.length = 2 * n + 1)
    (hw : w.reverse = w) (hx : w[n]? = some x) :
    w = w.take n ++ [x] ++ (w.take n).reverse := by
  have hn : n < w.length := by omega
  have hx' : w[n] = x := by
    rw [List.getElem?_eq_getElem hn] at hx
    exact Option.some.inj hx
  have h1 : (w.take n).reverse = w.drop (n + 1) := by
    rw [List.reverse_take, hw]
    congr 1; omega
  conv_lhs => rw [← List.take_append_drop n w, List.drop_eq_getElem_cons hn, hx']
  rw [h1]
  simp

theorem pal_Bk1 (R : List (Lt 0 r)) (j : Fin r) :
    (R ++ [Sum.inr j] ++ R.reverse).reverse = R ++ [Sum.inr j] ++ R.reverse := by simp

/-! ### From a factorization to a fold -/
theorem qp_of_rep (R S : List (Lt 0 r)) (j i : Fin r) (t : ℕ) (ht : 1 ≤ t)
    (hne : rep (Bk R j S i) t ≠ []) :
    Qp (rep (Bk R j S i) t) hne R.length (R.length + S.length + 1) j i := by
  set p := R.length with hp
  set q := S.length with hq
  set d := p + q + 1 with hd
  set P1 := R ++ [Sum.inr j] ++ R.reverse with hP1
  set P2 := S ++ [Sum.inr i] ++ S.reverse with hP2
  have hB : Bk R j S i = P1 ++ P2 := rfl
  have hlB : (Bk R j S i).length = 2 * d := length_Bk R j S i
  have hl1 : P1.length = 2 * p + 1 := by simp [hP1]; omega
  have hl2 : P2.length = 2 * q + 1 := by simp [hP2]; omega
  have hL : (rep (Bk R j S i) t).length = t * (2 * d) := by rw [length_rep, hlB]
  have hL2 : 2 * d ≤ (rep (Bk R j S i) t).length := by
    rw [hL]; exact Nat.le_mul_of_pos_left _ ht
  have hdvd : 2 * d ∣ (rep (Bk R j S i) t).length := ⟨t, by rw [hL, Nat.mul_comm]⟩
  have hget : ∀ n, n < (rep (Bk R j S i) t).length →
      (rep (Bk R j S i) t)[n]? = (Bk R j S i)[n % (2 * d)]? := by
    intro n hn
    rw [rep_getElem? _ _ n (by rw [hlB, ← hL]; exact hn), hlB]
  have hB1 : ∀ n, n < 2 * p + 1 → (Bk R j S i)[n]? = P1[n]? := by
    intro n hn
    rw [hB, List.getElem?_append_left (by omega)]
  have hB2 : ∀ n, 2 * p + 1 ≤ n → (Bk R j S i)[n]? = P2[n - (2 * p + 1)]? := by
    intro n hn
    rw [hB, List.getElem?_append_right (by omega), hl1]
  have hpal1 : ∀ m, m < 2 * p + 1 → P1[m]? = P1[2 * p - m]? := by
    intro m hm
    have := pal_get? (pal_Bk1 R j) (m := m) (by rw [← hP1, hl1]; exact hm)
    rw [← hP1, hl1] at this
    rw [this]; congr 1
  have hpal2 : ∀ m, m < 2 * q + 1 → P2[m]? = P2[2 * q - m]? := by
    intro m hm
    have := pal_get? (pal_Bk1 S i) (m := m) (by rw [← hP2, hl2]; exact hm)
    rw [← hP2, hl2] at this
    rw [this]; congr 1
  have hmid1 : P1[p]? = some (Sum.inr j) := by simp [hP1, hp]
  have hmid2 : P2[q]? = some (Sum.inr i) := by simp [hP2, hq]
  have hBsym : ∀ n n', n < 2 * d → n' < 2 * d → lb p d n = lb p d n' →
      (Bk R j S i)[n]? = (Bk R j S i)[n']? := by
    intro n n' hn hn' h
    rcases lb_eq_cases (by omega) hn hn' h with rfl | h1 | ⟨h1, h2, h3⟩
    · rfl
    · rw [hB1 n (by omega), hB1 n' (by omega), hpal1 n (by omega)]
      congr 1; omega
    · rw [hB2 n h1, hB2 n' h2, hpal2 _ (by omega)]
      congr 1; omega
  refine ⟨by omega, hdvd, ?_, ?_, ?_⟩
  · intro τ τ' h
    rw [ac_mod _ hne τ, ac_mod _ hne τ']
    have hpos : 0 < (rep (Bk R j S i) t).length := by omega
    refine ac_of_get? _ hne (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) ?_
    rw [hget _ (Nat.mod_lt _ hpos), hget _ (Nat.mod_lt _ hpos), Nat.mod_mod_of_dvd _ hdvd,
      Nat.mod_mod_of_dvd _ hdvd]
    refine hBsym _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) ?_
    rw [lb_mod, lb_mod, h]
  · refine ac_of_get?_inr _ hne (by omega) ?_
    rw [hget _ (by omega), Nat.mod_eq_of_lt (by omega), hB1 _ (by omega), hmid1]
  · refine ac_of_get?_inr _ hne (by omega) ?_
    rw [hget _ (by omega), Nat.mod_eq_of_lt (by omega), hB2 _ (by omega),
      show p + d - (2 * p + 1) = q by omega, hmid2]

/-! ### From a fold to a factorization -/
theorem rep_of_qp (u : List (Lt 0 r)) (hne : u ≠ []) {p d : ℕ} {j i : Fin r}
    (hQ : Qp u hne p d j i) :
    u = rep (Bk (u.take p) j ((u.drop (2 * p + 1)).take (d - 1 - p)) i) (u.length / (2 * d)) := by
  obtain ⟨hpd, hdvd, hfac, hj, hi⟩ := hQ
  have hL := List.length_pos_iff.2 hne
  have hL2 : 2 * d ≤ u.length := Nat.le_of_dvd hL hdvd
  set q := d - 1 - p with hq
  have hsym : ∀ n n', n < u.length → n' < u.length → lb p d n = lb p d n' → u[n]? = u[n']? :=
    fun n n' hn hn' h => get?_of_ac u hne hn hn' (hfac n n' h)
  -- periodicity
  have hper : u = rep (u.take (2 * d)) (u.length / (2 * d)) := by
    have hlt : (u.take (2 * d)).length = 2 * d := by rw [List.length_take]; omega
    have hlr : (rep (u.take (2 * d)) (u.length / (2 * d))).length = u.length := by
      rw [length_rep, hlt, Nat.div_mul_cancel hdvd]
    apply List.ext_getElem?
    intro n
    by_cases hn : n < u.length
    · rw [rep_getElem? _ _ n (by rw [hlt, Nat.div_mul_cancel hdvd]; exact hn), hlt,
        List.getElem?_take_of_lt (Nat.mod_lt _ (by omega))]
      exact hsym _ _ hn (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hL2) (lb_mod p d n).symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  -- the two palindromes
  have hsplit : u.take (2 * d) = u.take (2 * p + 1) ++ (u.drop (2 * p + 1)).take (2 * q + 1) := by
    rw [show 2 * d = (2 * p + 1) + (2 * q + 1) by omega, List.take_add]
  have hl1 : (u.take (2 * p + 1)).length = 2 * p + 1 := by rw [List.length_take]; omega
  have hl2 : ((u.drop (2 * p + 1)).take (2 * q + 1)).length = 2 * q + 1 := by
    rw [List.length_take, List.length_drop]; omega
  have hg2 : ∀ k, k < 2 * q + 1 →
      ((u.drop (2 * p + 1)).take (2 * q + 1))[k]? = u[2 * p + 1 + k]? := by
    intro k hk
    rw [List.getElem?_take_of_lt hk, List.getElem?_drop]
  have hU1 : u.take (2 * p + 1) = u.take p ++ [Sum.inr j] ++ (u.take p).reverse := by
    have h := pal_split (u.take (2 * p + 1)) p (Sum.inr j) hl1 ?_ ?_
    · rw [List.take_take, show min p (2 * p + 1) = p by omega] at h
      exact h
    · apply List.ext_getElem?
      intro m
      by_cases hm : m < 2 * p + 1
      · rw [List.getElem?_reverse (by omega), hl1, List.getElem?_take_of_lt (by omega),
          List.getElem?_take_of_lt hm, show 2 * p + 1 - 1 - m = 2 * p - m by omega]
        exact hsym _ _ (by omega) (by omega) (lb_refl1 hpd (by omega))
      · rw [List.getElem?_eq_none (by rw [List.length_reverse]; omega),
          List.getElem?_eq_none (by omega)]
    · rw [List.getElem?_take_of_lt (by omega), get?_eq u hne (by omega), hj]
  have hU2 : (u.drop (2 * p + 1)).take (2 * q + 1) =
      (u.drop (2 * p + 1)).take q ++ [Sum.inr i] ++ ((u.drop (2 * p + 1)).take q).reverse := by
    have h := pal_split ((u.drop (2 * p + 1)).take (2 * q + 1)) q (Sum.inr i) hl2 ?_ ?_
    · rw [List.take_take, show min q (2 * q + 1) = q by omega] at h
      exact h
    · apply List.ext_getElem?
      intro m
      by_cases hm : m < 2 * q + 1
      · rw [List.getElem?_reverse (by omega), hl2, hg2 _ (by omega), hg2 _ hm,
          show 2 * q + 1 - 1 - m = 2 * q - m by omega]
        exact hsym _ _ (by omega) (by omega) (lb_refl2 (by omega) (by omega))
      · rw [List.getElem?_eq_none (by rw [List.length_reverse]; omega),
          List.getElem?_eq_none (by omega)]
    · rw [hg2 _ (by omega), get?_eq u hne (by omega), show 2 * p + 1 + q = p + d by omega, hi]
  have hBk : Bk (u.take p) j ((u.drop (2 * p + 1)).take q) i = u.take (2 * d) := by
    unfold Bk
    rw [hsplit, ← hU1, ← hU2]
  rw [hBk]
  exact hper

/-! ### Peeling a conjugation -/
theorem peel {β : Type*} {U U' : List β} (hU : ∀ x C, U ≠ x :: (C ++ [x]))
    (hU' : ∀ x C, U' ≠ x :: (C ++ [x])) :
    ∀ A A' : List β, A ++ U ++ A.reverse = A' ++ U' ++ A'.reverse → A = A' ∧ U = U' := by
  intro A
  induction A with
  | nil =>
    intro A' h
    cases A' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons y A' =>
      exfalso
      refine hU y (A' ++ U' ++ A'.reverse) ?_
      simpa using h
  | cons x A ih =>
    intro A' h
    cases A' with
    | nil =>
      exfalso
      refine hU' x (A ++ U ++ A.reverse) ?_
      simpa using h.symm
    | cons y A' =>
      have h' : x :: ((A ++ U ++ A.reverse) ++ [x]) = y :: ((A' ++ U' ++ A'.reverse) ++ [y]) := by
        simpa using h
      injection h' with h1 h2
      subst h1
      obtain ⟨e1, e2⟩ := ih A' (List.append_cancel_right h2)
      exact ⟨by rw [e1], e2⟩

theorem no_wrap_of_cycRed (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u) :
    ∀ x C, u ≠ x :: (C ++ [x]) := by
  intro x C h
  have hL := List.length_pos_iff.2 hne
  have h0 : u[0]? = some x := by rw [h]; rfl
  have h1 : u[u.length - 1]? = some x := by rw [h]; simp
  have e : ac u hne 0 = ac u hne (u.length - 1) := ac_of_get? u hne hL (by omega) (h0.trans h1.symm)
  have := ac_cr u hne hcr (u.length - 1)
  rw [show u.length - 1 + 1 = 0 + u.length by omega, ac_per] at this
  exact this e

theorem no_wrap_of_red (R S : List (Lt 0 r)) (j i : Fin r) (t : ℕ) (ht : 1 ≤ t)
    (hred : Red (rep (Bk R j S i) t)) : ∀ x C, rep (Bk R j S i) t ≠ x :: (C ++ [x]) := by
  intro x C h
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  set P1 := R ++ [Sum.inr j] ++ R.reverse with hP1
  set P2 := S ++ [Sum.inr i] ++ S.reverse with hP2
  have hB : Bk R j S i = P1 ++ P2 := rfl
  have hne1 : P1 ≠ [] := by simp [hP1]
  have hne2 : P2 ≠ [] := by simp [hP2]
  have hBne : Bk R j S i ≠ [] := by rw [hB]; simp [hne1]
  -- head and last of the power
  have hhead : (rep (Bk R j S i) (t + 1)).head? = P1.head? := by
    rw [rep_succ, List.head?_append_of_ne_nil _ hBne, hB, List.head?_append_of_ne_nil _ hne1]
  have hlast : (rep (Bk R j S i) (t + 1)).getLast? = P2.getLast? := by
    rw [rep_add, show rep (Bk R j S i) 1 = Bk R j S i by simp [rep_succ],
      List.getLast?_append_of_ne_nil _ hBne, hB, List.getLast?_append_of_ne_nil _ hne2]
  have hx1 : P1.head? = some x := by rw [← hhead, h]; rfl
  have hx2 : P2.getLast? = some x := by
    rw [← hlast, h, ← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]
    rfl
  have hl1 : P1.getLast? = some x := by
    rw [← List.head?_reverse, hP1, pal_Bk1, ← hP1]; exact hx1
  have hh2 : P2.head? = some x := by
    rw [← List.getLast?_reverse, hP2, pal_Bk1, ← hP2]; exact hx2
  have hredB : Red (P1 ++ P2) := by
    rw [rep_succ, hB] at hred
    exact red_left hred
  rw [Red, List.isChain_append] at hredB
  have := hredB.2.2 x (by rw [hl1]; rfl) x (by rw [hh2]; rfl)
  exact this (bar_eq x).symm

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r s : ℕ}
open scoped Classical
variable {r : ℕ}
variable (a : G 0 r) (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
  (hlen : len (a * wprod u * a⁻¹) = 2 * len a + u.length)
/-! ### The tuples of `C2count` -/
include hlen in
theorem nf_conj : nf (a * wprod u * a⁻¹) = nf a ++ u ++ (nf a).reverse := by
  rw [← ibar_eq]
  apply eq_nf_of_length
  · rw [wprod_append, wprod_append, wprod_ibar, wprod_nf]
  · rw [hlen, len_eq_length_nf a]
    simp
    omega

include hne hcr hlen in
/-- A tuple counted by `C2count` has `a' = a` and gives a factorization of `u`. -/
theorem tuple_spec (i j : Fin r) (a' ρ σ : G 0 r) (t : ℕ) (ht : 1 ≤ t)
    (hg : a * wprod u * a⁻¹ = a' * (ρ * mI j * ρ⁻¹ * (σ * mI i * σ⁻¹)) ^ t * a'⁻¹)
    (hl : len (a * wprod u * a⁻¹) = 2 * len a' + t * (2 * len ρ + 2 * len σ + 2)) :
    a' = a ∧ u = rep (Bk (nf ρ) j (nf σ) i) t := by
  have h1 := nf_conj a u hlen
  have h2 : nf (a * wprod u * a⁻¹) =
      nf a' ++ rep (Bk (nf ρ) j (nf σ) i) t ++ (nf a').reverse := by
    rw [← ibar_eq]
    apply eq_nf_of_length
    · rw [wprod_append, wprod_append, wprod_ibar, wprod_nf, wprod_rep, wprod_Bk, wprod_nf,
        wprod_nf, hg]
    · rw [hl, len_eq_length_nf a', len_eq_length_nf ρ, len_eq_length_nf σ]
      simp [length_Bk]
      ring
  have hred : Red (rep (Bk (nf ρ) j (nf σ) i) t) := by
    have := red_nf (a * wprod u * a⁻¹)
    rw [h2] at this
    exact red_right (red_left this)
  have hp := peel (no_wrap_of_cycRed u hne hcr) (no_wrap_of_red _ _ j i t ht hred)
    (nf a) (nf a') (h1.symm.trans h2)
  exact ⟨nf_injective hp.1.symm, hp.2⟩

theorem take_rep_Bk (R S : List (Lt 0 r)) (j i : Fin r) (t : ℕ) (ht : 1 ≤ t) :
    (rep (Bk R j S i) t).take R.length = R ∧
      ((rep (Bk R j S i) t).drop (2 * R.length + 1)).take S.length = S := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [rep_succ]
  constructor
  · have : Bk R j S i ++ rep (Bk R j S i) t =
        R ++ ([Sum.inr j] ++ R.reverse ++ (S ++ [Sum.inr i] ++ S.reverse) ++ rep (Bk R j S i) t) := by
      simp [Bk]
    rw [this, List.take_left]
  · have : Bk R j S i ++ rep (Bk R j S i) t =
        (R ++ [Sum.inr j] ++ R.reverse) ++
          (S ++ ([Sum.inr i] ++ S.reverse ++ rep (Bk R j S i) t)) := by
      simp [Bk]
    rw [this, List.drop_left' (by simp; omega), List.take_left]

include hne hcr hlen in
theorem c2count_eq (i j : Fin r) :
    C2count i j (a * wprod u * a⁻¹) = (Par u hne j i).card := by
  have hL := List.length_pos_iff.2 hne
  unfold C2count
  rw [← Fintype.card_coe (Par u hne j i), ← Nat.card_eq_fintype_card]
  have hmem : ∀ p : {p : G 0 r × G 0 r × G 0 r × ℕ // 1 ≤ p.2.2.2 ∧
      a * wprod u * a⁻¹ =
        p.1 * (p.2.1 * mI j * p.2.1⁻¹ * (p.2.2.1 * mI i * p.2.2.1⁻¹)) ^ p.2.2.2 * p.1⁻¹ ∧
      len (a * wprod u * a⁻¹) =
        2 * len p.1 + p.2.2.2 * (2 * len p.2.1 + 2 * len p.2.2.1 + 2)},
      (len p.1.2.1, len p.1.2.1 + len p.1.2.2.1 + 1) ∈ Par u hne j i := by
    rintro ⟨⟨a', ρ, σ, t⟩, ht, hg, hl⟩
    obtain ⟨-, hu⟩ := tuple_spec a u hne hcr hlen i j a' ρ σ t ht hg hl
    have hQ : Qp u hne (len ρ) (len ρ + len σ + 1) j i := by
      have hne' : rep (Bk (nf ρ) j (nf σ) i) t ≠ [] := hu ▸ hne
      have := qp_of_rep (nf ρ) (nf σ) j i t ht hne'
      rw [len_eq_length_nf ρ, len_eq_length_nf σ]
      revert this
      generalize hne' = hne''
      revert hne''
      rw [← hu]
      intro hne'' h
      exact h
    simp only [Par, mem_filter, mem_product, mem_range]
    have h2 : 2 * (len ρ + len σ + 1) ≤ u.length := Nat.le_of_dvd hL hQ.2.1
    exact ⟨⟨by omega, by omega⟩, hQ⟩
  refine Nat.card_eq_of_bijective (fun p => ⟨_, hmem p⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨a1, ρ1, σ1, t1⟩, ht1, hg1, hl1⟩ ⟨⟨a2, ρ2, σ2, t2⟩, ht2, hg2, hl2⟩ heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq ⊢
    obtain ⟨e1, e2⟩ := heq
    have e3 : len σ1 = len σ2 := by omega
    obtain ⟨ha1, hu1⟩ := tuple_spec a u hne hcr hlen i j a1 ρ1 σ1 t1 ht1 hg1 hl1
    obtain ⟨ha2, hu2⟩ := tuple_spec a u hne hcr hlen i j a2 ρ2 σ2 t2 ht2 hg2 hl2
    obtain ⟨r1, s1⟩ := take_rep_Bk (nf ρ1) (nf σ1) j i t1 ht1
    obtain ⟨r2, s2⟩ := take_rep_Bk (nf ρ2) (nf σ2) j i t2 ht2
    rw [← hu1] at r1 s1
    rw [← hu2] at r2 s2
    have hρ : nf ρ1 = nf ρ2 := by
      rw [← r1, ← r2, ← len_eq_length_nf, ← len_eq_length_nf, e1]
    have hσ : nf σ1 = nf σ2 := by
      rw [← s1, ← s2, ← len_eq_length_nf, ← len_eq_length_nf, ← len_eq_length_nf,
        ← len_eq_length_nf, e1, e3]
    have ht : t1 = t2 := by
      have l1 := congrArg List.length hu1
      have l2 := congrArg List.length hu2
      rw [length_rep, length_Bk, ← len_eq_length_nf, ← len_eq_length_nf] at l1 l2
      rw [l1, e1, e3] at l2
      exact Nat.eq_of_mul_eq_mul_right (by omega) l2
    exact ⟨ha1.trans ha2.symm, nf_injective hρ, nf_injective hσ, ht⟩
  · rintro ⟨⟨p, d⟩, hpd⟩
    have hQ : Qp u hne p d j i := (mem_filter.1 hpd).2
    have hu := rep_of_qp u hne hQ
    obtain ⟨hpd', hdvd, -, -, -⟩ := hQ
    set R := u.take p with hR
    set S := (u.drop (2 * p + 1)).take (d - 1 - p) with hS
    set t := u.length / (2 * d) with ht
    have hL2 : 2 * d ≤ u.length := Nat.le_of_dvd hL hdvd
    have hlR : R.length = p := by rw [hR, List.length_take]; omega
    have hlS : S.length = d - 1 - p := by rw [hS, List.length_take, List.length_drop]; omega
    have hredu : Red u := red_left (red_sq_of_cycRed hcr)
    have hredR : Red R := by
      have := hredu
      rw [← List.take_append_drop p u] at this
      exact red_left this
    have hredS : Red S := by
      have := hredu
      rw [← List.take_append_drop (2 * p + 1) u] at this
      have := red_right this
      rw [← List.take_append_drop (d - 1 - p) (u.drop (2 * p + 1))] at this
      exact red_left this
    have ht1 : 1 ≤ t := (Nat.one_le_div_iff (by omega)).2 hL2
    have hw : wprod u =
        (wprod R * mI j * (wprod R)⁻¹ * (wprod S * mI i * (wprod S)⁻¹)) ^ t := by
      conv_lhs => rw [hu]
      rw [wprod_rep, wprod_Bk]
    refine ⟨⟨(a, wprod R, wprod S, t), ht1, ?_, ?_⟩, ?_⟩
    · show a * wprod u * a⁻¹ = a * _ ^ t * a⁻¹
      rw [← hw]
    · show len (a * wprod u * a⁻¹) = 2 * len a + t * (2 * len (wprod R) + 2 * len (wprod S) + 2)
      rw [hlen, len_wprod_of_red hredR, len_wprod_of_red hredS, hlR, hlS]
      have : u.length = t * (2 * d) := (Nat.div_mul_cancel hdvd).symm
      rw [this, show 2 * p + 2 * (d - 1 - p) + 2 = 2 * d by omega]
    · apply Subtype.ext
      show (len (wprod R), len (wprod R) + len (wprod S) + 1) = (p, d)
      rw [len_wprod_of_red hredR, len_wprod_of_red hredS, hlR, hlS]
      congr 1; omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- Second-order colourings with two loops are the tree-path shapes counted by `C2count`. -/
theorem card_second_order (a : G 0 r) (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (hlen : len (a * wprod u * a⁻¹) = 2 * len a + u.length) (i j : Fin r) :
    ((CGL u).filter fun c => nv c + 1 = Ecount u c + Fcount u c ∧
        ∀ k, fK u c k = (if k = i then 1 else 0) + (if k = j then 1 else 0)).card =
      if i = j then C2count i i (a * wprod u * a⁻¹)
      else C2count i j (a * wprod u * a⁻¹) + C2count j i (a * wprod u * a⁻¹) := by
  rw [card_second_eq u hne hcr i j]
  split_ifs with hij
  · subst hij
    rw [union_self, c2count_eq a u hne hcr hlen i i]
  · rw [c2count_eq a u hne hcr hlen i j, c2count_eq a u hne hcr hlen j i]
    apply card_union_of_disjoint
    rw [disjoint_left]
    rintro ⟨p, d⟩ h1 h2
    have q1 : Qp u hne p d j i := (mem_filter.1 h1).2
    have q2 : Qp u hne p d i j := (mem_filter.1 h2).2
    exact hij (q2.2.2.2.1.symm.trans q1.2.2.2.1)

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias card_second_order := RandomInvolutions.Dev.PartW.card_second_order

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
lemma T_sum (a : G 0 r) (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (hlen : len (a * wprod u * a⁻¹) = 2 * len a + u.length) :
    ∃ (c0 : ℝ) (c1 : Fin r → ℝ), ∀ κ : Fin r → ℕ,
      ∑ c ∈ CGL u, Tc u κ c = c0 + ∑ i, (κ i : ℝ) * c1 i +
        ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j (a * wprod u * a⁻¹) := by
  have hcard : ∀ i j, (((CGL u).filter fun c => PcC u c i j).card : ℝ) =
      if i = j then (C2count i i (a * wprod u * a⁻¹) : ℝ)
      else C2count i j (a * wprod u * a⁻¹) + C2count j i (a * wprod u * a⁻¹) := by
    intro i j
    have hnat : ((CGL u).filter fun c => PcC u c i j).card =
        if i = j then C2count i i (a * wprod u * a⁻¹)
        else C2count i j (a * wprod u * a⁻¹) + C2count j i (a * wprod u * a⁻¹) := by
      rw [← card_second_order a u hne hcr hlen i j]
      congr 1
      ext c
      exact ⟨fun h => mem_filter.2 (mem_filter.1 h), fun h => mem_filter.2 (mem_filter.1 h)⟩
    rw [hnat]
    split_ifs <;> push_cast <;> rfl
  refine ⟨∑ c ∈ CGL u, alphaC u c,
    fun i => ∑ c ∈ CGL u, betaC u c i - C2count i i (a * wprod u * a⁻¹), fun κ => ?_⟩
  rw [sum_congr rfl (Tc_eq u κ), sum_add_distrib, sum_add_distrib]
  have e1 : ∑ c ∈ CGL u, ∑ i, (κ i : ℝ) * betaC u c i =
      ∑ i, (κ i : ℝ) * ∑ c ∈ CGL u, betaC u c i := by
    rw [sum_comm]
    simp only [mul_sum]
  have e2 : ∑ c ∈ CGL u, ∑ i, ∑ j, (if PcC u c i j then wq κ i j else 0) =
      ∑ i, ∑ j, wq κ i j * (if i = j then (C2count i i (a * wprod u * a⁻¹) : ℝ)
        else C2count i j (a * wprod u * a⁻¹) + C2count j i (a * wprod u * a⁻¹)) := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← hcard i j, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have t : ∀ i j, wq κ i j * (if i = j then (C2count i i (a * wprod u * a⁻¹) : ℝ)
        else C2count i j (a * wprod u * a⁻¹) + C2count j i (a * wprod u * a⁻¹)) =
      (κ i : ℝ) * κ j / 2 * C2count i j (a * wprod u * a⁻¹) +
        (κ j : ℝ) * κ i / 2 * C2count j i (a * wprod u * a⁻¹) -
        (if i = j then (κ i : ℝ) * C2count i i (a * wprod u * a⁻¹) else 0) := by
    intro i j
    unfold wq
    by_cases h : i = j
    · subst h
      simp only [if_true]
      ring
    · simp only [if_neg h]
      ring
  have hx : ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j (a * wprod u * a⁻¹) =
      ∑ i, ∑ j, (κ i : ℝ) * κ j / 2 * C2count i j (a * wprod u * a⁻¹) +
        ∑ i, ∑ j, (κ i : ℝ) * κ j / 2 * C2count i j (a * wprod u * a⁻¹) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have e3 : ∑ i, ∑ j, wq κ i j * (if i = j then (C2count i i (a * wprod u * a⁻¹) : ℝ)
        else C2count i j (a * wprod u * a⁻¹) + C2count j i (a * wprod u * a⁻¹)) =
      ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j (a * wprod u * a⁻¹) -
        ∑ i, (κ i : ℝ) * C2count i i (a * wprod u * a⁻¹) := by
    simp only [t, sum_sub_distrib, sum_add_distrib]
    rw [sum_comm (f := fun i j => (κ j : ℝ) * κ i / 2 * C2count j i (a * wprod u * a⁻¹)), hx]
    simp only [sum_ite_eq, mem_univ, if_true]
  rw [e1, e2, e3]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-! ## `tendsto_mul_expFixK_sub_first_order` -/
lemma expand_g (g : G 0 r) (hg : g ≠ 1) :
    ∃ (c0 : ℝ) (c1 : Fin r → ℝ), ∀ κ : Fin r → ℕ,
      Tendsto (fun N : ℕ => (N : ℝ) * (expFixK r N κ g -
          ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) (admF κ)
        (𝓝 (c0 + ∑ i, (κ i : ℝ) * c1 i +
          ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)) := by
  obtain ⟨a, u, hne, rfl, hlen, hcase⟩ := exists_cyc_rep g hg
  rcases hcase with hc | ⟨i, rfl⟩
  · obtain ⟨c0, c1, hT⟩ := T_sum a u hne hc hlen
    refine ⟨c0, c1, fun κ => ?_⟩
    rw [← hT κ]
    have h1 := (sum_tendsto u hne hc κ).mono_left (inf_le_left : admF κ ≤ atTop)
    refine h1.congr' ?_
    have hbig : ∀ᶠ N in admF κ, max 1 u.length ≤ N :=
      (eventually_ge_atTop (max 1 u.length)).filter_mono inf_le_left
    have hadm : ∀ᶠ N in admF κ, AdmK N κ :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [hbig, hadm] with N hN hA
    rw [expFixK_conj, expect_formulaK u N κ (le_of_max_le_left hN) hA (le_of_max_le_right hN),
      S0_card a u hne hc hg]
    have hB : ∀ i, Bcount i (a * wprod u * a⁻¹) = 0 := fun i => bcount_cyc a u hne hc hlen i
    simp [hB]
  · refine ⟨0, fun _ => 0, fun κ => ?_⟩
    rw [wprod_single]
    have h2 : ∀ k j, C2count k j (a * mI i * a⁻¹) = 0 := fun k j => c2count_torsion a i k j
    have hB : ∀ k, Bcount k (a * mI i * a⁻¹) = if k = i then 1 else 0 :=
      fun k => bcount_torsion a i k
    have hlim : (0 : ℝ) + ∑ k, (κ k : ℝ) * (fun _ => (0 : ℝ)) k +
        ∑ k, ∑ j, (κ k : ℝ) * κ j * C2count k j (a * mI i * a⁻¹) = 0 := by
      simp [h2]
    rw [hlim]
    refine tendsto_const_nhds.congr' ?_
    have hadm : ∀ᶠ N in admF κ, AdmK N κ :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [hadm] with N hA
    rw [expFixK_torsion hA, cfun_torsion a i]
    simp [hB]

/-- `E_{N,κ}[fix g] = cfun g + 1 + ∑ κᵢ Bᵢ(g) + (C₀(g) + ∑ κᵢ C₁ᵢ(g) + ∑ κᵢ κⱼ C₂ᵢⱼ(g))/N +
o(1/N)` along admissible `N`, for `g ≠ 1`. -/
theorem tendsto_mul_expFixK_sub_first_order (r : ℕ) : ∃ (C0 : G 0 r → ℝ) (C1 : Fin r → G 0 r → ℝ),
    ∀ g : G 0 r, g ≠ 1 → ∀ κ : Fin r → ℕ,
      Tendsto (fun N : ℕ => (N : ℝ) * (expFixK r N κ g -
          ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) (admF κ)
        (𝓝 (C0 g + ∑ i, (κ i : ℝ) * C1 i g +
          ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)) := by
  have key : ∀ g : G 0 r, ∃ (c0 : ℝ) (c1 : Fin r → ℝ), g ≠ 1 → ∀ κ : Fin r → ℕ,
      Tendsto (fun N : ℕ => (N : ℝ) * (expFixK r N κ g -
          ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) (admF κ)
        (𝓝 (c0 + ∑ i, (κ i : ℝ) * c1 i +
          ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨0, fun _ => 0, fun h => absurd hg h⟩
    · obtain ⟨c0, c1, h⟩ := expand_g g hg
      exact ⟨c0, c1, fun _ => h⟩
  choose C0 C1 h using key
  exact ⟨C0, fun i g => C1 g i, fun g hg κ => h g hg κ⟩

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias tendsto_mul_expFixK_sub_first_order := RandomInvolutions.Dev.PartK2.tendsto_mul_expFixK_sub_first_order

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
open RandomInvolutions
open RandomInvolutions.Dev
theorem solution (r : ℕ) : ∃ (C0 : G 0 r → ℝ) (C1 : Fin r → G 0 r → ℝ),
    ∀ g : G 0 r, g ≠ 1 → ∀ κ : Fin r → ℕ,
      Tendsto (fun N : ℕ => (N : ℝ) * (expFixK r N κ g -
          ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) (admF κ)
        (𝓝 (C0 g + ∑ i, (κ i : ℝ) * C1 i g +
          ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)) := by
  exact RandomInvolutions.Dev.tendsto_mul_expFixK_sub_first_order r
end
end
