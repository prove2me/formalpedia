-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.fderiv_phiM_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:56.448962+00:00
-- url     : https://prove2.me/submissions/83d32f82-d13a-49aa-abdb-492897866e38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem contDiff_lead_casimir_coefficients (j : ℕ) :
    ContDiff ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ => lead j w) := by
  by_cases h : j ≤ n
  · have e : (fun w : Matrix (Fin n) (Fin n) ℂ => lead j w) =
        fun w => (w.submatrix (Fin.castLE h) (Fin.castLE h)).det := funext fun w => dif_pos h
    rw [e]
    simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    refine contDiff_prod fun p _ => ?_
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_id (𝕜 := ℂ) (E := Matrix (Fin n) (Fin n) ℂ))
      (Fin.castLE h (σ p))) (Fin.castLE h p)
  · have e : (fun w : Matrix (Fin n) (Fin n) ℂ => lead j w) = fun _ => 0 := funext fun w => dif_neg h
    rw [e]
    exact contDiff_const
private theorem differentiableAt_PhiM_of_mem_OmegaSet (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0 := hz
  have key : ∀ i : Fin n, ContDiffAt ℂ 1
      (fun w : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) w ^ (-(μ i - muNext μ i))) z := by
    intro i
    have hd : ContDiffAt ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) w) z :=
      (contDiff_lead_casimir_coefficients ((i : ℕ) + 1)).contDiffAt
    have key' : ∀ k : ℤ,
        ContDiffAt ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) w ^ k) z := by
      intro k
      cases k with
      | ofNat p => simpa using hd.pow p
      | negSucc p =>
        simp only [zpow_negSucc]
        exact (hd.pow (p + 1)).inv (pow_ne_zero _ (hz' i))
    exact key' _
  have hc : ContDiffAt ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ =>
      ∏ i : Fin n, lead ((i : ℕ) + 1) w ^ (-(μ i - muNext μ i))) z :=
    contDiffAt_prod fun i _ => key i
  exact hc.differentiableAt one_ne_zero
private theorem fderiv_PhiM_of_lead_curve (μ : Fin n → ℤ) {z V : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    (D : ℕ → ℂ) (hlead : ∀ (t : ℂ) (i : Fin n), lead ((i : ℕ) + 1) (z + t • V) =
      (∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * D a)) * lead ((i : ℕ) + 1) z) :
    fderiv ℂ (PhiM μ) z V = -(∑ a ∈ Finset.range n,
      (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) * D a) * PhiM μ z := by
  set m : ℕ → ℂ := fun k => if h : k < n then (μ ⟨k, h⟩ : ℂ) else 0 with hm
  have hc : HasDerivAt (fun t : ℂ => z + t • V) V 0 := by
    exact (((hasDerivAt_id (0 : ℂ)).smul_const V).const_add z).congr_deriv (one_smul ℂ V)
  have hΦ : HasFDerivAt (PhiM μ) (fderiv ℂ (PhiM μ) z) (z + (0 : ℂ) • V) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_PhiM_of_mem_OmegaSet μ hz).hasFDerivAt
  have h1 := hΦ.comp_hasDerivAt (0 : ℂ) hc
  set p : Fin n → ℂ → ℂ := fun i t => ∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * D a) with hp
  have hfun : (PhiM μ ∘ fun t : ℂ => z + t • V) =
      fun t => (∏ i : Fin n, p i t ^ (-(μ i - muNext μ i))) * PhiM μ z := by
    funext t
    simp only [Function.comp_apply, PhiM, hlead, mul_zpow, Finset.prod_mul_distrib, hp]
  have hpd : ∀ i : Fin n, HasDerivAt (p i) (∑ a ∈ Finset.range ((i : ℕ) + 1), D a) 0 := by
    intro i
    have h := HasDerivAt.finset_prod (u := Finset.range ((i : ℕ) + 1)) (x := (0 : ℂ))
      (f := fun a t => 1 + t * D a) (f' := fun a => D a)
      (fun a _ => by simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (D a)).const_add 1)
    refine (h.congr_deriv (by simp [Finset.prod_apply])).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [hp, Finset.prod_apply]
  have hp0 : ∀ i : Fin n, p i 0 = 1 := fun i => by simp [hp]
  have hfd : ∀ i : Fin n, HasDerivAt (fun t => p i t ^ (-(μ i - muNext μ i)))
      ((((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a) 0 := by
    intro i
    have h := (hasDerivAt_zpow (-(μ i - muNext μ i)) (p i 0)
      (Or.inl (by rw [hp0]; exact one_ne_zero))).comp (0 : ℂ) (hpd i)
    exact h.congr_deriv (by rw [hp0]; simp)
  have h2 : HasDerivAt (fun t => (∏ i : Fin n, p i t ^ (-(μ i - muNext μ i))) * PhiM μ z)
      ((∑ i : Fin n, (((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a) *
        PhiM μ z) 0 := by
    have h := (HasDerivAt.finset_prod (u := Finset.univ) (fun i _ => hfd i)).mul_const (PhiM μ z)
    refine (h.congr_deriv (by simp [hp0, Finset.prod_apply])).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have htel : ∀ N : ℕ, ∑ k ∈ Finset.range N, (m (k + 1) - m k) * ∑ a ∈ Finset.range (k + 1), D a =
      m N * ∑ a ∈ Finset.range N, D a - ∑ a ∈ Finset.range N, m a * D a := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ (fun k => (m (k + 1) - m k) * ∑ a ∈ Finset.range (k + 1), D a), ih,
        Finset.sum_range_succ (fun a => m a * D a), Finset.sum_range_succ D]
      ring
  have hmn : m n = 0 := by simp [hm]
  have hm0 : ∀ i : Fin n, m i = (μ i : ℂ) := fun i => by simp [hm, i.2]
  have hmN : ∀ i : Fin n, ((muNext μ i : ℤ) : ℂ) = m ((i : ℕ) + 1) := fun i => by
    simp only [muNext, hm]
    split_ifs <;> simp
  have hterm : ∀ i : Fin n, (((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a =
      (m ((i : ℕ) + 1) - m i) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a := fun i => by
    rw [hm0 i, ← hmN i]
    push_cast
    ring
  have hsumeq : ∑ i : Fin n, (((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a =
      -∑ a ∈ Finset.range n, m a * D a := by
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range (fun k => (m (k + 1) - m k) * ∑ a ∈ Finset.range (k + 1), D a) n,
      htel n, hmn]
    ring
  rw [hfun] at h1
  have hu := h1.unique h2
  rw [hsumeq] at hu
  exact hu
private theorem lead_add_smul_mul_of_isUpperTri {X z : Matrix (Fin n) (Fin n) ℂ} (hX : IsUpperTri X) (t : ℂ)
    (i : Fin n) : lead ((i : ℕ) + 1) (z + t • (z * X)) =
      (∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0))) *
        lead ((i : ℕ) + 1) z := by
  have hi : (i : ℕ) + 1 ≤ n := i.2
  set e : Fin ((i : ℕ) + 1) → Fin n := Fin.castLE hi with he
  set A : Matrix (Fin n) (Fin n) ℂ := 1 + t • X with hA
  have hAz : z + t • (z * X) = z * A := by
    rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hzero : ∀ a c : Fin n, c < a → A a c = 0 := fun a c hca => by
    rw [hA, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hca).symm, Matrix.smul_apply, hX _ _ hca,
      smul_zero, zero_add]
  have hsub : (z * A).submatrix e e = z.submatrix e e * A.submatrix e e := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective hi) _ _ ?_ (fun r => rfl)
    intro c hc
    have hc' : (i : ℕ) + 1 ≤ c := by
      by_contra hlt
      push_neg at hlt
      exact hc ⟨⟨c, hlt⟩, Fin.ext rfl⟩
    have hlt : e q < c := by
      show (q : ℕ) < c
      exact lt_of_lt_of_le q.2 hc'
    show z (e p) c * A c (e q) = 0
    rw [hzero _ _ hlt, mul_zero]
  have htri : (A.submatrix e e).BlockTriangular id := by
    intro p q hpq
    have hlt : e q < e p := by
      show (q : ℕ) < p
      exact hpq
    exact hzero _ _ hlt
  simp only [lead, dif_pos hi]
  rw [hAz, hsub, Matrix.det_mul, Matrix.det_of_upperTriangular htri, mul_comm]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun a => 1 + t * (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : (p : ℕ) < n := lt_of_lt_of_le p.2 hi
  have hep : (⟨(p : ℕ), hp⟩ : Fin n) = e p := Fin.ext rfl
  simp only [dif_pos hp, hep, Matrix.submatrix_apply, hA, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) {z X : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    (hX : IsUpperTri X) :
    fderiv ℂ (PhiM μ) z (z * X) = -(∑ a, (μ a : ℂ) * X a a) * PhiM μ z := by
  have hs : ∑ a ∈ Finset.range n, (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) *
      (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0) = ∑ a, (μ a : ℂ) * X a a := by
    rw [← Fin.sum_univ_eq_sum_range (fun a => (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) *
      (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0)) n]
    simp
  rw [fderiv_PhiM_of_lead_curve μ hz _ (fun t i => lead_add_smul_mul_of_isUpperTri hX t i), hs]
end ReciprocityTheory.ChartRestriction.DS.S7
