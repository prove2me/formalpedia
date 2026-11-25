-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:02.481891+00:00
-- url     : https://prove2.me/submissions/087a112e-cf00-4883-8b0d-bb79c50d392e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_simdiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
theorem _root_.solution (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    ∃ (L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) (b : Fin (Module.finrank ℝ E) → ℂ),
      (∀ i, 0 < (b i).re) ∧ ∀ w, B (L w) (L w) = ∑ i, b i * (w i : ℂ) ^ 2 := by
  let e := Module.finBasis ℝ E
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2
  let C : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2
  have hexp : ∀ x : Fin (Module.finrank ℝ E) → ℝ, B (e.equivFun.symm x) (e.equivFun.symm x) =
      ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (e i) (e j) := by
    intro x
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, Complex.real_smul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hsymm : ∀ (x : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      ∑ i, x i * ∑ j, ((f i j + f j i) / 2) * x j = ∑ i, ∑ j, x i * x j * f i j := by
    intro x f
    have h1 : ∑ i, ∑ j, x i * x j * f j i = ∑ i, ∑ j, x i * x j * f i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, x i * ∑ j, ((f i j + f j i) / 2) * x j =
        (∑ i, ∑ j, x i * x j * f i j + ∑ i, ∑ j, x i * x j * f j i) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, h1]
    ring
  have hre : ∀ x, (B (e.equivFun.symm x) (e.equivFun.symm x)).re = x ⬝ᵥ (A *ᵥ x) := by
    intro x
    show _ = ∑ i, x i * ∑ j, ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2 * x j
    rw [hsymm x (fun i j => (B (e i) (e j)).re), hexp]
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have him : ∀ x, (B (e.equivFun.symm x) (e.equivFun.symm x)).im = x ⬝ᵥ (C *ᵥ x) := by
    intro x
    show _ = ∑ i, x i * ∑ j, ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2 * x j
    rw [hsymm x (fun i j => (B (e i) (e j)).im), hexp]
    simp only [Complex.im_sum, Complex.im_ofReal_mul]
  have hAh : A.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star (((B (e j) (e i)).re + (B (e i) (e j)).re) / 2) =
      ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2
    rw [star_trivial, add_comm]
  have hCh : C.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star (((B (e j) (e i)).im + (B (e i) (e j)).im) / 2) =
      ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2
    rw [star_trivial, add_comm]
  have hApd : A.PosDef := by
    refine ⟨hAh, fun x hx => ?_⟩
    have key : (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj) = (⇑x) ⬝ᵥ (A *ᵥ ⇑x) := by
      rw [Finsupp.sum_fintype]
      · show ∑ i, (x.sum fun j xj => star (x i) * A i j * xj) = ∑ i, x i * ∑ j, A i j * x j
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.sum_fintype]
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [star_trivial]; ring
        · intro j; simp
      · intro i; simp
    rw [key, ← hre]
    refine hB _ ((LinearEquiv.map_ne_zero_iff _).2 ?_)
    intro h0
    exact hx (Finsupp.ext fun i => by simpa using congrFun h0 i)
  obtain ⟨P, hP, c, hPA, hPC⟩ := simdiag A C hApd hCh
  have hcong : ∀ (M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      (w : Fin (Module.finrank ℝ E) → ℝ),
      (P *ᵥ w) ⬝ᵥ (M *ᵥ (P *ᵥ w)) = w ⬝ᵥ ((Pᵀ * M * P) *ᵥ w) := by
    intro M w
    rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose P w, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨(Matrix.toLinearEquiv' P hP.invertible).trans e.equivFun.symm,
    fun i => 1 + (c i : ℂ) * I, fun i => by simp, fun w => ?_⟩
  have hd : diagonal c *ᵥ w = fun i => c i * w i := funext (Matrix.mulVec_diagonal c w)
  show B (e.equivFun.symm (P *ᵥ w)) (e.equivFun.symm (P *ᵥ w)) = _
  rw [← Complex.re_add_im (B (e.equivFun.symm (P *ᵥ w)) (e.equivFun.symm (P *ᵥ w))), hre, him,
    hcong, hcong, hPA, hPC, Matrix.one_mulVec, hd]
  show ((∑ i, w i * w i : ℝ) : ℂ) + ((∑ i, w i * (c i * w i) : ℝ) : ℂ) * I = _
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
