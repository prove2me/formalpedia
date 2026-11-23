-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:08.533956+00:00
-- url     : https://prove2.me/submissions/a99c6290-5ea3-4d78-bf0e-cfb6783c5e87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_JJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  have hJJ := rq_JJ ε
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hXH : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [eq_neg_of_add_eq_zero_left hX', neg_mul]
  have hAH : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv, Matrix.conjTranspose_smul, hXH]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_neg]
  have hEu : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := Matrix.isUnit_exp _
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, hAH, Matrix.exp_conj _ _ hJu, hJinv, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hEu), mul_one]
end ReciprocityTheory.ChartRestriction.DS
