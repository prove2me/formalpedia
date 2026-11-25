-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_uniform_coeff_bound_56e632b89056
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:53.888167+00:00
-- url     : https://prove2.me/submissions/27bc0857-9093-4f12-8a7e-eeeaade8dd4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_coeff_le_sum_abs_coeff_f3bc80b28092
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.antisymEvalOn_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : Type*} (G : E →ₗ[ℝ] MvPolynomial σ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : E) (m : σ →₀ ℕ), |coeff m (G y)| ≤ C * ‖y‖ := by
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → (E →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖c i‖ * ∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))|,
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _), fun y m => ?_⟩
  have hy : G y = ∑ i, b.repr y i • G (b i) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [map_smul]
  rw [hy, coeff_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [coeff_smul, smul_eq_mul, abs_mul]
  have h1 : |b.repr y i| ≤ ‖c i‖ * ‖y‖ := by
    have := (c i).le_opNorm y
    simpa [c, Real.norm_eq_abs] using this
  calc |b.repr y i| * |coeff m (G (b i))|
      ≤ (‖c i‖ * ‖y‖) * ∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))| :=
        mul_le_mul h1 (abs_coeff_le_sum_abs_coeff _ _) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖c i‖ * (∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))|) * ‖y‖ := by ring
end GroundTheory.Heights₂.Heights
