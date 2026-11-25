-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_span_denom_num_eq_6cb8a20bd333
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:53.50154+00:00
-- url     : https://prove2.me/submissions/f47b2702-dab7-4430-afd5-60249f6ec5eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (g : SL(2, ℤ)) (τ : ℂ) :
    Submodule.span ℤ ({(g 1 0 : ℂ) * τ + g 1 1, (g 0 0 : ℂ) * τ + g 0 1} : Set ℂ) =
      Submodule.span ℤ ({1, τ} : Set ℂ) := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  apply le_antisymm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_span_pair.mpr ⟨g 1 1, g 1 0, by simp [zsmul_eq_mul]; ring⟩
    · exact Submodule.mem_span_pair.mpr ⟨g 0 1, g 0 0, by simp [zsmul_eq_mul]; ring⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · refine Submodule.mem_span_pair.mpr ⟨g 0 0, -g 1 0, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination hdet
    · refine Submodule.mem_span_pair.mpr ⟨-g 0 1, g 1 1, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination τ * hdet
end GroundTheory.Heights₂.Theta
