-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefOp_unitary_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:19.422879+00:00
-- url     : https://prove2.me/submissions/e77ac57d-768c-41f2-9950-b017fbcebc53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_norm_exp_clm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_unitary_le_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_le_sqrt_hs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (k * NormedSpace.exp X)‖ ≤ Real.exp (Real.sqrt (S7.hs X)) := by
  have hc : Continuous (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hexp : Matrix.toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp X) =
      NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) X) := by
    let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedRing
    let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAlgebra
    refine NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) _ hc X ?_
    rw [NormedSpace.expSeries_radius_eq_top]
    simp
  rw [map_mul, hexp]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k * NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) X)‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k‖ * ‖NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) X)‖ :=
        norm_mul_le _ _
    _ ≤ 1 * Real.exp (Real.sqrt (S7.hs X)) :=
        mul_le_mul (coefOp_unitary_le_one hk)
          ((coefOp_norm_exp_clm _).trans (Real.exp_le_exp.mpr (coefOp_le_sqrt_hs X)))
          (norm_nonneg _) zero_le_one
    _ = Real.exp (Real.sqrt (S7.hs X)) := one_mul _
end ReciprocityTheory.ChartRestriction.DS
