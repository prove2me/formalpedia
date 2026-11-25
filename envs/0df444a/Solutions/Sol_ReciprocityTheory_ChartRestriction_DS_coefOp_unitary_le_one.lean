-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefOp_unitary_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:09.440429+00:00
-- url     : https://prove2.me/submissions/d290bf08-0303-4216-8d60-0d87d706785b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp

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
theorem _root_.solution {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k‖ ≤ 1 := by
  have hU : star (Matrix.toEuclideanCLM (𝕜 := ℂ) k) * Matrix.toEuclideanCLM (𝕜 := ℂ) k = 1 := by
    rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hk, map_one]
  have h := CStarRing.norm_star_mul_self (x := Matrix.toEuclideanCLM (𝕜 := ℂ) k)
  rw [hU] at h
  have h1 : ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) k)]
end ReciprocityTheory.ChartRestriction.DS
