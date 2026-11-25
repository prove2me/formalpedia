-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefOp_apply_le_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:02.341987+00:00
-- url     : https://prove2.me/submissions/faa91ccf-1515-4d2e-9b8d-6ae92a001492

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
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ ≤ ‖A‖ * ‖v‖ := by
  have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := rfl
  rw [h1, ← Matrix.frobenius_norm_replicateCol (ι := Fin 1), Matrix.replicateCol_mulVec]
  calc ‖A * Matrix.replicateCol (Fin 1) (WithLp.ofLp v)‖
      ≤ ‖A‖ * ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp v)‖ := Matrix.frobenius_norm_mul _ _
    _ = ‖A‖ * ‖v‖ := by
      congr 1
      exact Matrix.frobenius_norm_replicateCol (ι := Fin 1) (WithLp.ofLp v)
end ReciprocityTheory.ChartRestriction.DS
