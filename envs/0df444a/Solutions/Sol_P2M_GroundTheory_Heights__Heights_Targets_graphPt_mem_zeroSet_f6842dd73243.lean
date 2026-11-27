-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphPt_mem_zeroSet_f6842dd73243
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:43.319335+00:00
-- url     : https://prove2.me/submissions/5c353642-d7c7-4c8b-a79d-ba10a34db204

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_eval_graphPt_b9a26ea46c65

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : graphPt p x ∈ zeroSet (graphIdeal J p) := by
  intro q hq
  rw [eval_graphPt]
  exact hx _ hq
end GroundTheory.Heights₂.Heights.Targets
