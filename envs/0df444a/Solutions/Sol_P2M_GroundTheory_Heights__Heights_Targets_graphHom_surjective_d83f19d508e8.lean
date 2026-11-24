-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:59.457636+00:00
-- url     : https://prove2.me/submissions/6665ccbf-35c6-4620-b268-19f843eca8ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299

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
theorem _root_.solution (p : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom p) :=
  fun q => ⟨rename Fin.castSucc q, graphHom_rename p q⟩
end GroundTheory.Heights₂.Heights.Targets
