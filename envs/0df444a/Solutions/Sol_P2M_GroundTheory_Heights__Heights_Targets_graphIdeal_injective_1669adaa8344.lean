-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_injective_1669adaa8344
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:07.154368+00:00
-- url     : https://prove2.me/submissions/ee456c1d-b651-4b4c-baf1-8c861b591497

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8

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
theorem _root_.solution (p : MvPolynomial (Fin n) ℂ) : Function.Injective (fun W => graphIdeal W p) :=
  Ideal.comap_injective_of_surjective _ (graphHom_surjective p)
end GroundTheory.Heights₂.Heights.Targets
