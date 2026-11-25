-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_mono_7f5bbd22b5ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:41.652966+00:00
-- url     : https://prove2.me/submissions/905504e1-7afa-464c-baf8-5521bd3ad8e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal

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
theorem _root_.solution {J W : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) (h : J ≤ W) :
    graphIdeal J p ≤ graphIdeal W p :=
  Ideal.comap_mono h
end GroundTheory.Heights₂.Heights.Targets
