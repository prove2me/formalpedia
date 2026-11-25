-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_isPrime_99ea8f7d95b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:40.727805+00:00
-- url     : https://prove2.me/submissions/f4d93286-076b-450e-8357-3b4c42e6036e

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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p).IsPrime :=
  Ideal.comap_isPrime _ _
end GroundTheory.Heights₂.Heights.Targets
