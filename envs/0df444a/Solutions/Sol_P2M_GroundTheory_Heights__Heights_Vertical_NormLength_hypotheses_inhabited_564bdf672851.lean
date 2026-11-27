-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormLength_hypotheses_inhabited_564bdf672851
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:32.892933+00:00
-- url     : https://prove2.me/submissions/6fe5ec2a-6860-4b38-8bb3-9293ccd24913

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormLength
theorem _root_.solution :
    Function.Injective (fun x : ℤ_[2] => (1 : ℤ_[2]) * x) := fun x y h => by
  simpa using h
end NormLength
end GroundTheory.Heights₂.Heights.Vertical
