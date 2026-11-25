-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap__4078fa1dc1cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:49.566645+00:00
-- url     : https://prove2.me/submissions/ce5237b7-b2ae-4458-a38a-724fa3d75553

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity

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
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (x : MvPolynomial (Par e n) (𝓞 K)) :
    parToFrac e n v (algebraMap _ (ParDVR e n v) x) = algebraMap _ (ParFrac K e n) x := by
  rw [parToFrac, IsLocalization.lift_eq]
end GroundTheory.Heights₂.Heights.Vertical
