-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_parY_14f8a84ea9a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:22.615423+00:00
-- url     : https://prove2.me/submissions/f4d0f0ac-4e13-49b2-b1a0-0a9a3fe31638

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBGeneric

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
open GroundTheory.Heights₂.Heights.Vertical.SecBGeneric
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBGeneric
theorem _root_.solution (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (p : Par e n) :
    parToFrac e n v (parY e n v p) = parYF K e n p := by
  rw [parY, parToFrac, IsLocalization.lift_eq, parYF]
end GroundTheory.Heights₂.Heights.Vertical.SecBGeneric
