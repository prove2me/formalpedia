-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_X_inl_7dae525d82ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:28.350505+00:00
-- url     : https://prove2.me/submissions/250396c3-eb47-4b0e-90de-009ca0dba71a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

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
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (j : Fin n) :
    specHom e n v (X (Sum.inl j)) = X j := by
  simp [specHom]
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
