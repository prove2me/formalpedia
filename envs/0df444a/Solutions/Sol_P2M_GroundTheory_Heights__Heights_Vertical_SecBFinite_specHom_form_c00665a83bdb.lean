-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_form_c00665a83bdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:09.552555+00:00
-- url     : https://prove2.me/submissions/e96f0e2c-ebae-4981-8fa3-4772421da6bb

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
theorem _root_.solution (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (i : Fin (e + 1)) :
    specHom e n v (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) =
      linForm fun j => parY e n v (parIdx e n (i, j)) := by
  simp [specHom, linForm, map_sum]
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
