-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_linForm_f08d93cacfab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:24.665811+00:00
-- url     : https://prove2.me/submissions/01dbb701-71c6-4db0-a404-ef82143fcb66

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
variable {σ R S : Type*} [CommRing R] [CommRing S]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution {n : ℕ} (u : Fin n → R) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
