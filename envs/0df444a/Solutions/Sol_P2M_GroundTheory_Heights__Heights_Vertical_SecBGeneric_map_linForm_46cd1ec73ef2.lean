-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_linForm_46cd1ec73ef2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:18.855201+00:00
-- url     : https://prove2.me/submissions/9db26d99-b83f-4248-b8af-fa34d3ff80e1

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
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by
  simp [linForm, map_sum]
end GroundTheory.Heights₂.Heights.Vertical.SecBGeneric
