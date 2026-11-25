-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SecRankSpecialize_secMap_mk_98e321aae280
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:01.441304+00:00
-- url     : https://prove2.me/submissions/5517ff32-3294-40f9-b406-06ff17574bb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecRankSpecialize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SecRankSpecialize
open Vertical
namespace GroundTheory.Heights₂.Heights.SecRankSpecialize
theorem _root_.solution {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (p : MvPolynomial (Fin n) R) :
    secMap S Q y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := rfl
end GroundTheory.Heights₂.Heights.SecRankSpecialize
