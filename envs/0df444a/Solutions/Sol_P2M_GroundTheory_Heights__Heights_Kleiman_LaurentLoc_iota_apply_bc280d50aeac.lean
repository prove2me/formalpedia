-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_apply_bc280d50aeac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:53.791269+00:00
-- url     : https://prove2.me/submissions/a83e9e49-7ea3-44be-b263-69340a78503e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (I : StdCell N) (z : LocMod S N (Poly S N) I.1) : iota I z = (iotaP I.1 z).coeff := rfl
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
