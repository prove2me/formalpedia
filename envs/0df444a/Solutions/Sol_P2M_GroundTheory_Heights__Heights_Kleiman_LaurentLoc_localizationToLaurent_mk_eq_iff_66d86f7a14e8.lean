-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:01.617834+00:00
-- url     : https://prove2.me/submissions/7869ef06-83ff-48c5-9167-dd7012bfb580

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
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I) (y : LRing S N) :
    iotaP I (LocalizedModule.mk p s) = y ↔ toL S N p = toL S N s * y := by
  change (↑((isUnit_end (S := S) I s).unit⁻¹) : Module.End (Poly S N) (LRing S N))
      (Algebra.linearMap (Poly S N) (LRing S N) p) = y ↔ _
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
