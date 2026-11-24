-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_monomial_dc51169fa57e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:54.367864+00:00
-- url     : https://prove2.me/submissions/f7f653a2-cedf-4bbc-a353-0dd35bb91f0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8

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
theorem _root_.solution (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I)
    (f : Fin (N + 1) →₀ ℕ) (hf : (s : Poly S N) = monomial f 1) :
    iotaP I (LocalizedModule.mk p s) = AddMonoidAlgebra.single (-expToInt N f) 1 * toL S N p := by
  rw [localizationToLaurent_mk_eq_iff, hf, toL_monomial, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
    add_neg_cancel, mul_one]
  exact (one_mul _).symm
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
