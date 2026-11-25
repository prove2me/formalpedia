-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_sub_c165d8124f4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:16.459633+00:00
-- url     : https://prove2.me/submissions/ebbcab96-6533-439f-bcf5-8c67a47cb65e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
theorem _root_.solution {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {u v : Ω}
    (hu : u ∈ Q.sub (liftChart hxy J)) (hv : v ∈ Q.sub (liftChart hxy J)) :
    r (u - v) = r u - r v := by
  have := h.add J (u - v) (sub_mem hu hv) v hv
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm
end GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
