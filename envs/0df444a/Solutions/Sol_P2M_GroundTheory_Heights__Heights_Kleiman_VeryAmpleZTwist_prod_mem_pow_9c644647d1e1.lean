-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_prod_mem_pow_9c644647d1e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:35.684721+00:00
-- url     : https://prove2.me/submissions/9c1ebff5-79b1-4ad8-9f68-9c2c86208b6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
theorem _root_.solution (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.sub I) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span ⟨h l, hh l, _, ih, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
