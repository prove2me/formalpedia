-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubFamily_exists_pow_6e2f7e5f6f11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:01.342197+00:00
-- url     : https://prove2.me/submissions/e3c50ae5-c12a-4a06-8439-896e531209e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubFamilyTwistPow

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
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SubFamily
theorem _root_.solution (Q : SubFamily S x Ω) (n : ℕ) :
    ∃ P : SubFamily S x Ω, P.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨(twistBundle S x 0).toSubFamily, rfl⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.twistFam Q, ?_⟩
    change P.toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [hP]
end SubFamily
end GroundTheory.Heights₂.Heights.Kleiman
