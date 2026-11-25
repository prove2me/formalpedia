-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_eq_bot_405b85e0afc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:14.381067+00:00
-- url     : https://prove2.me/submissions/399b284d-ee91-43fa-93bf-5681942894a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a

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
universe u v w u₁ v₁ w₁
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
omit [Module k E] [IsScalarTower k Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  | 0, _, _, I => hF I
  | t + 1, _, _, I => twist_sub_eq_bot (fun I => solution hF t _ _ I) _ I
end GroundTheory.Heights₂.Heights.Kleiman
