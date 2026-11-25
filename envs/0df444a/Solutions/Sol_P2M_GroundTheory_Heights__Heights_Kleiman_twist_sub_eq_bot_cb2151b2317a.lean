-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:30.829418+00:00
-- url     : https://prove2.me/submissions/29622637-288e-4486-8253-f9e8ada1d9c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage

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
theorem _root_.solution {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  rw [hF I, Submodule.mem_bot] at hy
  rw [hy, smul_zero]
end GroundTheory.Heights₂.Heights.Kleiman
