-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_of_bot_8adbac9f88d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:07.065513+00:00
-- url     : https://prove2.me/submissions/7777c0cf-f7cc-4f62-a577-bf9b7bf68cc6

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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by
  have hq : ∀ I, SubSystem.quotSub F₁ F₂ I = ⊥ := fun I => by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => Subtype.ext ?_
    have hy' : (y : E) ∈ F₂.sub I := hy
    rw [h I, Submodule.mem_bot] at hy'
    exact hy'
  let φ : ∀ I, F₁.sub I ≃ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) := fun I =>
    (Submodule.quotEquivOfEqBot _ (hq I)).symm
  have hφ : ∀ I J h m, φ J (F₁.res I J h m) = SubSystem.quotRes F₁ F₂ I J h (φ I m) := fun _ _ _ _ => rfl
  unfold eulerCharQuot eulerChar
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm
end GroundTheory.Heights₂.Heights.Kleiman
