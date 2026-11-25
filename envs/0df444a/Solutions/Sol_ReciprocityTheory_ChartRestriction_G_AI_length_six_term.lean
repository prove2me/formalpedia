-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_six_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:37.765178+00:00
-- url     : https://prove2.me/submissions/713334a8-70aa-4385-a501-0501c930f91d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_range_add_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A : Type*} [Ring A] {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    [AddCommGroup M₃] [Module A M₃] [AddCommGroup M₄] [Module A M₄]
    [AddCommGroup M₅] [Module A M₅] [AddCommGroup M₆] [Module A M₆]
    {f₁ : M₁ →ₗ[A] M₂} {f₂ : M₂ →ₗ[A] M₃} {f₃ : M₃ →ₗ[A] M₄} {f₄ : M₄ →ₗ[A] M₅}
    {f₅ : M₅ →ₗ[A] M₆} (h₁ : Function.Injective f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ f₃) (h₄ : Function.Exact f₃ f₄) (h₅ : Function.Exact f₄ f₅)
    (h₆ : Function.Surjective f₅) :
    length A M₁ + length A M₃ + length A M₅ = length A M₂ + length A M₄ + length A M₆ := by
  have e1 : length A M₁ = length A (LinearMap.range f₁) := (LinearEquiv.ofInjective f₁ h₁).length_eq
  have e6 : length A (LinearMap.range f₅) = length A M₆ :=
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 h₆)).length_eq
  rw [e1, length_eq_range_add_range h₂, length_eq_range_add_range h₃, length_eq_range_add_range h₄,
    length_eq_range_add_range h₅, ← e6]
  ring
end ReciprocityTheory.ChartRestriction.G.AI
