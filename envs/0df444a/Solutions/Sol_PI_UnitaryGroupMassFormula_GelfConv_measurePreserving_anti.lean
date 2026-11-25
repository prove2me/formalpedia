-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:20.233844+00:00
-- url     : https://prove2.me/submissions/18b0fc6b-60b8-4061-af96-fc887b68812a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_isInvInvariant_of_compact
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_measurePreserving_of_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfConv
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (τ : G → G) (hc : Continuous τ)
    (hm : ∀ x y, τ (x * y) = τ y * τ x) (hi : ∀ x, τ (τ x) = x) :
    MeasurePreserving τ μ μ := by
  have := isInvInvariant_of_compact μ
  have h1 : τ 1 = 1 := by
    have := hm 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, mul_inv_cancel, h1]
  let σ : G →* G :=
    { toFun := fun x => τ x⁻¹
      map_one' := by simp [h1]
      map_mul' := fun x y => by simp only [mul_inv_rev]; rw [hm] }
  have hσc : Continuous σ := hc.comp continuous_inv
  have hσs : Function.Surjective σ := fun y => ⟨(τ y)⁻¹, by simp [σ, hi]⟩
  have hσ := measurePreserving_of_hom μ σ hσc hσs
  have : τ = Inv.inv ∘ σ := funext fun x => by simp [σ, hinv]
  rw [this]
  exact (measurePreserving_inv μ).comp hσ
end PI.UnitaryGroupMassFormula.GelfConv
