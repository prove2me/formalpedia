-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:38.369101+00:00
-- url     : https://prove2.me/submissions/9688cb1a-a03b-46a3-8872-bd8e8af520cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_IntegrableOfContinuousCpt
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_integrable_of_continuous_cpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution {N : ℕ} (μ : Measure G) [μ.IsHaarMeasure] (R : G → Matrix (Fin N) (Fin N) ℂ)
    (hR : ∀ i j, Continuous fun g => R g i j) (hRm : ∀ x y, R (x * y) = R x * R y)
    (f₁ f₂ : G → ℂ) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (i j : Fin N) :
    ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ) =
      ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by
  calc ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ)
      = ∑ k, ∫ x, f₁ x * R x i k * (∫ y, f₂ y * R y k j ∂μ) ∂μ := by
        congr 1; funext k; rw [integral_mul_const]
    _ = ∫ x, ∑ k, f₁ x * R x i k * (∫ y, f₂ y * R y k j ∂μ) ∂μ := by
        rw [integral_finsetSum]
        intro k _
        exact integrable_of_continuous_cpt μ ((h₁.mul (hR i k)).mul continuous_const)
    _ = ∫ x, ∫ y, f₁ x * f₂ y * R (x * y) i j ∂μ ∂μ := by
        congr 1; funext x
        have e : ∀ y, f₁ x * f₂ y * R (x * y) i j = ∑ k, f₁ x * R x i k * (f₂ y * R y k j) := by
          intro y; rw [hRm, Matrix.mul_apply, Finset.mul_sum]; congr 1; funext k; ring
        simp_rw [e]
        rw [integral_finsetSum]
        · congr 1; funext k; rw [integral_const_mul]
        · intro k _
          exact integrable_of_continuous_cpt μ (continuous_const.mul (h₂.mul (hR k j)))
    _ = ∫ x, ∫ z, f₁ x * f₂ (x⁻¹ * z) * R z i j ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f₁ x * f₂ (x⁻¹ * z) * R z i j) x]
        simp only [inv_mul_cancel_left]
    _ = ∫ z, ∫ x, f₁ x * f₂ (x⁻¹ * z) * R z i j ∂μ ∂μ := by
        rw [integral_integral_swap]
        exact integrable_of_continuous_cpt (μ.prod μ)
          (F := Function.uncurry fun x z => f₁ x * f₂ (x⁻¹ * z) * R z i j)
          (((h₁.comp continuous_fst).mul
            (h₂.comp (continuous_fst.inv.mul continuous_snd))).mul ((hR i j).comp continuous_snd))
    _ = ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by
        congr 1; funext z; rw [integral_mul_const]
end PI.UnitaryGroupMassFormula.GelfCpt
