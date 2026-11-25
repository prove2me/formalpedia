-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.testEx_bichar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:29.781337+00:00
-- url     : https://prove2.me/submissions/4eb89e13-af57-4207-9e31-984aa608ac00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdTestInfW_bichar_eq
import Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_kernel
import Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_fourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution (μ : Measure W) [μ.IsAddHaarMeasure] {χ : W → W → ℂ} (h : IsBichar χ) :
    SdUniqW.TestEx μ χ := by
  obtain ⟨L, hL⟩ := bichar_eq h
  by_cases hs : Function.Surjective L
  · have hi : Function.Injective L :=
      (LinearMap.injective_iff_surjective (f := (L : W →ₗ[ℝ] W))).2 hs
    let A : W ≃L[ℝ] W :=
      (LinearEquiv.ofBijective (L : W →ₗ[ℝ] W) ⟨hi, hs⟩).toContinuousLinearEquiv
    have e : χ = fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ) :=
      funext₂ fun x y => by rw [hL x y]; rfl
    rw [e]; exact testEx_fourier μ A
  · have hK : (LinearMap.range (L : W →ₗ[ℝ] W))ᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]; exact hs
    obtain ⟨t, htK, ht0⟩ := (Submodule.ne_bot_iff _).1 hK
    refine testEx_kernel μ χ h.addL h.contL t ht0 fun y => ?_
    have h0 : ⟪t, L y⟫ = 0 :=
      (Submodule.mem_orthogonal' _ t).1 htK _ (LinearMap.mem_range_self (L : W →ₗ[ℝ] W) y)
    rw [hL, h0, AddChar.map_zero_eq_one, Circle.coe_one]
end PI.VolStabW.SdTestInfW
