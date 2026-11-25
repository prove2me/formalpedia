-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.bichar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:25.934784+00:00
-- url     : https://prove2.me/submissions/5357b96e-edca-4c31-aa5a-3ab0ae09028e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdTestInfW_IsBichar_zero_left
import Theorems.Thm_PI_VolStabW_SdTestInfW_IsBichar_freq
import Theorems.Thm_PI_VolStabW_SdTestInfW_measurable_freq
import Theorems.Thm_PI_VolStabW_SdTestInfW_freq_add

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
open scoped RealInnerProductSpace
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution {χ : W → W → ℂ} (h : IsBichar χ) :
    ∃ L : W →L[ℝ] W, ∀ x y, χ x y = (Real.fourierChar ⟪x, L y⟫ : ℂ) := by
  classical
  choose β hβ using fun v y => h.freq v y
  let b := stdOrthonormalBasis ℝ W
  have hm : ∀ j, Measurable (fun y => β (b j) y) := fun j =>
    measurable_freq h (b j) _ (fun y => hβ (b j) y)
  have ha : ∀ j y y', β (b j) (y + y') = β (b j) y + β (b j) y' := fun j =>
    freq_add h (b j) (fun y => β (b j) y) (fun y => hβ (b j) y)
  let Lf : W → W := fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
  let Lm : W →+ W := AddMonoidHom.mk' Lf fun y y' => by
    simp only [Lf, ha, add_div, add_smul, Finset.sum_add_distrib]
  have hLm : Measurable Lm := by
    show Measurable fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
    exact Finset.measurable_sum Finset.univ fun j _ => ((hm j).div_const _).smul_const (b j)
  have hLc : Continuous Lm := Measure.AddMonoidHom.continuous_of_measurable Lm hLm
  refine ⟨Lm.toRealLinearMap hLc, fun x y => ?_⟩
  have hprod : ∀ s : Finset (Fin (Module.finrank ℝ W)),
      χ (∑ j ∈ s, ⟪b j, x⟫ • b j) y = ∏ j ∈ s, χ (⟪b j, x⟫ • b j) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h.zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, h.addL, ih]
  have e1 : χ x y = χ (∑ j, ⟪b j, x⟫ • b j) y := by rw [b.sum_repr' x]
  rw [e1, hprod]
  have e2 : ∀ j, χ (⟪b j, x⟫ • b j) y = exp (↑(β (b j) y * ⟪b j, x⟫) * I) := fun j => hβ _ _ _
  simp only [e2]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  have hLy : ⟪x, (Lm.toRealLinearMap hLc) y⟫ = ∑ j, β (b j) y / (2 * Real.pi) * ⟪b j, x⟫ := by
    show ⟪x, Lf y⟫ = _
    simp only [Lf, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  rw [hLy]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
end PI.VolStabW.SdTestInfW
