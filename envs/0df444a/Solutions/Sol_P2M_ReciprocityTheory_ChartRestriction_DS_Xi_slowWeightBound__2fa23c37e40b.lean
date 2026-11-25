-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_slowWeightBound__2fa23c37e40b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:46.166244+00:00
-- url     : https://prove2.me/submissions/a918f2a1-6524-440a-b4ed-9c7d86818a73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_int_abs_rpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_slowWeight_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_measurable_slowWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open PolynomialGrowthIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution : SLOW := by
  intro n T κ hκ0 hκ1
  refine ⟨3 ^ T / (1 - κ) + 1, fun t A b R hR ht hT hA => ?_⟩
  set f := slowly t A b with hf_def
  set I := ∫⁻ β, f β with hI
  have hfm : Measurable f := measurable_slowWeight t A b
  have hw : Measurable fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ)) := by fun_prop
  set c : ℝ := 3 ^ (∑ i, t i) / (2 * R) with hc
  set q : ℝ := R ^ (1 - κ) / (1 - κ) with hq

  have hcen : ∀ β ∈ Icc (-R) R, f β ≤ ENNReal.ofReal c * I := by
    intro β hβ
    have hb : |β| ≤ R := abs_le.2 ⟨hβ.1, hβ.2⟩
    have key : f β * ENNReal.ofReal (2 * R) ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by
      calc f β * ENNReal.ofReal (2 * R) = ∫⁻ _ in Icc (-R) R, f β := by
            rw [setLIntegral_const, Real.volume_Icc]; congr 2; ring
        _ ≤ ∫⁻ β' in Icc (-R) R, ENNReal.ofReal (3 ^ ∑ i, t i) * f β' :=
            setLIntegral_mono (measurable_const.mul hfm) fun β' hβ' =>
              slowWeight_le hR ht hA hb (abs_le.2 ⟨hβ'.1, hβ'.2⟩)
        _ = ENNReal.ofReal (3 ^ ∑ i, t i) * ∫⁻ β' in Icc (-R) R, f β' := lintegral_const_mul _ hfm
        _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by gcongr; exact setLIntegral_le_lintegral _ _
    have hinv : ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
    calc f β = f β * ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I * ENNReal.ofReal (1 / (2 * R)) := by gcongr
      _ = ENNReal.ofReal c * I := by
          rw [hc, div_eq_mul_one_div (3 ^ ∑ i, t i), ENNReal.ofReal_mul (by positivity)]; ring

  have hA1 : ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤
      ENNReal.ofReal (c * (2 * q)) * I := by
    calc ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in Icc (-R) R, ENNReal.ofReal c * I * ENNReal.ofReal (|β| ^ (-κ)) :=
          setLIntegral_mono (measurable_const.mul hw) fun β hβ => by gcongr; exact hcen β hβ
      _ = ENNReal.ofReal c * I * ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) :=
          lintegral_const_mul _ hw
      _ ≤ ENNReal.ofReal c * I * (2 * ENNReal.ofReal q) :=
          by gcongr; exact int_abs_rpow hR hκ0 hκ1
      _ = ENNReal.ofReal (c * (2 * q)) * I := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          try ring

  have hA2 : ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤ ENNReal.ofReal (R ^ (-κ)) * I := by
    calc ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (R ^ (-κ)) := by
          refine setLIntegral_mono (hfm.mul measurable_const) fun β hβ => ?_
          have hb : R < |β| := by
            by_contra h
            exact hβ (abs_le.1 (not_lt.1 h))
          gcongr f β * ?_
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hR hb.le (by linarith))
      _ = (∫⁻ β in (Icc (-R) R)ᶜ, f β) * ENNReal.ofReal (R ^ (-κ)) := lintegral_mul_const _ hfm
      _ ≤ I * ENNReal.ofReal (R ^ (-κ)) := by gcongr; exact setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (R ^ (-κ)) * I := mul_comm _ _

  have hRk : R ^ (1 - κ) = R * R ^ (-κ) := by
    rw [show 1 - κ = 1 + -κ by ring, Real.rpow_add hR, Real.rpow_one]
  have hcq : c * (2 * q) = 3 ^ (∑ i, t i) * R ^ (-κ) / (1 - κ) := by
    rw [hc, hq, hRk]
    have : (1 - κ) ≠ 0 := by linarith
    field_simp
    try ring
  have hsT : (3 : ℝ) ^ (∑ i, t i) ≤ 3 ^ T := Real.rpow_le_rpow_of_exponent_le (by norm_num) hT
  have hRp : 0 < R ^ (-κ) := Real.rpow_pos_of_pos hR _
  have hreal : c * (2 * q) + R ^ (-κ) ≤ (3 ^ T / (1 - κ) + 1) * R ^ (-κ) := by
    rw [hcq, add_mul, one_mul, div_mul_eq_mul_div]
    gcongr
    try linarith
  calc ∫⁻ β, slowly t A b β * ENNReal.ofReal (|β| ^ (-κ))
      = (∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) :=
        (lintegral_add_compl (fun β => f β * ENNReal.ofReal (|β| ^ (-κ))) measurableSet_Icc).symm
    _ ≤ ENNReal.ofReal (c * (2 * q)) * I + ENNReal.ofReal (R ^ (-κ)) * I := add_le_add hA1 hA2
    _ = ENNReal.ofReal (c * (2 * q) + R ^ (-κ)) * I := by
        rw [ENNReal.ofReal_add (by positivity) hRp.le, add_mul]
    _ ≤ ENNReal.ofReal ((3 ^ T / (1 - κ) + 1) * R ^ (-κ)) * I :=
        by gcongr
end ReciprocityTheory.ChartRestriction.DS.Xi
