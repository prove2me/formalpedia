-- Prove2me | solution 1 for Pr6453.tail_ratios
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T18:11:37.066594+00:00
-- url     : https://prove2.me/submissions/a451d594-ea02-4a50-88f4-6c1026746099

/-
# PR #6453: the three tail ratios

`α`, `γ` and `δ` of the strictification, from the two proved halves of the shifted enclosure.
-/
import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification
import Definitions.Def_Pr6453_TailRatiosFixed
import Theorems.Thm_Pr6453_shifted_lower
import Theorems.Thm_Pr6453_shifted_upper

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pr6453

noncomputable section

/-- `log 3 ≥ 1.098612288143` — the same Taylor enclosure used for the rank logarithms. -/
theorem log_three_lower : (1.098612288143 : ℝ) ≤ Real.log 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num) 18
  norm_num at h
  have hle := abs_le.mp h
  have e : Real.log (3:ℝ) = Real.log (3/4) + 2 * Real.log 2 := by
    have h1 : Real.log ((3:ℝ)/4) = Real.log 3 - Real.log 4 :=
      Real.log_div (by norm_num) (by norm_num)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [e]
  linarith [hle.1, Real.log_two_gt_d9]

/-- `12^(1/7) ≥ 1.41`, from `exp x ≥ 1 + x + x²/2` at `x = (log 12)/7 ≥ 0.354986`. -/
theorem twelve_pow : (1.41 : ℝ) ≤ (12:ℝ)^((1:ℝ)/7) := by
  have h3 := log_three_lower
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h12 : (2.484906648 : ℝ) ≤ Real.log 12 := by
    have e : Real.log (12:ℝ) = 2 * Real.log 2 + Real.log 3 := by
      rw [show (12:ℝ) = 2^2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      norm_num
    rw [e]; linarith
  have hx : (0.354986 : ℝ) ≤ Real.log 12 * ((1:ℝ)/7) := by linarith
  have h1 : (1.41 : ℝ) ≤ Real.exp (0.354986 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.354986) 3
    have hval : (1.41 : ℝ) ≤ (∑ i ∈ Finset.range 3, (0.354986:ℝ)^i / (i.factorial : ℝ)) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 12)]
  have h2' : Real.exp (0.354986 : ℝ) ≤ Real.exp (Real.log 12 * ((1:ℝ)/7)) :=
    Real.exp_le_exp.mpr hx
  linarith only [h1, h2']

/-- `12^t ≥ 1` at the tested saving. -/
theorem twelve_pow_t : (1 : ℝ) ≤ (12:ℝ)^(tested:ℝ) :=
  Real.one_le_rpow (by norm_num) (by unfold tested; norm_num)

theorem targets_lower : (183876.163374196000 : ℝ) ≤ moment targets (1 - (tested:ℝ)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := shifted_lower
  simp only [moment, targets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.cast_ofNat, Nat.cast_one, Real.one_rpow, mul_one, add_zero]
  linarith only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]

theorem paid_upper : moment paid (1 - (tested:ℝ)) ≤ (183876.163305504000 : ℝ) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩ := shifted_upper
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    c1, c2, c3, c4, c5⟩ := shifted_lower
  simp only [moment, paid, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.cast_ofNat, Nat.cast_one, Real.one_rpow, mul_one, add_zero]
  linarith only [c1, c2, c3, c4, c5, b1, b2, b3, b4, b5, b6, b7]

theorem paid_upper_one : moment paid (1 - (tested:ℝ) + 1/7) ≤ (242327.543574028000 : ℝ) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩ := shifted_upper
  simp only [moment, paid, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.cast_ofNat, Nat.cast_one, Real.one_rpow, mul_one, add_zero]
  linarith only [b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19]

theorem alpha_lt : alpha2 < 1 - (reserve : ℝ) := by
  have hT := targets_lower
  have hP := paid_upper
  have hres : (0:ℝ) < 1 - (reserve : ℝ) := by unfold reserve; norm_num
  have hnum : (183876.163305504000 : ℝ) < (1 - (reserve : ℝ)) * 183876.163374196000 := by
    unfold reserve; norm_num
  have hTpos : (0:ℝ) < moment targets (1 - (tested:ℝ)) :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 183876.163374196000) hT
  have hstep : (1 - (reserve:ℝ)) * (183876.163374196000:ℝ) ≤
      (1 - (reserve:ℝ)) * moment targets (1 - (tested:ℝ)) :=
    mul_le_mul_of_nonneg_left hT (le_of_lt hres)
  rw [alpha2, div_lt_iff₀ hTpos]
  nlinarith only [hP, hstep, hnum]

theorem gammaTail_lt : gammaTail2 < (decay : ℝ) := by
  have hT := targets_lower
  have hP := paid_upper_one
  have hm : (1.41:ℝ) ≤ (12:ℝ)^((1:ℝ)/7) := twelve_pow
  have hnum : (242327.543574028000 : ℝ) < (31/32) * 1.41 * 183876.163374196000 := by norm_num
  have h12 : (0:ℝ) < (12:ℝ)^((1:ℝ)/7) := Real.rpow_pos_of_pos (by norm_num) _
  have hdec : (decay : ℝ) = 31/32 := by unfold decay; norm_num
  have hTpos : (0:ℝ) < moment targets (1 - (tested:ℝ)) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 183876.163374196000) hT
  have hpos' : (0:ℝ) < (12:ℝ)^((1:ℝ)/7) * moment targets (1 - (tested:ℝ)) := by positivity
  rw [gammaTail2, div_lt_iff₀ hpos', hdec]
  have hstep : (31/32) * 1.41 * 183876.163374196000 ≤
      (31/32) * (12:ℝ)^((1:ℝ)/7) * moment targets (1 - (tested:ℝ)) := by
    nlinarith only [hm, hT, h12, (by norm_num : (0:ℝ) ≤ (31:ℝ)/32)]
  linarith only [hP, hnum, hstep]

theorem deltaTail_lt : deltaTail2 < (decay : ℝ) := by
  have hT := targets_lower
  have hm : (1:ℝ) ≤ (12:ℝ)^(tested:ℝ) := twelve_pow_t
  have hnum : (13652 * 13 : ℝ) < (31/32) * 1 * 183876.163374196000 := by norm_num
  have h12 : (0:ℝ) < (12:ℝ)^(tested:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hdec : (decay : ℝ) = 31/32 := by unfold decay; norm_num
  have hTpos : (0:ℝ) < moment targets (1 - (tested:ℝ)) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 183876.163374196000) hT
  have hpos' : (0:ℝ) < (12:ℝ)^(tested:ℝ) * moment targets (1 - (tested:ℝ)) := by positivity
  rw [deltaTail2, div_lt_iff₀ hpos', hdec]
  nlinarith only [hT, hm, hnum, h12, hTpos]

/-- **The three tail ratios of the strictification.** -/
theorem tail_ratios :
    alpha2 < 1 - (reserve : ℝ) ∧ gammaTail2 < (decay : ℝ) ∧ deltaTail2 < (decay : ℝ) :=
  ⟨alpha_lt, gammaTail_lt, deltaTail_lt⟩

end
end Pr6453

theorem solution :
    Pr6453.alpha2 < 1 - (Pr6453.reserve : ℝ) ∧
      Pr6453.gammaTail2 < (Pr6453.decay : ℝ) ∧
      Pr6453.deltaTail2 < (Pr6453.decay : ℝ) :=
  Pr6453.tail_ratios
