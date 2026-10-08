-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyholeBoundaryPath_piecewise_C1_actual
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-19T22:38:11.628975+00:00
-- url     : https://prove2.me/submissions/a5af255b-cfa9-4eb0-ab3a-3ba85ab321d0

import Mathlib
import Definitions.Def_keyholeBoundaryPath
import Definitions.Def_keyholeUpperBank
import Definitions.Def_keyholeLowerBank
import Definitions.Def_keyholeInnerArc
import Definitions.Def_keyholeOuterArc
open scoped Interval

theorem solution
    (a₀ a₁ r R : ℝ) :
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo 0 (1 / 4)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 4) (1 / 2)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 2) (3 / 4)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (3 / 4) 1) := by
  have hprim :
      ContDiff ℝ 1 (fun t : ℝ => keyholeUpperBank (a₀ + 4 * t * (a₁ - a₀))) ∧
      ContDiff ℝ 1 (fun t : ℝ => keyholeLowerBank (a₁ + (4 * t - 2) * (a₀ - a₁))) ∧
      ContDiff ℝ 1 (fun t : ℝ => keyholeOuterArc R (4 * t - 1)) ∧
      ContDiff ℝ 1 (fun t : ℝ => keyholeInnerArc r (4 * t - 3)) := by
    unfold keyholeUpperBank keyholeLowerBank keyholeOuterArc keyholeInnerArc
    have hreal1 : ContDiff ℝ 1 (fun t : ℝ => a₀ + 4 * t * (a₁ - a₀)) := by fun_prop
    have hreal2 : ContDiff ℝ 1 (fun t : ℝ => a₁ + (4 * t - 2) * (a₀ - a₁)) := by fun_prop
    have hreal3 : ContDiff ℝ 1 (fun t : ℝ => 4 * t - 1) := by fun_prop
    have hreal4 : ContDiff ℝ 1 (fun t : ℝ => 4 * t - 3) := by fun_prop
    have hc1 : ContDiff ℝ 1 (fun t : ℝ => ((a₀ + 4 * t * (a₁ - a₀) : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal1
    have hc2 : ContDiff ℝ 1 (fun t : ℝ => ((a₁ + (4 * t - 2) * (a₀ - a₁) : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal2
    have hc3 : ContDiff ℝ 1 (fun t : ℝ => ((4 * t - 1 : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal3
    have hc4 : ContDiff ℝ 1 (fun t : ℝ => ((4 * t - 3 : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal4
    constructor
    · simpa [zero_mul, add_zero] using hc1
    constructor
    · simpa [zero_mul, sub_zero] using hc2
    constructor
    · have harg : ContDiff ℝ 1 (fun t : ℝ => Complex.I * (((4 * t - 1 : ℝ) : ℂ) * (Real.pi : ℂ))) := by fun_prop
      have hexp : ContDiff ℝ 1 (fun t : ℝ => Complex.exp (Complex.I * (((4 * t - 1 : ℝ) : ℂ) * (Real.pi : ℂ)))) := Complex.contDiff_exp.comp harg
      simpa [mul_assoc, mul_comm, mul_left_comm] using ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (R : ℂ))).mul hexp)
    · have harg : ContDiff ℝ 1 (fun t : ℝ => Complex.I * (((4 * t - 3 : ℝ) : ℂ) * (Real.pi : ℂ))) := by fun_prop
      have hexp : ContDiff ℝ 1 (fun t : ℝ => Complex.exp (Complex.I * (((4 * t - 3 : ℝ) : ℂ) * (Real.pi : ℂ)))) := Complex.contDiff_exp.comp harg
      simpa [mul_assoc, mul_comm, mul_left_comm] using ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (r : ℂ))).mul hexp)
  constructor
  · intro x hx
    have hbranch : ContDiffAt ℝ 1 (fun t : ℝ => keyholeUpperBank (a₀ + 4 * t * (a₁ - a₀))) x := hprim.1.contDiffAt
    apply hbranch.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hlt : ¬ (4⁻¹ : ℝ) ≤ t := by norm_num; linarith [ht.2]
      have ht1 : t < (1 / 4 : ℝ) := by linarith [ht.2]
      have ht1' : t < (4⁻¹ : ℝ) := by norm_num; linarith [ht1]
      simp_all [keyholeBoundaryPath]
    · have hltx : ¬ (4⁻¹ : ℝ) ≤ x := by norm_num; linarith [hx.2]
      change (if x < 1 / 4 then keyholeUpperBank (a₀ + 4 * x * (a₁ - a₀)) else if x < 1 / 2 then keyholeOuterArc R (4 * x - 1) else if x < 3 / 4 then keyholeLowerBank (a₁ + (4 * x - 2) * (a₀ - a₁)) else keyholeInnerArc r (4 * x - 3)) = keyholeUpperBank (a₀ + 4 * x * (a₁ - a₀))
      simp_all [keyholeBoundaryPath]
  constructor
  · intro x hx
    have hbranch : ContDiffAt ℝ 1 (fun t : ℝ => keyholeOuterArc R (4 * t - 1)) x := hprim.2.2.1.contDiffAt
    apply hbranch.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hge : (4⁻¹ : ℝ) ≤ t := by norm_num; linarith [ht.1]
      have hlt : ¬ (2⁻¹ : ℝ) ≤ t := by norm_num; linarith [ht.2]
      have ht1 : ¬ t < (1 / 4 : ℝ) := by linarith [hge]
      have ht2 : t < (1 / 2 : ℝ) := by linarith [hlt]
      have ht1' : ¬ t < (4⁻¹ : ℝ) := not_lt_of_ge hge
      have ht2' : t < (2⁻¹ : ℝ) := lt_of_not_ge hlt
      simp_all [keyholeBoundaryPath]
    · have hgex : (4⁻¹ : ℝ) ≤ x := by norm_num; linarith [hx.1]
      have hltx : ¬ (2⁻¹ : ℝ) ≤ x := by norm_num; linarith [hx.2]
      have hn₁ : ¬ x < (4⁻¹ : ℝ) := not_lt_of_ge hgex
      have hn₂ : x < (2⁻¹ : ℝ) := lt_of_not_ge hltx
      have hn₁' : ¬ x < (1 / 4 : ℝ) := by linarith [hx.1]
      have hn₂' : x < (1 / 2 : ℝ) := hx.2
      change (if x < 1 / 4 then keyholeUpperBank (a₀ + 4 * x * (a₁ - a₀))
        else if x < 1 / 2 then keyholeOuterArc R (4 * x - 1)
        else if x < 3 / 4 then keyholeLowerBank (a₁ + (4 * x - 2) * (a₀ - a₁))
        else keyholeInnerArc r (4 * x - 3)) = keyholeOuterArc R (4 * x - 1)
      simp_all [keyholeBoundaryPath]
  constructor
  · intro x hx
    have hbranch : ContDiffAt ℝ 1 (fun t : ℝ => keyholeLowerBank (a₁ + (4 * t - 2) * (a₀ - a₁))) x := hprim.2.1.contDiffAt
    apply hbranch.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hge₁ : (4⁻¹ : ℝ) ≤ t := by norm_num; linarith [show (1 / 2 : ℝ) < t from ht.1]
      have hge₂ : (2⁻¹ : ℝ) ≤ t := by norm_num; linarith [ht.1]
      have hlt : ¬ (3 / 4 : ℝ) ≤ t := by linarith [ht.2]
      have ht1 : ¬ t < (1 / 4 : ℝ) := by linarith [hge₁]
      have ht2 : ¬ t < (1 / 2 : ℝ) := by linarith [hge₂]
      have ht3 : t < (3 / 4 : ℝ) := lt_of_not_ge hlt
      have ht1' : ¬ t < (4⁻¹ : ℝ) := not_lt_of_ge hge₁
      have ht2' : ¬ t < (2⁻¹ : ℝ) := not_lt_of_ge hge₂
      have hnot1 : ¬ t < (4⁻¹ : ℝ) := not_lt_of_ge hge₁
      have hnot2 : ¬ t < (2⁻¹ : ℝ) := not_lt_of_ge hge₂
      simp [keyholeBoundaryPath, hnot1, hnot2, ht3]
    · have hge₁x : (4⁻¹ : ℝ) ≤ x := by norm_num; linarith [show (1 / 2 : ℝ) < x from hx.1]
      have hge₂x : (2⁻¹ : ℝ) ≤ x := by norm_num; linarith [hx.1]
      have hltx : ¬ (3 / 4 : ℝ) ≤ x := by linarith [hx.2]
      have hn₁ : ¬ x < (4⁻¹ : ℝ) := not_lt_of_ge hge₁x
      have hn₂ : ¬ x < (2⁻¹ : ℝ) := not_lt_of_ge hge₂x
      have hn₃ : x < (3 / 4 : ℝ) := lt_of_not_ge hltx
      have hn₁' : ¬ x < (1 / 4 : ℝ) := by linarith [hx.1]
      have hn₂' : ¬ x < (1 / 2 : ℝ) := by linarith [hx.1]
      change (if x < 1 / 4 then keyholeUpperBank (a₀ + 4 * x * (a₁ - a₀))
        else if x < 1 / 2 then keyholeOuterArc R (4 * x - 1)
        else if x < 3 / 4 then keyholeLowerBank (a₁ + (4 * x - 2) * (a₀ - a₁))
        else keyholeInnerArc r (4 * x - 3)) = keyholeLowerBank (a₁ + (4 * x - 2) * (a₀ - a₁))
      simp only [if_neg hn₁', if_neg hn₂', if_pos hn₃]
  · intro x hx
    have hbranch : ContDiffAt ℝ 1 (fun t : ℝ => keyholeInnerArc r (4 * t - 3)) x := hprim.2.2.2.contDiffAt
    apply hbranch.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hge₁ : (4⁻¹ : ℝ) ≤ t := by norm_num; linarith [show (3 / 4 : ℝ) < t from ht.1]
      have hge₂ : (2⁻¹ : ℝ) ≤ t := by norm_num; linarith [show (3 / 4 : ℝ) < t from ht.1]
      have hge₃ : (3 / 4 : ℝ) ≤ t := by linarith [ht.1]
      have ht1 : ¬ t < (1 / 4 : ℝ) := by linarith [hge₁]
      have ht2 : ¬ t < (1 / 2 : ℝ) := by linarith [hge₂]
      have ht3 : ¬ t < (3 / 4 : ℝ) := by linarith [hge₃]
      have ht1' : ¬ t < (4⁻¹ : ℝ) := not_lt_of_ge hge₁
      have ht2' : ¬ t < (2⁻¹ : ℝ) := not_lt_of_ge hge₂
      have ht3' : ¬ t < (3 / 4 : ℝ) := not_lt_of_ge hge₃
      have hnot1 : ¬ t < (4⁻¹ : ℝ) := not_lt_of_ge hge₁
      have hnot2 : ¬ t < (2⁻¹ : ℝ) := not_lt_of_ge hge₂
      have hnot3 : ¬ t < (3 / 4 : ℝ) := not_lt_of_ge hge₃
      simp [keyholeBoundaryPath, hnot1, hnot2, hnot3]
    · have hge₁x : (4⁻¹ : ℝ) ≤ x := by norm_num; linarith [show (3 / 4 : ℝ) < x from hx.1]
      have hge₂x : (2⁻¹ : ℝ) ≤ x := by norm_num; linarith [show (3 / 4 : ℝ) < x from hx.1]
      have hge₃x : (3 / 4 : ℝ) ≤ x := by linarith [hx.1]
      have hn₁ : ¬ x < (4⁻¹ : ℝ) := not_lt_of_ge hge₁x
      have hn₂ : ¬ x < (2⁻¹ : ℝ) := not_lt_of_ge hge₂x
      have hn₃ : ¬ x < (3 / 4 : ℝ) := not_lt_of_ge hge₃x
      have hn₁' : ¬ x < (1 / 4 : ℝ) := by linarith [hx.1]
      have hn₂' : ¬ x < (1 / 2 : ℝ) := by linarith [hx.1]
      have hn₃' : ¬ x < (3 / 4 : ℝ) := by linarith [hx.1]
      change (if x < 1 / 4 then keyholeUpperBank (a₀ + 4 * x * (a₁ - a₀))
        else if x < 1 / 2 then keyholeOuterArc R (4 * x - 1)
        else if x < 3 / 4 then keyholeLowerBank (a₁ + (4 * x - 2) * (a₀ - a₁))
        else keyholeInnerArc r (4 * x - 3)) = keyholeInnerArc r (4 * x - 3)
      simp only [if_neg hn₁', if_neg hn₂', if_neg hn₃']
