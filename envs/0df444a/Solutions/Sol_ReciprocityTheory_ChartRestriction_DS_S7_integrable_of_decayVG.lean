-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.integrable_of_decayVG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:42.439578+00:00
-- url     : https://prove2.me/submissions/952506b6-9253-4186-bb40-6854ae71f8b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_volGrowthVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ballFiniteVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_continuous_toM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_contVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_oneVG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] (ε : Fin n → Bool) (s : Bool)
    (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (f : UJ ε → E) (hf : AEStronglyMeasurable f ν) (M : ℝ)
    (hM : ∀ g, hs (toM g) ≤ (n : ℝ) * Real.exp 2 + 1 → ‖f g‖ ≤ M) (a : ℝ)
    (ha : ((2 * (n * Fintype.card (SgIxV ε s)) : ℕ) : ℝ) < a)
    (hdec : ∀ g, (n : ℝ) * Real.exp 2 + 1 < hs (toM g) →
      ∃ t : ℝ, hs (toM g) ≤ n * Real.exp (2 * t) ∧ ‖f g‖ ≤ M * Real.exp (-(a * t))) :
    Integrable f ν := by
  obtain ⟨C, hC0, hC⟩ := volGrowthVG ε s ν
  set N : ℕ := 2 * (n * Fintype.card (SgIxV ε s)) with hN
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg N) ha
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hM0 : 0 ≤ M := by
    refine (norm_nonneg _).trans (hM 1 ?_)
    have e1 : hs (toM (1 : UJ ε)) = n := hs_oneVG n
    have e2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    rw [e1]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let A0 : ℝ := Real.exp (a * Real.log n / 2)
  let y : ℝ := Real.exp (-(a * Real.log 2))
  let r : ℝ := 2 ^ N * y
  have hy0 : 0 < y := Real.exp_pos _
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have e : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    show 2 ^ N * Real.exp (-(a * Real.log 2)) < 1
    rw [e, ← Real.exp_add, Real.exp_lt_one_iff]
    nlinarith
  let B0 : Set (UJ ε) := {g | hs (toM g) ≤ (n : ℝ) * Real.exp 2 + 1}
  let S : ℕ → Set (UJ ε) := fun j => {g | hs (toM g) ≤ ((2 : ℝ) ^ j) ^ 2}
  have hcont : Continuous (fun g : UJ ε => hs (toM g)) := hs_contVG.comp (continuous_toM ε)
  have hB0m : MeasurableSet B0 := (isClosed_le hcont continuous_const).measurableSet
  have hSm : ∀ j, MeasurableSet (S j) := fun j => (isClosed_le hcont continuous_const).measurableSet
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (M * (A0 * y ^ j))
  let F : UJ ε → ℝ≥0∞ := fun g =>
    B0.indicator (fun _ => ENNReal.ofReal M) g + ∑' j, (S (j + 1)).indicator (fun _ => c j) g
  have hpt : ∀ g, ‖f g‖ₑ ≤ F g := by
    intro g
    by_cases hg : g ∈ B0
    · calc ‖f g‖ₑ ≤ ENNReal.ofReal M := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM g hg)
        _ = B0.indicator (fun _ => ENNReal.ofReal M) g :=
            (Set.indicator_of_mem hg (fun _ => ENNReal.ofReal M)).symm
        _ ≤ F g := le_self_add
    · have hg' : (n : ℝ) * Real.exp 2 + 1 < hs (toM g) := not_le.1 hg
      obtain ⟨t, ht1, ht2⟩ := hdec g hg'
      have hpos : (1 : ℝ) ≤ hs (toM g) := by
        have : 0 ≤ (n : ℝ) * Real.exp 2 := by positivity
        linarith
      obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hpos (show (1 : ℝ) < 4 by norm_num)
      have hn0 : (0 : ℝ) < n := by
        by_contra hcon
        have : (n : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg n)
        rw [this, zero_mul] at ht1
        linarith
      have hmem : g ∈ S (j + 1) := by
        show hs (toM g) ≤ ((2 : ℝ) ^ (j + 1)) ^ 2
        have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 ^ (j + 1) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]; exact hj2.le
      have hlog : (j : ℝ) * Real.log 2 - Real.log n / 2 ≤ t := by
        have h4 : (4 : ℝ) ^ j ≤ n * Real.exp (2 * t) := hj1.trans ht1
        have h5 := Real.log_le_log (by positivity) h4
        rw [Real.log_pow, Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at h5
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [h6] at h5
        linarith
      have hexp : Real.exp (-(a * t)) ≤ A0 * y ^ j := by
        show Real.exp (-(a * t)) ≤ Real.exp (a * Real.log n / 2) * Real.exp (-(a * Real.log 2)) ^ j
        rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
        nlinarith
      have hb : ‖f g‖ ≤ M * (A0 * y ^ j) := ht2.trans (mul_le_mul_of_nonneg_left hexp hM0)
      calc ‖f g‖ₑ ≤ c j := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hb
        _ = (S (j + 1)).indicator (fun _ => c j) g := (Set.indicator_of_mem hmem (fun _ => c j)).symm
        _ ≤ ∑' j, (S (j + 1)).indicator (fun _ => c j) g :=
            ENNReal.le_tsum (f := fun j => (S (j + 1)).indicator (fun _ => c j) g) j
        _ ≤ F g := le_add_self
  have hterm : ∀ j, c j * ν (S (j + 1)) ≤ ENNReal.ofReal (M * A0 * C * 2 ^ N * r ^ j) := by
    intro j
    have h2 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    calc c j * ν (S (j + 1)) ≤ c j * ENNReal.ofReal (C * (2 ^ (j + 1)) ^ N) := by
          gcongr
          exact hC _ h2
      _ = ENNReal.ofReal (M * (A0 * y ^ j) * (C * (2 ^ (j + 1)) ^ N)) :=
          (ENNReal.ofReal_mul (mul_nonneg hM0 (by positivity))).symm
      _ = ENNReal.ofReal (M * A0 * C * 2 ^ N * r ^ j) := by
          congr 1
          show M * (A0 * y ^ j) * (C * (2 ^ (j + 1)) ^ N) = M * A0 * C * 2 ^ N * (2 ^ N * y) ^ j
          rw [mul_pow]
          ring
  have hFint : ∫⁻ g, F g ∂ν < ⊤ := by
    have e1 : ∫⁻ g, F g ∂ν = ENNReal.ofReal M * ν B0 + ∑' j, c j * ν (S (j + 1)) := by
      show ∫⁻ g, (B0.indicator (fun _ => ENNReal.ofReal M) g +
        ∑' j, (S (j + 1)).indicator (fun _ => c j) g) ∂ν = _
      rw [lintegral_add_left (measurable_const.indicator hB0m), lintegral_indicator_const hB0m,
        lintegral_tsum (fun j => (measurable_const.indicator (hSm (j + 1))).aemeasurable)]
      congr 1
      exact tsum_congr fun j => lintegral_indicator_const (hSm (j + 1)) _
    rw [e1]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballFiniteVG ε ν _), ?_⟩
    have hsum : Summable fun j : ℕ => M * A0 * C * 2 ^ N * r ^ j :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    calc ∑' j, c j * ν (S (j + 1)) ≤ ∑' j, ENNReal.ofReal (M * A0 * C * 2 ^ N * r ^ j) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' j, M * A0 * C * 2 ^ N * r ^ j) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => by
            have := mul_nonneg hM0 (by positivity : (0 : ℝ) ≤ A0 * C * 2 ^ N * r ^ j)
            simpa only [mul_assoc] using this) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨hf, lt_of_le_of_lt (lintegral_mono hpt) hFint⟩
end ReciprocityTheory.ChartRestriction.DS.S7
