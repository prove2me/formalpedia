-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.apra_blow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:35:09.684739+00:00
-- url     : https://prove2.me/submissions/fbc746f1-2cb7-44eb-98a1-613a66650e2b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apraW_meas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apraW_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) :
    ⨆ n : ℕ, ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
  have : Nontrivial (V d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  set f : ℕ → V d → ℝ≥0∞ := fun n x => apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ with hf
  have hmeas : ∀ n, Measurable (f n) := fun n => (apraW_meas _ _ _).comp measurable_norm
  have hmono : Monotone f := by
    intro m n hmn x
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    show apraW d ε (1 / ((m : ℝ) + 1)) ‖x‖ ≤ apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖
    exact apraW_anti d ε h2 h1 _
  rw [← lintegral_iSup hmeas hmono]
  set g : V d → ℝ≥0∞ := fun x => ENNReal.ofReal ‖x‖ ^ (-2 * (d : ℝ)) with hg
  have hpt : ∀ x : V d, x ≠ 0 → (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    intro x hx0
    by_cases hx : ‖x‖ < ε
    · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hx)]
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (pow_pos hpos 2)
      refine le_trans ?_ (le_iSup _ n)
      simp only [hf, hg, apraW, if_pos hx]
      rw [max_eq_left hn.le, ENNReal.ofReal_rpow_of_pos hpos, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le]
      apply le_of_eq
      congr 2
      push_cast
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (mem_ball_zero_iff.mp h))]
      exact bot_le
  have hae : ∀ᵐ x ∂(volume : Measure (V d)), (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    have h0 : ∀ᵐ x ∂(volume : Measure (V d)), x ∉ ({0} : Set (V d)) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with x hx using hpt x (by simpa using hx)
  have hT : ∫⁻ y in ball (0 : V d) 1, g y = ⊤ :=
    not_lt_top_iff.mp (fun h => lt_irrefl _ ((hMVI hd d).1 h))
  have hdn : -2 * (d : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpt2 : ∀ y : V d, g y ≤ (ball (0 : V d) ε).indicator g y + ENNReal.ofReal ε ^ (-2 * (d : ℝ)) := by
    intro y
    by_cases hy : y ∈ ball (0 : V d) ε
    · rw [Set.indicator_of_mem hy]
      exact le_self_add
    · rw [Set.indicator_of_notMem hy, zero_add]
      have : ε ≤ ‖y‖ := by simpa [mem_ball_zero_iff] using hy
      simp only [hg]
      rw [ENNReal.ofReal_rpow_of_pos (hε.trans_le this), ENNReal.ofReal_rpow_of_pos hε]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hε this hdn)
  have hc : ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [ENNReal.rpow_eq_top_iff, hε]) measure_ball_lt_top.ne
  have hle : ∫⁻ y in ball (0 : V d) 1, g y ≤ (∫⁻ y, (ball (0 : V d) ε).indicator g y) +
      ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
    calc ∫⁻ y in ball (0 : V d) 1, g y
        ≤ ∫⁻ y in ball (0 : V d) 1, ((ball (0 : V d) ε).indicator g y +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ))) := lintegral_mono fun y => hpt2 y
      _ = (∫⁻ y in ball (0 : V d) 1, (ball (0 : V d) ε).indicator g y) +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ _ := add_le_add (setLIntegral_le_lintegral _ _) le_rfl
  have hind : ∫⁻ y, (ball (0 : V d) ε).indicator g y = ⊤ := by
    by_contra hne
    exact (ENNReal.add_ne_top.2 ⟨hne, hc⟩) (eq_top_iff.2 (hT ▸ hle))
  exact eq_top_iff.2 (hind ▸ lintegral_mono_ae hae)
end ReciprocityTheory.L2DbarEstimates.Y
