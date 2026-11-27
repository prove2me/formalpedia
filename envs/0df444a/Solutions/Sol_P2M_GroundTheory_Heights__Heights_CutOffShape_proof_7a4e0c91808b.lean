-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffShape_proof_7a4e0c91808b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:39.113234+00:00
-- url     : https://prove2.me/submissions/344f9ef2-d37d-4b27-8228-06f8d91340c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffShape
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology
open scoped ContDiff
noncomputable section
private theorem cutStep_small (k : ℕ) {w : ℝ} (h0 : w ≠ 0) (hw : |w| < cutLevel k) :
    cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : Real.log w < -Real.exp ((k : ℝ) + 1) := by
    rw [← Real.log_abs, ← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (abs_pos.2 h0) hw
  have h2 : (k : ℝ) + 1 < Real.log (-Real.log w) := by
    rw [← Real.log_exp ((k : ℝ) + 1)]
    exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  have h3 : 1 < Real.log (-Real.log w) / ((k : ℝ) + 1) := (one_lt_div hk).2 h2
  exact Real.smoothTransition.zero_of_nonpos (by linarith)
private theorem cutStep_large (k : ℕ) {w : ℝ} (hw : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < w)
    (h1 : w < 1) : cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw0 : 0 < w := (Real.exp_pos _).trans hw
  have hl : -Real.exp (((k : ℝ) + 1) / 2) < Real.log w := by
    rw [← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (Real.exp_pos _) hw
  have hneg : 0 < -Real.log w := neg_pos.2 (Real.log_neg hw0 h1)
  have h2 : Real.log (-Real.log w) < ((k : ℝ) + 1) / 2 := by
    rw [← Real.log_exp (((k : ℝ) + 1) / 2)]
    exact Real.log_lt_log hneg (by linarith)
  have h3 : Real.log (-Real.log w) / ((k : ℝ) + 1) < 1 / 2 := by
    rw [div_lt_iff₀ hk]; linarith
  exact Real.smoothTransition.one_of_one_le (by linarith)
private theorem cutProfile_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ∞ (cutProfile k) (Set.Ioi (-cutLevel k)) := by
  obtain ⟨hc0, hc1⟩ := cutLevel_mem k
  set c' := Real.exp (-Real.exp (((k : ℝ) + 1) / 2))
  have hc'1 : c' < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))
  refine (isOpen_Ioi.contDiffOn_iff).2 fun x hx => ?_
  rcases lt_or_ge x (cutLevel k) with hxc | hxc
  ·
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (Set.mem_Ioi.1 hx) hxc] with w hw
    have hwa : |w| < cutLevel k := abs_lt.2 hw
    unfold cutProfile
    split_ifs with h0 h1
    · rfl
    · exact absurd (h1.trans_lt (hw.2.trans hc1)) (lt_irrefl _)
    · exact cutStep_small k h0 hwa
  rcases lt_or_ge c' x with hxc' | hxc'
  ·
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxc'] with w hw
    have hw0 : 0 < w := (Real.exp_pos _).trans hw
    unfold cutProfile
    split_ifs with h0 h1
    · exact absurd h0 hw0.ne'
    · rfl
    · exact cutStep_large k hw (not_le.1 h1)
  ·
    have hx0 : 0 < x := hc0.trans_le hxc
    have hx1 : x < 1 := hxc'.trans_lt hc'1
    have hform : ContDiffAt ℝ ∞ (fun w => cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))) x := by
      have hlog : ContDiffAt ℝ ∞ (fun w => Real.log (-Real.log w)) x :=
        ((Real.contDiffAt_log.2 hx0.ne').neg).log (neg_ne_zero.2 (Real.log_neg hx0 hx1).ne)
      exact Real.smoothTransition.contDiffAt.comp x
        (contDiffAt_const.sub (contDiffAt_const.mul (hlog.div_const _)))
    refine hform.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx0 hx1] with w hw
    simp [cutProfile, hw.1.ne', not_le.2 hw.2]
end
end GroundTheory.Heights₂.Heights
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CutOffShape
theorem _root_.solution : CutOffShape.Statement := by
  intro m Q
  have hF : ∀ k, logLogCut Q k = cutProfile k ∘ fun y => ‖eval y Q‖ ^ 2 := fun k => rfl
  have hstep : ∀ t, cutStep t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨fun k => ⟨?_, fun y => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · rw [hF]
    have hw : ContDiff ℝ ∞ fun y : Fin m → ℂ => ‖eval y Q‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp
        (((AnalyticOnNhd.eval_mvPolynomial Q).contDiff (n := ∞)).restrict_scalars ℝ)
    exact (cutProfile_contDiffOn k).comp_contDiff hw fun y =>
      (neg_neg_of_pos (cutLevel_mem k).1).trans_le (by positivity)
  · unfold logLogCut; split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hstep _
  · have h1 := (cutLevel_mem k).2
    unfold logLogCut logAbsSq; split_ifs with h0 h1'
    · rfl
    · exact absurd (h1'.trans_lt (hy.trans h1)) (lt_irrefl _)
    · exact cutStep_small k h0 (by rwa [abs_of_nonneg (by positivity)])
  · have hw0 : ‖eval y Q‖ ^ 2 ≠ 0 := by positivity
    by_cases hw1 : 1 ≤ ‖eval y Q‖ ^ 2
    · simp [logLogCut, hw0, hw1]
    refine tendsto_const_nhds.congr' ?_
    set L := Real.log (-Real.log (‖eval y Q‖ ^ 2))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * |L|)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : L / ((k : ℝ) + 1) < 1 / 2 := by
      rw [div_lt_iff₀ hk']; linarith [le_abs_self L]
    simp only [logLogCut, logAbsSq, hw0, hw1, if_false]
    exact (Real.smoothTransition.one_of_one_le (by linarith)).symm
end CutOffShape
end GroundTheory.Heights₂.Heights
