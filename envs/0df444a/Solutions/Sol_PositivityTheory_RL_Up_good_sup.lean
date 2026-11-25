-- Prove2me | solution 1 for PositivityTheory.RL.Up.good_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:11.982389+00:00
-- url     : https://prove2.me/submissions/7e4c797f-3a6f-42b7-8716-acc43b69b8e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
import Theorems.Thm_PositivityTheory_RL_Up_bdd_of_weak
import Theorems.Thm_PositivityTheory_RL_Up_taylor2
import Theorems.Thm_PositivityTheory_RL_Up_norm_le_of_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
omit [DecidableEq l]
namespace PositivityTheory.RL.Up
theorem _root_.solution (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1)
    (hm : ∀ s t, U (s + t) = U s * U t)
    (h1 : ∀ f, HasDerivAt (fun t => (U t f).toLp 2 volume) ((Q f).toLp 2 volume) 0)
    (hL : ∀ s, ∃ L : L2 l →L[ℂ] L2 l, ∀ f, (U s f).toLp 2 volume = L (f.toLp 2 volume))
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun t => T (U t f)) :
    Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ) := by
  intro f
  have hd : ∀ g s, HasDerivAt (fun t => (U t g).toLp 2 volume) ((U s (Q g)).toLp 2 volume) s := fun g s => by
    obtain ⟨L, hL⟩ := hL s
    have a : HasDerivAt (fun t => (U (t - s) g).toLp 2 volume) ((Q g).toLp 2 volume) s := by
      have := h1 g
      rw [← sub_self s] at this
      exact this.comp_sub_const s s
    have b := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s a
    rw [hL]
    refine b.congr_of_eventuallyEq (.of_forall fun t => ?_)
    show _ = L _
    rw [← hL, ← ContinuousLinearMap.mul_apply, ← hm, add_sub_cancel]
  obtain ⟨M, hM⟩ := bdd_of_weak (fun t => toBoundedContinuousFunctionCLM ℂ _ ℂ (U t (Q (Q f))))
    fun φ => hw (φ ∘L toBoundedContinuousFunctionCLM ℂ _ ℂ) _
  have key : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖toBoundedContinuousFunctionCLM ℂ _ ℂ (U t f - f - (t : ℂ) • Q f)‖ ≤ M * t ^ 2 := fun t ht => by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    refine norm_le_of_avg volume (U t f - f - (t : ℂ) • Q f : Sch l) (SchwartzMap.continuous _) x fun r hr => ?_
    set s := Metric.closedBall x r
    have hfin : volume s < ⊤ := (isCompact_closedBall x _).measure_lt_top
    let u : L2 l := indicatorConstLp 2 (measurableSet_closedBall (x := x) (ε := r)) hfin.ne (1 : ℂ)
    have hu : ∀ g : Sch l, innerSL ℂ u (g.toLp 2 volume) = ∫ y in s, g y := fun g => by
      rw [innerSL_apply_apply, L2.inner_indicatorConstLp_one]
      exact setIntegral_congr_ae measurableSet_closedBall ((g.coeFn_toLp 2 volume).mono fun y hy _ => hy)
    have hd' : ∀ g s, HasDerivAt (fun t => innerSL ℂ u ((U t g).toLp 2 volume))
        (innerSL ℂ u ((U s (Q g)).toLp 2 volume)) s := fun g s =>
      ((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd g s)
    have := taylor2 _ _ _ (hd' f) (hd' (Q f)) (M := M * volume.real s) (fun v hv => by
      rw [hu]
      exact norm_setIntegral_le_of_norm_le_const hfin fun y _ =>
        (BoundedContinuousFunction.norm_coe_le_norm (toBoundedContinuousFunctionCLM ℂ _ ℂ (U v (Q (Q f)))) y).trans
          (hM v hv)) ht
    rw [← hu]
    simp only [h0, ContinuousLinearMap.one_apply] at this
    rw [← toLpCLM_apply (𝕜 := ℂ), map_sub, map_sub, map_smul, map_sub, map_sub, map_smul]
    simp only [toLpCLM_apply, smul_eq_mul]
    linarith
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun t : ℝ => t ^ 2) (IsBigO.of_bound M ?_) (isLittleO_pow_id (by norm_num))
  filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
  have := key t ht
  simp only [map_sub, map_smul] at this
  simpa [h0, ← Complex.coe_smul] using this
end PositivityTheory.RL.Up
