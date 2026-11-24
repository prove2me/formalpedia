-- Prove2me | solution 1 for ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:02.296182+00:00
-- url     : https://prove2.me/submissions/adacef6b-6c11-467b-9c68-e7f1d14201f6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm
open MeasureTheory Metric Filter Topology
open MeasureTheory Metric Filter Topology
private theorem analyticAt_cons_right {D : ℕ} (t : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun v : Fin D → ℂ => (Fin.cons t v : Fin (D + 1) → ℂ)) w := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact analyticAt_const
  · simp only [Fin.cons_succ]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) j).analyticAt w
private theorem analyticAt_cons_left {D : ℕ} (t : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (Fin.cons s w : Fin (D + 1) → ℂ)) t := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact analyticAt_id
  · simp only [Fin.cons_succ]
    exact analyticAt_const
private theorem cons_mem_ball {D : ℕ} {c : Fin (D + 1) → ℂ} {r : ℝ} (hr : 0 < r) (t : ℂ)
    (w : Fin D → ℂ) :
    (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ↔ t ∈ ball (c 0) r ∧ w ∈ ball (Fin.tail c) r := by
  simp only [ball_pi _ hr, Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.tail]
private theorem measurableSet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) : MeasurableSet {z | z ∈ U ∧ f z = 0} := by
  have h1 : IsOpen (U ∩ f ⁻¹' {0}ᶜ) :=
    hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have h2 : {z | z ∈ U ∧ f z = 0} = U \ (U ∩ f ⁻¹' {0}ᶜ) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    tauto
  rw [h2]
  exact hU.measurableSet.diff h1.measurableSet
private theorem nz_one {U : Set ℂ} (hc : IsPreconnected U) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hne : ∃ z ∈ U, g z ≠ 0) : volume {z | z ∈ U ∧ g z = 0} = 0 := by
  apply measure_null_of_locally_null
  rintro z ⟨hzU, -⟩
  rcases (hg z hzU).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨w, hwU, hgw⟩ := hne
    exact hgw (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU h hwU)
  · refine ⟨{z}, ?_, measure_singleton z⟩
    rw [mem_nhdsWithin_iff_eventually]
    rw [eventually_nhdsWithin_iff] at h
    filter_upwards [h] with x hx hxZ
    by_contra hxz
    exact hx hxz hxZ.2
private theorem nz_ball : ∀ (D : ℕ) (c : Fin D → ℂ) (r : ℝ) (f : (Fin D → ℂ) → ℂ),
    AnalyticOnNhd ℂ f (ball c r) → (∃ z ∈ ball c r, f z ≠ 0) →
    volume {z | z ∈ ball c r ∧ f z = 0} = 0 := by
  intro D
  induction D with
  | zero =>
    intro c r f _ hne
    obtain ⟨z₀, _, hz₀⟩ := hne
    have h1 : {z | z ∈ ball c r ∧ f z = 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hz
      exact hz₀ (Subsingleton.elim z z₀ ▸ hz)
    rw [h1, measure_empty]
  | succ D ih =>
    intro c r f hf hne
    obtain ⟨z₀, hz₀b, hz₀⟩ := hne
    have hr : 0 < r := pos_of_mem_ball hz₀b
    have hZm : MeasurableSet {z | z ∈ ball c r ∧ f z = 0} := measurableSet_zero isOpen_ball hf
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    have h1 := (MeasurePreserving.symm e he).measure_preimage hZm.nullMeasurableSet
    rw [← h1, Measure.volume_eq_prod, Measure.prod_apply_symm (e.symm.measurable hZm)]
    have hslice : ∀ w : Fin D → ℂ, (fun t => (t, w)) ⁻¹' (e.symm ⁻¹' {z | z ∈ ball c r ∧ f z = 0}) =
        {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} := by
      intro w
      ext t
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    simp_rw [hslice]
    set t₀ := z₀ 0 with ht₀_def
    have hz₀' : (Fin.cons t₀ (Fin.tail z₀) : Fin (D + 1) → ℂ) = z₀ := Fin.cons_self_tail z₀
    have hmem₀ := (cons_mem_ball hr t₀ (Fin.tail z₀)).1 (by rw [hz₀']; exact hz₀b)
    have hf' : AnalyticOnNhd ℂ (fun w => f (Fin.cons t₀ w)) (ball (Fin.tail c) r) := fun w hw =>
      (hf _ ((cons_mem_ball hr t₀ w).2 ⟨hmem₀.1, hw⟩)).comp (analyticAt_cons_right t₀ w)
    have hW0 := ih (Fin.tail c) r _ hf' ⟨Fin.tail z₀, hmem₀.2, by simpa [hz₀'] using hz₀⟩
    have hae : ∀ᵐ w ∂(volume : Measure (Fin D → ℂ)),
        volume {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hW0] with w hw
      by_cases hwb : w ∈ ball (Fin.tail c) r
      · have hw' : f (Fin.cons t₀ w) ≠ 0 := fun h0 => hw ⟨hwb, h0⟩
        have hg : AnalyticOnNhd ℂ (fun t => f (Fin.cons t w)) (ball (c 0) r) := fun t ht =>
          AnalyticAt.comp (g := f) (f := fun s => (Fin.cons s w : Fin (D + 1) → ℂ))
            (hf _ ((cons_mem_ball hr t w).2 ⟨ht, hwb⟩)) (analyticAt_cons_left t w)
        have h2 := nz_one (convex_ball (c 0) r).isPreconnected hg ⟨t₀, hmem₀.1, hw'⟩
        have hset : {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} =
            {t | t ∈ ball (c 0) r ∧ f (Fin.cons t w) = 0} := by
          ext t
          simp only [Set.mem_ofPred_eq, cons_mem_ball hr, hwb, and_true]
        rw [hset]
        exact h2
      · have hset : {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} = ∅ := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, cons_mem_ball hr]
          tauto
        rw [hset, measure_empty]
    rw [lintegral_congr_ae hae, lintegral_zero]
end ReciprocityTheory.AnForm
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Metric Filter Topology
open MeasureTheory Metric Filter Topology
namespace ReciprocityTheory.AnForm
theorem _root_.solution {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hc : IsPreconnected U) {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) :
    volume {z | z ∈ U ∧ f z = 0} = 0 := by
  apply measure_null_of_locally_null
  rintro z ⟨hzU, -⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
  refine ⟨{x | x ∈ ball z ε ∧ f x = 0}, ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [ball_mem_nhds z hε] with x hx hxZ using ⟨hx, hxZ.2⟩
  · apply nz_ball D z ε f (hf.mono hball)
    by_contra hall
    push Not at hall
    obtain ⟨w, hwU, hfw⟩ := hne
    have h1 : f =ᶠ[𝓝 z] 0 := by
      filter_upwards [ball_mem_nhds z hε] with x hx using hall x hx
    exact hfw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU h1 hwU)
end ReciprocityTheory.AnForm
