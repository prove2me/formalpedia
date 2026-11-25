-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_inter_ne_zero_of_complex_4bc36446fe62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:16.724831+00:00
-- url     : https://prove2.me/submissions/05387a83-7673-47f2-99cc-374e25a63d6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_ball_diff_countable_8821c6595739

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Set
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ManifoldZerosComplementConnected
theorem _root_.solution {V : Set ℂ}
    (hVo : IsOpen V) (hV : IsPreconnected V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hφz₀ : φ z₀ ≠ 0) : IsPreconnected (V ∩ {z | φ z ≠ 0}) := by
  have hev : ∀ z ∈ V, ∀ᶠ w in 𝓝[≠] z, φ w ≠ 0 := by
    intro z hz
    rcases (hφ z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV hz h hz₀) hφz₀
    · exact h
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hV inter_subset_left ?_ ?_
  · intro z hz
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ V ∩ {z | φ z ≠ 0} :=
      ((hev z hz).and (nhdsWithin_le_nhds (hVo.mem_nhds hz))).mono fun w hw => ⟨hw.2, hw.1⟩
    exact mem_closure_iff_frequently.mpr (h1.frequently.filter_mono nhdsWithin_le_nhds)
  · intro z hz
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo z hz
    obtain ⟨r', hr', hr'φ⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp (hev z hz))
    have hρ : 0 < min r r' := lt_min hr hr'
    refine ⟨Metric.ball z (min r r'), Metric.isOpen_ball, Metric.mem_ball_self hρ, ?_⟩
    have heq : Metric.ball z (min r r') ∩ (V ∩ {w | φ w ≠ 0}) =
        Metric.ball z (min r r') \ ({z} \ {w | φ w ≠ 0}) := by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hb, -, hne⟩
        exact ⟨hb, fun h => h.2 hne⟩
      · rintro ⟨hb, hw⟩
        refine ⟨hb, hrV (Metric.ball_subset_ball (min_le_left _ _) hb), ?_⟩
        by_cases hwz : w = z
        · intro h0
          exact hw ⟨hwz, fun h => h h0⟩
        · exact hr'φ w (Metric.ball_subset_ball (min_le_right _ _) hb) hwz
    rw [heq]
    exact ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable
      (by rw [Complex.rank_real_complex]; exact_mod_cast (by norm_num : (1 : ℕ) < 2)) z hρ ((countable_singleton z).mono sdiff_subset)
end ManifoldZerosComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
