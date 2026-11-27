-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_proof_d84158b6189f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:40.548025+00:00
-- url     : https://prove2.me/submissions/574319a6-7c62-40d7-82ec-8942e6f4b071

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNonIsolatedFibreCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_analyticOnNhd_of_differentiableOn_c00fe3584ee6

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
open Topology Metric Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NonIsolatedFibreCurve
theorem _root_.solution (hComp : AnalyticGermComponents.Statement)
    (hCurve : IrreducibleGermCurve.Statement) : NonIsolatedFibreCurve.Statement := by
  intro k m U f p hU hf hp hacc
  set Z : Set (Fin k → ℂ) := {v | v ∈ U ∧ f v = f p} with hZ
  have hZan : IsAnalyticNear Z p := by
    refine ⟨U, m, fun i v => f v i - f p i, hU, hp, fun i => ?_, ?_⟩
    · exact analyticOnNhd_of_differentiableOn hU ((differentiableOn_pi.1 hf i).sub_const _)
    · ext v
      simp only [hZ, Set.mem_inter_iff, Set.mem_ofPred_eq, sub_eq_zero, funext_iff]
      tauto
  obtain ⟨n, Y, hY, W, hW, hZW⟩ := hComp (Fin k) Z p hZan ⟨hp, rfl⟩

  have hfreq : ∃ᶠ y in 𝓝 p, y ≠ p ∧ y ∈ ⋃ i, Y i := by
    have h := accPt_iff_frequently.1 hacc
    refine (h.and_eventually hW).mono fun y ⟨⟨hne, hyZ⟩, hyW⟩ => ⟨hne, ?_⟩
    have : y ∈ Z ∩ W := ⟨hyZ, hyW⟩
    rw [hZW] at this
    exact this.1
  obtain ⟨i, hi⟩ : ∃ i, AccPt p (𝓟 (Y i)) := by
    by_contra hno
    push Not at hno
    have hev : ∀ᶠ y in 𝓝 p, ∀ i, ¬ (y ≠ p ∧ y ∈ Y i) := by
      refine eventually_all.2 fun i => ?_
      have := hno i
      rw [accPt_iff_frequently, Filter.not_frequently] at this
      exact this
    obtain ⟨y, ⟨hne, hyU⟩, hy⟩ := (hfreq.and_eventually hev).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hyU
    exact hy j ⟨hne, hj⟩
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγm⟩ := hCurve (Fin k) (Y i) p (hY i).1 (hY i).2 hi

  have hcont : ContinuousAt γ 0 := (hγd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rwa [hγ0])
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hpre
  have hsub : ball (0 : ℂ) (min r ε) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r ε, lt_min hr hε, γ, hγd.mono hsub, hγi.mono hsub, hγ0, fun τ hτ => ?_⟩
  have hτW : γ τ ∈ W := hεW (ball_subset_ball (min_le_right _ _) hτ)
  have : γ τ ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hγm (hsub hτ)⟩, hτW⟩
  rw [← hZW] at this
  exact this.1
end NonIsolatedFibreCurve
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
