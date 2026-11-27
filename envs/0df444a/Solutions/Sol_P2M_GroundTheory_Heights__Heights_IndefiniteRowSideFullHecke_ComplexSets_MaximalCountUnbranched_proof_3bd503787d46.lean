-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_proof_3bd503787d46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:35.677376+00:00
-- url     : https://prove2.me/submissions/04e7f4a9-94bf-4312-b1ed-f50239bbbeb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaximalCountUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaximalCountUnbranched
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_analyticOnNhd_of_differentiableOn_pi_eff0fba7ce93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_fibre_unique_near_7ec4b92fbfb3

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
open Topology Filter Metric
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
theorem _root_.solution (hRE : RiemannExtensionAnalytic.Statement) : MaximalCountUnbranched.Statement := by
  intro σ _ Y d A D N _hD hmaps _hprop hopen hgen x hx hxN
  have key := fun (z : σ → ℂ) (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) =>
    fibre_unique_near hmaps hopen hgen.1 hz hzN
  obtain ⟨ε, ⟨W₀, hW₀, hW₀p⟩, hε0⟩ := ((key x hx hxN).and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  obtain ⟨U, g, hUo, hxU, _hUD, hg, hgnz, hgsec⟩ := hgen.2 (A x) (hmaps hx)
  have hOo : IsOpen (interior W₀ ∩ U) := isOpen_interior.inter hUo
  have hOW : ∀ y ∈ interior W₀ ∩ U, y ∈ W₀ := fun y hy => interior_subset hy.1
  have hex : ∀ y ∈ interior W₀ ∩ U, ∃ x' ∈ Y, A x' = y ∧ dist x' x < ε :=
    fun y hy => (hW₀p y (hOW y hy)).2.1
  choose! h hhY hhA hhd using hex
  have hu : ∀ y ∈ interior W₀ ∩ U, ∀ x' ∈ Y, A x' = y → dist x' x < ε → x' = h y :=
    fun y hy x' hx' hA hd =>
      (hW₀p y (hOW y hy)).2.2 x' hx' (h y) (hhY y hy) hA (hhA y hy) hd (hhd y hy)

  have hcont : ContinuousOn h (interior W₀ ∩ U) := by
    intro y₀ hy₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro η hη
    have hzN : {x' | x' ∈ Y ∧ A x' = A (h y₀)}.encard = N := by
      rw [hhA y₀ hy₀]; exact (hW₀p y₀ (hOW y₀ hy₀)).1
    have hgap : 0 < ε - dist (h y₀) x := by linarith [hhd y₀ hy₀]
    have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < min η (ε - dist (h y₀) x) :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hη hgap))
    obtain ⟨e, ⟨W₁, hW₁, hW₁p⟩, he⟩ := ((key (h y₀) (hhY y₀ hy₀) hzN).and hsmall).exists
    rw [hhA y₀ hy₀] at hW₁
    filter_upwards [hW₁, hOo.mem_nhds hy₀] with y hy1 hyO
    obtain ⟨x'', hx''Y, hx''A, hx''d⟩ := (hW₁p y hy1).2.1
    have hm1 := min_le_left η (ε - dist (h y₀) x)
    have hm2 := min_le_right η (ε - dist (h y₀) x)
    have hx''x : dist x'' x < ε := by
      have := dist_triangle x'' (h y₀) x
      linarith
    rw [← hu y hyO x'' hx''Y hx''A hx''x]
    linarith

  have hdiff : ∀ y₀ ∈ interior W₀ ∩ U, g y₀ ≠ 0 → DifferentiableAt ℂ h y₀ := by
    intro y₀ hy₀ hg₀
    obtain ⟨_, hsec⟩ := hgsec y₀ hy₀.2 hg₀
    obtain ⟨O₁, V₁, h₁, hO₁, _hV₁, hzV₁, han₁, hA₁, hYV₁⟩ := hsec (h y₀) (hhY y₀ hy₀) (hhA y₀ hy₀)
    have hz : h y₀ ∈ h₁ '' O₁ := hYV₁ ▸ ⟨hhY y₀ hy₀, hzV₁⟩
    obtain ⟨y₁, hy₁, hy₁e⟩ := hz
    have hy₁₀ : y₁ = y₀ := by rw [← hA₁ y₁ hy₁, hy₁e, hhA y₀ hy₀]
    rw [hy₁₀] at hy₁ hy₁e
    have hc₁ : ContinuousAt h₁ y₀ := (han₁ y₀ hy₁).continuousAt
    have hball : ball x ε ∈ 𝓝 (h₁ y₀) := by
      rw [hy₁e]; exact isOpen_ball.mem_nhds (mem_ball.2 (hhd y₀ hy₀))
    have heq : h₁ =ᶠ[𝓝 y₀] h := by
      filter_upwards [hc₁.preimage_mem_nhds hball, hO₁.mem_nhds hy₁, hOo.mem_nhds hy₀]
        with y hyb hyO₁ hyO
      have hyY : h₁ y ∈ Y := by
        have hmem : h₁ y ∈ h₁ '' O₁ := ⟨y, hyO₁, rfl⟩
        rw [← hYV₁] at hmem
        exact hmem.1
      exact hu y hyO (h₁ y) hyY (hA₁ y hyO₁) (mem_ball.1 hyb)
    exact (han₁ y₀ hy₁).differentiableAt.congr_of_eventuallyEq heq.symm

  have hgd : DifferentiableOn ℂ g (interior W₀ ∩ U) := hg.differentiableOn.mono fun y hy => hy.2
  have hgnz' : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ interior W₀ ∩ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0 :=
    fun V hV hVO hVn => hgnz V hV (hVO.trans Set.inter_subset_right) hVn
  have hdense : interior W₀ ∩ U ⊆ closure ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) := by
    intro y hy
    rw [_root_.mem_closure_iff]
    intro o ho hyo
    obtain ⟨t, ht, hgt⟩ := hgnz' (o ∩ (interior W₀ ∩ U)) (ho.inter hOo) Set.inter_subset_right ⟨y, hyo, hy⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  have hcoord : ∀ j : σ, DifferentiableOn ℂ (fun y => h y j) (interior W₀ ∩ U) := by
    intro j
    have hdj : DifferentiableOn ℂ (fun y => h y j) ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) :=
      fun y hy => (differentiableAt_pi.1 (hdiff y hy.1 hy.2) j).differentiableWithinAt
    have hbj : ∀ τ ∈ interior W₀ ∩ U, ∃ M ∈ 𝓝 τ,
        Bornology.IsBounded ((fun y => h y j) '' (M ∩ (interior W₀ ∩ U) ∩ {t | g t ≠ 0})) := by
      intro τ _
      refine ⟨Set.univ, univ_mem, ?_⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x‖ + ε, ?_⟩
      rintro _ ⟨y, ⟨⟨_, hyO⟩, _⟩, rfl⟩
      calc ‖h y j‖ ≤ ‖h y‖ := norm_le_pi_norm (h y) j
        _ ≤ ‖x‖ + ε := norm_le_of_mem_closedBall (mem_closedBall.2 (hhd y hyO).le)
    obtain ⟨F, hF, hFe⟩ := hRE d (interior W₀ ∩ U) g (fun y => h y j) hOo hgd hgnz' hdj hbj
    have hEq : Set.EqOn F (fun y => h y j) (interior W₀ ∩ U) :=
      hFe.of_subset_closure hF.continuousOn (continuousOn_pi.1 hcont j) Set.inter_subset_left hdense
    exact hF.congr fun y hy => (hEq hy).symm
  have han : AnalyticOnNhd ℂ h (interior W₀ ∩ U) :=
    analyticOnNhd_of_differentiableOn_pi hOo (differentiableOn_pi.2 hcoord)
  refine ⟨interior W₀ ∩ U, ball x ε ∩ A ⁻¹' (interior W₀ ∩ U), h, hOo,
    isOpen_ball.inter (hOo.preimage A.continuous),
    ⟨mem_ball_self hε0, mem_interior_iff_mem_nhds.2 hW₀, hxU⟩, han, hhA, ?_⟩
  ext x'
  constructor
  · rintro ⟨hx'Y, hx'b, hx'O⟩
    exact ⟨A x', hx'O, (hu (A x') hx'O x' hx'Y rfl (mem_ball.1 hx'b)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hhY y hy, mem_ball.2 (hhd y hy), show A (h y) ∈ interior W₀ ∩ U from (hhA y hy).symm ▸ hy⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
