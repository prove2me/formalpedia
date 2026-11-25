-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.removable_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:04.611833+00:00
-- url     : https://prove2.me/submissions/aa9435ce-f82d-414d-8ba2-4cfb596e0288

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_RemovableFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution (S : Finset ℂ) : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (↑S)ᶜ →
    (∀ c ∈ S, ∃ M : ℝ, ∀ᶠ t in 𝓝[≠] c, ‖f t‖ ≤ M) →
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ t ∉ S, F t = f t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro f hd _
    refine ⟨f, ?_, fun _ _ => rfl⟩
    exact differentiableOn_univ.mp (by simpa using hd)
  | insert c S hc ih =>
    intro f hd hb
    obtain ⟨M, hM⟩ := hb c (Finset.mem_insert_self c S)
    have hSc : ∀ᶠ t in 𝓝 c, t ∉ (S : Set ℂ) :=
      (S.finite_toSet.isClosed.isOpen_compl).mem_nhds (by simpa using hc)
    rw [eventually_nhdsWithin_iff] at hM
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hM.and hSc)
    set g := Function.update f c (limUnder (𝓝[≠] c) f) with hg
    have hsub : Metric.ball c ε \ {c} ⊆ (↑(insert c S) : Set ℂ)ᶜ := by
      intro t ht
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
      exact ⟨ht.2, (hball ht.1).2⟩
    have hgc : DifferentiableOn ℂ g (Metric.ball c ε) := by
      apply Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hε)
        (hd.mono hsub)
      refine ⟨M, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact (hball ht.1).1 ht.2
    have hgS : DifferentiableOn ℂ g (↑S)ᶜ := by
      intro t ht
      by_cases htc : t = c
      · subst htc
        exact (hgc.differentiableAt (Metric.ball_mem_nhds _ hε)).differentiableWithinAt
      · have hmem : t ∈ (↑(insert c S) : Set ℂ)ᶜ := by
          simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
          exact ⟨htc, ht⟩
        have hft : DifferentiableAt ℂ f t :=
          hd.differentiableAt ((Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds hmem)
        have heq : g =ᶠ[𝓝 t] f := by
          filter_upwards [isOpen_compl_singleton.mem_nhds htc] with y hy
          exact Function.update_of_ne hy _ _
        exact (hft.congr_of_eventuallyEq heq).differentiableWithinAt
    have hgb : ∀ c' ∈ S, ∃ M : ℝ, ∀ᶠ t in 𝓝[≠] c', ‖g t‖ ≤ M := by
      intro c' hc'
      obtain ⟨M', hM'⟩ := hb c' (Finset.mem_insert_of_mem hc')
      refine ⟨M', ?_⟩
      have hne : c' ≠ c := fun h => hc (h ▸ hc')
      have hnc : ∀ᶠ t in 𝓝[≠] c', t ≠ c :=
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne)
      filter_upwards [hM', hnc] with t h1 h2
      rwa [hg, Function.update_of_ne h2]
    obtain ⟨F, hF, hFg⟩ := ih g hgS hgb
    refine ⟨F, hF, fun t ht => ?_⟩
    have htc : t ≠ c := fun h => ht (h ▸ Finset.mem_insert_self c S)
    have htS : t ∉ S := fun h => ht (Finset.mem_insert_of_mem h)
    rw [hFg t htS, hg, Function.update_of_ne htc]
end ReciprocityTheory.L2DbarEstimates.Norm
