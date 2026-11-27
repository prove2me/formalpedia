-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_proof_d4400f09e5f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:40.637799+00:00
-- url     : https://prove2.me/submissions/8cff18b4-3247-4bd6-9d55-c21611088c23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermNullstellensatz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_exists_of_mem_holGermIdeal_830af1ccc461
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_mem_holGermIdeal_of_eq_b314ef4b9b79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_coeff_eq_zero_of_distinct_roots_3974fe2d6676

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
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
theorem _root_.solution (hCover : PrimeGermCanonicalCover.Statement) : PrimeGermNullstellensatz.Statement := by
  intro σ _ w k p g hp hg hP hvan
  obtain ⟨d, A, ℓ, N, δ, hδ, hδP, hdiv, hsheet⟩ := hCover σ w k p hp hP
  obtain ⟨M, a, h, ha, hh, hrel⟩ := hdiv g hg

  have hoff : ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ j, a j y = 0 := by
    filter_upwards [hsheet _ (hrel.and hvan)] with y hy hδy
    obtain ⟨x, hx, hinj⟩ := hy hδy
    refine coeff_eq_zero_of_distinct_roots (fun j => a j y) (fun m => ℓ (x m)) hinj fun m => ?_
    obtain ⟨⟨hr, hv⟩, hpx, hAx⟩ := hx m
    have hg0 : g (x m) = 0 := hv hpx
    have h0 : δ (A (x m)) ^ M * g (x m) - ∑ j, a j (A (x m)) * ℓ (x m) ^ (j : ℕ) = 0 := by
      rw [hr]
      simp [hpx]
    rw [hg0, mul_zero, zero_sub, neg_eq_zero, hAx] at h0
    exact h0

  have hδne : ¬ (δ =ᶠ[𝓝 (A w)] 0) := by
    intro h0
    apply hδP
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    filter_upwards [(A.continuous.tendsto w).eventually h0] with z hz
    simpa using hz

  have hzero : ∀ᶠ y in 𝓝 (A w), ∀ j, a j y = 0 := by
    have hall : ∀ᶠ y in 𝓝 (A w), AnalyticAt ℂ δ y ∧ (∀ j, AnalyticAt ℂ (a j) y) ∧
        (δ y ≠ 0 → ∀ j, a j y = 0) :=
      hδ.eventually_analyticAt.and ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and hoff)
    obtain ⟨r, hr0, hrB⟩ := Metric.eventually_nhds_iff_ball.1 hall
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y₀ hy₀ j
    by_contra hne
    apply hδne
    have hnear : δ =ᶠ[𝓝 y₀] 0 := by
      have hcont : ContinuousAt (a j) y₀ := ((hrB y₀ hy₀).2.1 j).continuousAt
      filter_upwards [hcont.eventually_ne hne, Metric.isOpen_ball.mem_nhds hy₀] with y hy hyB
      by_contra hδy
      exact hy ((hrB y hyB).2.2 hδy j)
    have hon : AnalyticOnNhd ℂ δ (Metric.ball (A w) r) := fun y hy => (hrB y hy).1
    have hEq := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hy₀ hnear
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y hy using hEq hy

  have hrel' : ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z = ∑ i, h i z * p i z := by
    filter_upwards [hrel, (A.continuous.tendsto w).eventually hzero] with z hz hz0
    rw [← hz]
    simp [hz0]
  have hδA : AnalyticAt ℂ (fun z => δ (A z)) w := hδ.comp (A.analyticAt w)
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  let Dg : holGerms w := ⟨((fun z => δ (A z) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hδA, rfl⟩
  have hmem : Dg ^ M * G ∈ holGermIdeal w p := by
    refine mem_holGermIdeal_of_eq hp hh _ ?_
    rw [show ((Dg ^ M * G : holGerms w) : Germ (𝓝 w) ℂ) =
        (((fun z => δ (A z)) ^ M * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) by
      rw [Germ.coe_mul, Germ.coe_pow]
      rfl]
    exact Germ.coe_eq.2 (hrel'.mono fun z hz => by simpa using hz)
  have hDg : Dg ∉ holGermIdeal w p := by
    intro hD
    obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hD
    exact hδP ⟨h', hh', Germ.coe_eq.1 e⟩
  have hG : G ∈ holGermIdeal w p := by
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact absurd (hP.mem_of_pow_mem M h1) hDg
    · exact h1
  obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hG
  exact ⟨h', hh', Germ.coe_eq.1 e⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
