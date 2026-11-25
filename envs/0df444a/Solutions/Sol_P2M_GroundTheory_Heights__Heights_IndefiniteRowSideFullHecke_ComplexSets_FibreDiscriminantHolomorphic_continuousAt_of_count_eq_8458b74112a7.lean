-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_continuousAt_of_count_eq_8458b74112a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:09:39.653769+00:00
-- url     : https://prove2.me/submissions/065fc0ad-ed74-48bf-8ca9-19748c77e571

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_continuous_pairProd_074550953a77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_enum_8b9a428901b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_fibreDiscr_eq_pairProd_4d8cdf3a1f36

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
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard = N) : ContinuousAt (fibreDiscr Y A l N) y₀ := by
  obtain ⟨p, hp, hrange⟩ := exists_enum hN
  have hpY : ∀ i, p i ∈ Y ∧ A (p i) = y₀ := fun i => by
    have : p i ∈ range p := mem_range_self i
    rw [hrange] at this
    exact this
  obtain ⟨U, hU, hdisj⟩ := (Set.finite_range p).t2_separation
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hΦ⟩ := Metric.continuousAt_iff.1 (continuous_pairProd l).continuousAt ε hε
  have hev : ∀ i, ∀ᶠ y in 𝓝 y₀, y ∈ A '' (Y ∩ (U (p i) ∩ ball (p i) δ)) := by
    intro i
    have := hopen (p i) (hpY i).1 _
      (inter_mem ((hU (p i)).2.mem_nhds (hU (p i)).1) (ball_mem_nhds _ hδ))
    rwa [(hpY i).2] at this
  filter_upwards [Filter.eventually_all.2 hev, hD.mem_nhds hy₀] with y hy hyD
  choose q hq hqy using hy
  have hqinj : Function.Injective q := by
    intro i j hij
    by_contra hne
    have hd := hdisj (mem_range_self i) (mem_range_self j) (fun h => hne (hp h))
    exact Set.disjoint_left.1 hd (hq i).2.1 (by rw [hij]; exact (hq j).2.1)
  rw [fibreDiscr_eq_pairProd l (hle y hyD) hqinj (fun i => ⟨(hq i).1, hqy i⟩),
    fibreDiscr_eq_pairProd l (hle y₀ hy₀) hp hpY]
  apply hΦ
  rw [dist_pi_lt_iff hδ]
  intro i
  exact (hq i).2.2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
