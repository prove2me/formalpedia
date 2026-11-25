-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.exists_density_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:42.164938+00:00
-- url     : https://prove2.me/submissions/8fdee077-8f1c-44f2-badf-a9daf25e383a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_img_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_rho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_qinv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exists_density


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open ReciprocityTheory.ChartRestriction.DS.HExp.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  have := C.nu_finite hR μ
  obtain ⟨c, hc0, hct, hup, hdown⟩ := HExp.exists_density lam (C.nu ρ μ)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  have key : ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) ρ → C.nu ρ μ s = μ (C.img s) := by
    intro s hs hsρ
    rw [C.nu_apply hR μ hs, Set.inter_eq_self_of_subset_left hsρ, img_eq]
  refine ⟨c, hc0, hct, fun D hD => ?_, fun D hD => ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hup D hD
    refine ⟨min δ ρ, lt_min hδ hρ, fun s hsm hs => ?_⟩
    rw [← key s hsm (hs.trans (ball_subset_ball (min_le_right _ _)))]
    exact h s (hs.trans (ball_subset_ball (min_le_left _ _)))
  · obtain ⟨δ, hδ, h⟩ := hdown D hD
    refine ⟨min δ ρ, lt_min hδ hρ, fun s hsm hs => ?_⟩
    rw [← key s hsm (hs.trans (ball_subset_ball (min_le_right _ _)))]
    exact h s (hs.trans (ball_subset_ball (min_le_left _ _)))
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
