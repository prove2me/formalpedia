-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.exists_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:14.235733+00:00
-- url     : https://prove2.me/submissions/02ced7c7-4ac7-41f9-b67c-0909292f8f01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_img_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_rho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_qinv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exists_density
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_tendsto_ratio


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
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  have := C.nu_finite hR μ
  obtain ⟨c, hc0, hct, hup, hdown⟩ := HExp.exists_density lam (C.nu ρ μ)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  refine ⟨c, hc0, hct, fun S hSm hS hS0 => ?_⟩
  refine (tendsto_ratio lam (C.nu ρ μ) hup hdown S hS hS0).congr' ?_
  filter_upwards [hS ρ hρ] with r hr
  rw [C.nu_apply hR μ (hSm r), Set.inter_eq_self_of_subset_left hr, img_eq]
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
