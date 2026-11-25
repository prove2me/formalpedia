-- Prove2me | solution 1 for OptimalAffinity.oa2x2_published_stationary_optimum_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:07:44.985906+00:00
-- url     : https://prove2.me/submissions/4355ed0a-490b-44bd-a17a-633ccd612a68

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
public import Theorems.Thm_OptimalAffinity_stationaryY_one
public import Theorems.Thm_OptimalAffinity_stationaryY_steady_of_nonneg
public import Theorems.Thm_OptimalAffinity_stationaryY_positive_near_one
public import Theorems.Thm_OptimalAffinity_stationary_current_hasDerivAt_one
public import Theorems.Thm_OptimalAffinity_oa2x2_current_le_one
public import Theorems.Thm_OptimalAffinity_oa2x2_one_one_current


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution :
    ∃ y : ℝ → ℝ,
      y 1 = 1 ∧
      HasDerivAt (fun x => productionCurrent oa2x2 x (y x)) 0 1 ∧
      ∀ᶠ x : ℝ in nhds 1,
        0 < x ∧ 0 < y x ∧ YSteady oa2x2 x (y x) ∧
          productionCurrent oa2x2 x (y x) ≤
            productionCurrent oa2x2 1 1 := by
  refine ⟨stationaryY, stationaryY_one, stationary_current_hasDerivAt_one, ?_⟩
  have hx : ∀ᶠ x : ℝ in nhds 1, 0 < x :=
    isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
  filter_upwards [hx, stationaryY_positive_near_one] with x hx hy
  have hs := stationaryY_steady_of_nonneg hx.le
  exact ⟨hx, hy, hs, by
    rw [oa2x2_one_one_current]
    exact oa2x2_current_le_one x (stationaryY x) hy hs⟩
end OptimalAffinity
