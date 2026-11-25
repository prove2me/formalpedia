-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_antidiag_telescope_f7a8653d28e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:09.274409+00:00
-- url     : https://prove2.me/submissions/347dac02-316d-4cea-85b5-17d868a5f339

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
theorem _root_.solution (g : ℕ → ℕ → ℝ) : ∀ e : ℕ,
    ∑ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) =
      ∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k)
  | 0 => by simp
  | e + 1 => by
    have ih := solution g e
    have h1 : ∀ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e + 1 - k), (g (k + 1) j - g k (j + 1)) =
        ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) + (g (k + 1) (e - k) - g k (e - k + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show e + 1 - k = e - k + 1 by omega, Finset.sum_range_succ]
    have h2 : ∑ k ∈ Finset.range (e + 1), (g (k + 1) (e - k) - g k (e - k + 1)) = g (e + 1) 0 - g 0 (e + 1) := by
      have h3 := Finset.sum_range_sub (fun k => g k (e + 1 - k)) (e + 1)
      simp only [Nat.sub_self, Nat.sub_zero] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show e + 1 - (k + 1) = e - k by omega, show e + 1 - k = e - k + 1 by omega]
    rw [Finset.sum_range_succ _ (e + 1), Finset.sum_range_succ (fun k => g k 0 - g 0 k) (e + 1), ← ih,
      Nat.sub_self, Finset.sum_range_zero, add_zero, Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]
end GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
