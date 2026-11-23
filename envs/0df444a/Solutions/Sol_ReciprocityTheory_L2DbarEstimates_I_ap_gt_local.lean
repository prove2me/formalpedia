-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_gt_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:29.046813+00:00
-- url     : https://prove2.me/submissions/a3bd1030-e5c2-4311-a2c6-96fadd7a5811

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (hS : (zeroSet n g).Finite)
    (hW : IsLocalData n g ph r W m) (x : M) (hx : ev n g ph r x < m) :
    gt n z g c W =ᶠ[𝓝 x]
      fun y => (∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y := by
  have key : ∀ p ∈ hS.toFinset, ∀ᶠ y in 𝓝 x,
      (W p).indicator (fun y => c p * jac n z g y) y = (if x ∈ W p then c p else 0) * jac n z g y := by
    intro p hp
    have hpS : p ∈ zeroSet n g := hS.mem_toFinset.1 hp
    obtain ⟨hWo, -, -, hfr, -⟩ := hW.2 p hpS
    by_cases hxW : x ∈ W p
    · filter_upwards [hWo.mem_nhds hxW] with y hy
      simp [hy, hxW]
    · have hxc : x ∉ closure (W p) := by
        intro hc
        have hfx : x ∈ frontier (W p) := ⟨hc, by rwa [hWo.interior_eq]⟩
        exact absurd (hfr x hfx) (not_le.2 hx)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      have hyW : y ∉ W p := fun h => hy (subset_closure h)
      simp [hyW, hxW]
  filter_upwards [(Filter.eventually_all_finset _).2 key] with y hy
  rw [ap_gt_eq_sum n z g c W hS y, Finset.sum_mul]
  exact Finset.sum_congr rfl hy
end ReciprocityTheory.L2DbarEstimates.I
