-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Holo.db_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:32.897111+00:00
-- url     : https://prove2.me/submissions/95a08636-d1cb-471e-86ba-4715052e7ca4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
private theorem wdb_eq_zero_of_complex_differentiableAt {n : ℕ} (j : Fin n) {g : V n → ℂ} {y : V n}
    (hg : DifferentiableAt ℂ g y) : wdb n j g y = 0 := by
  unfold wdb
  rw [hg.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul,
    ← mul_assoc, Complex.I_mul_I]
  ring
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Holo
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Holo n z f) (j : Fin n) (x : M) : db n z j f x = 0 := by
  unfold db
  split_ifs with h
  · obtain ⟨hc, hxc⟩ := Classical.choose_spec h
    apply wdb_eq_zero_of_complex_differentiableAt
    rw [hc hxc]
    exact (hf _ hc).differentiableAt
      ((Classical.choose h).open_target.mem_nhds ((Classical.choose h).map_source hxc))
  · rfl
end Holo
end ReciprocityTheory.L2DbarEstimates
