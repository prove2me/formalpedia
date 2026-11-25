-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.sum_single_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:48:00.989402+00:00
-- url     : https://prove2.me/submissions/20fc234d-ec72-4c02-8e7f-688cb039a597

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (W : Submodule ℂ (M2 n)) (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n)
    (h : ∀ i j a, Φ (Matrix.single i j a) ∈ W) (M : Matrix (Fin n) (Fin n) ℂ) : Φ M ∈ W := by
  rw [Matrix.matrix_eq_sum_single M, map_sum]
  exact Submodule.sum_mem _ fun i _ => by rw [map_sum]; exact Submodule.sum_mem _ fun j _ => h i j _
end PositivityTheory.Rg.Sw.LVs.II
