-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.fB_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:35.584749+00:00
-- url     : https://prove2.me/submissions/11921dfe-7917-4cbb-aab5-8259a83dcc96

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (B : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (x : Fin d → ℤ) : fB B x = ∑ i, ((e.repr x i : ℤ) : ℝ) • fB B (e i) := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, Int.cast_smul_eq_zsmul]
end ReciprocityTheory.ReducedBases.T2
