-- Prove2me | solution 1 for Projectivization.momentMap_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:37.336804+00:00
-- url     : https://prove2.me/submissions/1b10a532-ea28-4b5e-86dc-376920feedb6

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap

set_option autoImplicit false
@[expose] public section
public section
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace Projectivization
theorem _root_.solution (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    ∑ i, momentMap p i = 1 := by
  have hrep2 : ‖p.rep‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr p.rep_nonzero)
  unfold momentMap
  rw [← Finset.sum_div, ← EuclideanSpace.norm_sq_eq, div_self hrep2]
end Projectivization
