-- Prove2me | solution 1 for Projectivization.momentMap_mk_eq_inner_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:52.913081+00:00
-- url     : https://prove2.me/submissions/1613391d-da14-4be5-bb57-4db04e4fe9c9

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
public import Theorems.Thm_Projectivization_momentMap_mk

set_option autoImplicit false
@[expose] public section
public section
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Projectivization
theorem _root_.solution (ψ : EuclideanSpace ℂ ι) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : ι) :
    momentMap (mk ℂ ψ hψ0) i = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  rw [momentMap_mk ψ hψ0 i, hψ, one_pow, div_one,
      EuclideanSpace.inner_single_left, map_one, one_mul]
end Projectivization
