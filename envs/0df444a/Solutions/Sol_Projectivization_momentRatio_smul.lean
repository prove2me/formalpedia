-- Prove2me | solution 1 for Projectivization.momentRatio_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:38.317153+00:00
-- url     : https://prove2.me/submissions/ecd90bc9-3df8-4ef5-8683-348d0e810621

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
theorem _root_.solution (c : ℂ) (hc : c ≠ 0) (v : EuclideanSpace ℂ ι) (i : ι) :
    ‖(c • v) i‖ ^ 2 / ‖c • v‖ ^ 2 = ‖v i‖ ^ 2 / ‖v‖ ^ 2 := by
  rw [PiLp.smul_apply, smul_eq_mul, norm_smul, norm_mul, mul_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]
end Projectivization
