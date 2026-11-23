-- Prove2me | solution 1 for ReciprocityTheory.PGsh.colen_eq_v_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:50.050735+00:00
-- url     : https://prove2.me/submissions/b3673ceb-601a-4dcb-962f-9c1de6c984a8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.PGsh
open Matrix
section
variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {v}
end
namespace Lat
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem valuation_det_inv_mul_eq_div (L' L : ReciprocityTheory.PGsh.Lat v ι) :
    v (L.B⁻¹ * L'.B).det = v L'.B.det / v L.B.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_mul, map_inv₀,
    div_eq_inv_mul]
end Lat
section colen
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
end colen
end ReciprocityTheory.PGsh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (L' L : Lat v ι) : colen L' L = v (L.B⁻¹ * L'.B).det := by
  rw [_root_.ReciprocityTheory.PGsh.Lat.valuation_det_inv_mul_eq_div]
  rfl
end ReciprocityTheory.PGsh
