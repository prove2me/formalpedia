-- Prove2me | solution 1 for ReciprocityTheory.PGsh.IsIntegralMat.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:23.063985+00:00
-- url     : https://prove2.me/submissions/4eeb209b-066c-483d-9a87-f4d7b9b6cd24

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
private theorem nnreal_mul_le_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  simpa using mul_le_mul ha hb (zero_le) zero_le_one
end
namespace Lat
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
end Lat
section colen
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
end colen
end ReciprocityTheory.PGsh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {v}
namespace ReciprocityTheory.PGsh
namespace IsIntegralMat
theorem _root_.solution {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) : IsIntegralMat v (U * V) := by
  intro i j
  rw [Matrix.mul_apply]
  exact v.map_sum_le fun k _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i k) (hV k j)
end IsIntegralMat
end ReciprocityTheory.PGsh
