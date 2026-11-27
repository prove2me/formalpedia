-- Prove2me | solution 1 for ReciprocityTheory.PGsh.colen_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:00.494861+00:00
-- url     : https://prove2.me/submissions/26504965-000e-440d-958d-784c11832ca3

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
end Lat
section colen
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem valuation_det_dual_eq_inv {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) :
    v L.dual.B.det = (v L.B.det)⁻¹ := by
  show v ((L.Bᵀ)⁻¹).det = _
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_transpose, map_inv₀]
end colen
end ReciprocityTheory.PGsh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (L' L : Lat v ι) : colen L.dual L'.dual = colen L' L := by
  unfold colen
  rw [valuation_det_dual_eq_inv, valuation_det_dual_eq_inv, inv_div_inv]
end ReciprocityTheory.PGsh
