-- Prove2me | solution 1 for ReciprocityTheory.PGsh.colen_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:47.505183+00:00
-- url     : https://prove2.me/submissions/059dd049-ffdb-42fb-8415-0445115dbaf3

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
private theorem valuation_lat_det_ne_zero (L : ReciprocityTheory.PGsh.Lat v ι) : v L.B.det ≠ 0 :=
  (Valuation.ne_zero_iff v).mpr L.det_ne
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
theorem _root_.solution (L : Lat v ι) : colen L L = 1 :=
  div_self (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L)
end ReciprocityTheory.PGsh
