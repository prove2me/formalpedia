-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Lat.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:36.601669+00:00
-- url     : https://prove2.me/submissions/2fc40d97-1281-4eb1-8ec2-272dfbc3c92e

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
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
open ReciprocityTheory.PGsh.Lat
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Lat
theorem _root_.solution (L : Lat v ι) : IsUnit L.B.det :=
  isUnit_iff_ne_zero.mpr L.det_ne
end ReciprocityTheory.PGsh.Lat
