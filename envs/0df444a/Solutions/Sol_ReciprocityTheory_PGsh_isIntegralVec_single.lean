-- Prove2me | solution 1 for ReciprocityTheory.PGsh.isIntegralVec_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:18.774811+00:00
-- url     : https://prove2.me/submissions/e6c55f74-79e4-43e7-ab33-a58ac1ec74a0

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
variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {v}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (j : ι) : IsIntegralVec v (Pi.single j (1 : K)) := by
  intro k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]
end ReciprocityTheory.PGsh
