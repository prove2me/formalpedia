-- Prove2me | solution 1 for ReciprocityTheory.PGsh.IsIntegralMat.det_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:48.216185+00:00
-- url     : https://prove2.me/submissions/5b794aa1-3ab8-4188-a0bf-c194ae69234c

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
namespace IsIntegralMat
theorem _root_.solution {U : Matrix ι ι K} (hU : IsIntegralMat v U) : v U.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine v.map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  have hs : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hs, one_mul]
  exact Finset.prod_le_one (fun _ _ => zero_le) fun i _ => hU _ _
end IsIntegralMat
end ReciprocityTheory.PGsh
