-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_indexLog_primePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:28.832797+00:00
-- url     : https://prove2.me/submissions/4019eb27-1741-468e-8ac4-5be2d51cc3aa

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p n : ℕ) (hp : 1 < p) :
    indexLog p (p ^ n) = n := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hpR).ne'
  rw [indexLog, Nat.cast_pow, Real.log_pow]
  exact mul_div_cancel_right₀ (n : ℝ) hlog
end SharpIntermediateSubgroupBounds
