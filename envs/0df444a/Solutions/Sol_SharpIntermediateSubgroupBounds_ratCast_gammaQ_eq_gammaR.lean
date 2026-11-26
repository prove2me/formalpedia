-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.ratCast_gammaQ_eq_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:41.135392+00:00
-- url     : https://prove2.me/submissions/77f158d3-a2c8-40a7-bed7-c6906620963b

import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_succ
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons


attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (q r : ℕ) (hq : 0 < q) :
    ((gammaQ q r : ℚ) : ℝ) = gammaR (q : ℝ) r := by
  induction r with
  | zero => simp [gammaR]
  | succ r ih =>
      rw [gammaQ_succ q r hq]
      rw [gammaR, Finset.prod_range_succ]
      rw [gammaR] at ih
      push_cast
      rw [ih]
      congr 2
      norm_num [div_eq_mul_inv]
end SharpIntermediateSubgroupBounds
