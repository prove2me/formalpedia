-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.ratCast_finiteUQ_eq_finiteThetaSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:47.02495+00:00
-- url     : https://prove2.me/submissions/eb8ac44d-1e12-492d-8304-19de4652c9ed

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_ratCast_gammaQ_eq_gammaR
import Theorems.Thm_SharpIntermediateSubgroupBounds_exp_log_band_term
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_pos
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
theorem _root_.solution {q n : ℕ} (hq : 1 < q)
    (hn : 0 < n) :
    ((finiteUQ n q : ℚ) : ℝ) =
      finiteThetaSum (q : ℝ) (indexLog q n) := by
  rw [finiteUQ, finiteThetaSum, natFloor_indexLog]
  push_cast
  let f : ℕ → ℝ := fun r ↦
    (n : ℝ) ^ r /
      (((gammaQ q r : ℚ) : ℝ) * (q : ℝ) ^ (r * r))
  change (∑ r : Fin (Nat.log q n + 1), f r.1) = _
  rw [Fin.sum_univ_eq_sum_range f]
  unfold f
  apply Finset.sum_congr rfl
  intro r hr
  rw [exp_log_band_term hq hn, ← ratCast_gammaQ_eq_gammaR q r (by omega)]
  have hgamma : gammaQ q r ≠ 0 := (gammaQ_pos hq).ne'
  norm_num [div_eq_mul_inv, hgamma]
  ring
end SharpIntermediateSubgroupBounds
