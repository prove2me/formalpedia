-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_primePowerU_eq_ratCast_finiteUQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:39.543457+00:00
-- url     : https://prove2.me/submissions/0b7e30e7-2c8f-4dc3-aad0-055b0c1a0476

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_indexLog_primePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_ratCast_finiteUQ_eq_finiteThetaSum
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    (p n : ℕ) (hp : 1 < p) :
    primePowerU p n = ((finiteUQ (p ^ n) p : ℚ) : ℝ) := by
  rw [ratCast_finiteUQ_eq_finiteThetaSum hp (pow_pos (by omega) _),
    manuscript_indexLog_primePower p n hp]
  rw [primePowerU, finiteThetaSum]
  simp only [Nat.floor_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ ↦
    (p : ℝ) ^ (r * (n - r)) * (gammaR (p : ℝ) r)⁻¹)]
  apply Finset.sum_congr rfl
  intro r hrmem
  have hr : r ≤ n := by
    simp only [Finset.mem_range] at hrmem
    omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show Real.log (p : ℝ) * (r : ℝ) *
      ((n : ℝ) - (r : ℝ)) =
        Real.log (p : ℝ) * ((r * (n - r) : ℕ) : ℝ) by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    ring]
  have hexp : Real.exp
      (Real.log (p : ℝ) * ((r * (n - r) : ℕ) : ℝ)) =
      (p : ℝ) ^ (r * (n - r)) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hpR]
  rw [hexp]
  ring
end SharpIntermediateSubgroupBounds
