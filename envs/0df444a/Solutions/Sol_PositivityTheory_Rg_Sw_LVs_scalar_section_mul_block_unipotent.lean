-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.scalar_section_mul_block_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:33.892638+00:00
-- url     : https://prove2.me/submissions/6dfe86d1-9132-4e84-ab7c-8f70b6efed38

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_uAct
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_one_add_mul_embOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {p q : ℤ} {j : ℕ} {x : M2 n} (h1 : (u1 x).det ≠ 0) (h2 : (u2 x).det ≠ 0)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (f0 p q x * (1 + subOn (blkA j) (wM x) * T).det ^ (-q)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ (-p) := by
  have hd1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hd2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have k1 : u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u1 x * (1 + (wM x)⁻¹ * embOn (blkB j) S) := by
    rw [(uAct n x _ _ _ _).1, wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd2]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd1, Matrix.one_mul,
      Matrix.mul_one]
  have k2 : u2 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u2 x * (1 + wM x * embOn (blkA j) T) := by
    rw [(uAct n x _ _ _ _).2, wM]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [f0, f0, k1, k2, Matrix.det_mul, Matrix.det_mul, det_one_add_mul_embOn, det_one_add_mul_embOn,
    mul_zpow, mul_zpow]
  ring
end PositivityTheory.Rg.Sw.LVs
