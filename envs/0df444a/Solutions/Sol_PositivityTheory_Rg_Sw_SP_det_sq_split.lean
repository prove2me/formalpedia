-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.det_sq_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:15.307075+00:00
-- url     : https://prove2.me/submissions/966e882e-65ab-4307-be1e-6e50b81d8e23

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_c_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (B : MC n) :
    (1 + Matrix.of B * Matrix.of B).det =
      (1 - (Complex.I * s) • Matrix.of B).det * (1 + (Complex.I * s) • Matrix.of B).det := by
  rw [← Matrix.det_mul]
  congr 1
  have hc := c_sq s hs
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
  simp only [neg_smul, one_smul]
  abel
end PositivityTheory.Rg.Sw.SP
