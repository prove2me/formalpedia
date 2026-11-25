-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_one_add_mul_embOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:14.240138+00:00
-- url     : https://prove2.me/submissions/0b1a4d54-0034-46e4-bf5c-661511719701

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_embOn_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_incl_mul

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
theorem _root_.solution (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det = (1 + subOn s M * T).det := by
  rw [embOn_eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.det_one_add_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [incl_mul]
end PositivityTheory.Rg.Sw.LVs
