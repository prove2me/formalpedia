-- Prove2me | solution 1 for ThreeSum.TernaryBank.rank_update_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:02.396253+00:00
-- url     : https://prove2.me/submissions/23675122-04d7-4c5f-8ef4-9139c63ac9ef

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_rank_update_add

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) :
    rank (Function.update R i d) = rank R - ((R i).val - d.val) := by
  have h := rank_update_add R i d
  have hv : d.val ≤ (R i).val := hd
  omega
end ThreeSum.TernaryBank
