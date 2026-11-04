-- Prove2me | solution 1 for ThreeSum.TernaryBank.bank_downward_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:14.622518+00:00
-- url     : https://prove2.me/submissions/3781324b-6c63-453b-a5be-5a64ad6df22d

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_rank_mono
attribute [local simp] ThreeSum.TernaryBank.mem_bank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N T : ℕ} {R Q : TritWord N}
    (hRQ : Below R Q) (hQ : Q ∈ bank N T) : R ∈ bank N T :=
  mem_bank.mpr ((rank_mono hRQ).trans (mem_bank.mp hQ))
end ThreeSum.TernaryBank
