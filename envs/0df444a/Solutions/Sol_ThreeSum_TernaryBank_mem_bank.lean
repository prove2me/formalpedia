-- Prove2me | solution 1 for ThreeSum.TernaryBank.mem_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:15.757199+00:00
-- url     : https://prove2.me/submissions/4b4e0817-c3bd-4699-9477-f23b82e9bd34

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N T : ℕ} {R : TritWord N} :
    R ∈ bank N T ↔ rank R ≤ T := by simp [bank]
end ThreeSum.TernaryBank
