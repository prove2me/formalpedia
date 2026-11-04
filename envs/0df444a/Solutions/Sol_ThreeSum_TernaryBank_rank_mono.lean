-- Prove2me | solution 1 for ThreeSum.TernaryBank.rank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:16.695123+00:00
-- url     : https://prove2.me/submissions/9bb65067-e72e-489b-abe6-75d12f29876b

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
theorem _root_.solution {N : ℕ} {R Q : TritWord N} (h : Below R Q) : rank R ≤ rank Q :=
  Finset.sum_le_sum fun i _ => h i
end ThreeSum.TernaryBank
