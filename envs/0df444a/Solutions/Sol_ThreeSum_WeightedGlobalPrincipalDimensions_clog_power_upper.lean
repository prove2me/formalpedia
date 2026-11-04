-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.clog_power_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:01:55.224834+00:00
-- url     : https://prove2.me/submissions/f22a1a6b-6a9e-415a-b04d-a38af8f31122

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {M n : ℕ} (hM : 1 < M) (hn : 1 < n) :
    M^(Nat.clog M (n^2)) ≤ M*n^2 := by
  have hn2 : 1 < n^2 := by nlinarith
  have hpos := Nat.clog_pos hM hn2
  have hl := Nat.pow_pred_clog_lt_self hM hn2
  have he : Nat.clog M (n^2)=(Nat.clog M (n^2)).pred+1 :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  rw [he,pow_succ]
  exact (Nat.mul_le_mul_right M hl.le).trans_eq (Nat.mul_comm _ _)
end ThreeSum.WeightedGlobalPrincipalDimensions
