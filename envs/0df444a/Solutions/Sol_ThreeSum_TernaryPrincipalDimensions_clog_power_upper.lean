-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.clog_power_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:47.643669+00:00
-- url     : https://prove2.me/submissions/b562a87f-44ee-4b78-bd99-95b24f464b9b

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {M n : ℕ} (hM : 1 < M) (hn : 1 < n) :
    M^(Nat.clog M (n^2)) ≤ M*n^2 := by
  have hn2 : 1 < n^2 := by nlinarith
  have hpos := Nat.clog_pos hM hn2
  have hl := Nat.pow_pred_clog_lt_self hM hn2
  have he : Nat.clog M (n^2)=(Nat.clog M (n^2)).pred+1 :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  rw [he,pow_succ]
  exact (Nat.mul_le_mul_right M hl.le).trans_eq (Nat.mul_comm _ _)
end ThreeSum.TernaryPrincipalDimensions
