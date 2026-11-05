-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions.clog_power_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:07:43.42326+00:00
-- url     : https://prove2.me/submissions/b265df3b-9a5c-4d82-9e62-3a24014ccd73

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrincipalDimensions

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {M n : ℕ} (hM : 1 < M) (hn : 1 < n) :
    M^(Nat.clog M (n^2)) ≤ M*n^2 := by
  have hn2 : 1 < n^2 := by nlinarith
  have hpos := Nat.clog_pos hM hn2
  have hl := Nat.pow_pred_clog_lt_self hM hn2
  have he : Nat.clog M (n^2)=(Nat.clog M (n^2)).pred+1 :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  rw [he,pow_succ]
  exact (Nat.mul_le_mul_right M hl.le).trans_eq (Nat.mul_comm _ _)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions
