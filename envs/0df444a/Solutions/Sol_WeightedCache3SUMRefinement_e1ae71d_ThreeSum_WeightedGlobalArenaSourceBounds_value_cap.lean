-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.value_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:42:11.7622+00:00
-- url     : https://prove2.me/submissions/71b126e7-7d7a-4107-8ecd-37bf9afee929

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceBounds_local_le

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (n U H : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    valueCap (r := r) maps cap I≤(2^fixedAlpha m 2)^r*
      weight H (4^fixedLength m) U*(2*n*(sourceWidth maps cap)^r+1) := by
  have hl:=Nat.pow_le_pow_left (local_le maps cap false) r
  have hr:=Nat.pow_le_pow_left (local_le maps cap true) r
  have hsum : I.nB*(localRecords maps cap false).length^r+
      I.nC*(localRecords maps cap true).length^r+1≤2*n*(sourceWidth maps cap)^r+1 := by
    nlinarith [Nat.mul_le_mul hnB hl,Nat.mul_le_mul hnC hr]
  unfold valueCap
  rw [show 2^(r*fixedAlpha m 2)=(2^fixedAlpha m 2)^r by rw [←pow_mul,Nat.mul_comm]]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hweight) hsum
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
