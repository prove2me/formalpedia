-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceBounds.value_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:17:54.826622+00:00
-- url     : https://prove2.me/submissions/09254b83-fde0-4d9f-aeca-47b76de4be7d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_local_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceBounds
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
end ThreeSum.WeightedGlobalArenaSourceBounds
