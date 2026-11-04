-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairMass.fixed_pow_clog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:58:52.996127+00:00
-- url     : https://prove2.me/submissions/d47048bf-ec87-4328-993b-477d9c3d19b3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_clog_power_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairMass
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeMomentBounds
open WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaPairMass
theorem _root_.solution (M A n : ℕ) (hM : 1<M) :
    A^(Nat.clog M (n^2))≤M^A*(n+1)^(2*A) := by
  have hA : A≤M^A := (Nat.lt_pow_self hM).le
  have hc := Nat.clog_mono_right M (Nat.pow_le_pow_left (Nat.le_succ n) 2)
  have hp := (Nat.pow_le_pow_right hM.le hc).trans
    (WeightedGlobalSignedPadding.clog_power_bound hM (by positivity : 0<(n+1)^2))
  calc
    _≤(M^A)^(Nat.clog M (n^2)) := Nat.pow_le_pow_left hA _
    _=(M^(Nat.clog M (n^2)))^A := by rw [← pow_mul,← pow_mul,Nat.mul_comm A]
    _≤(M*(n+1)^2)^A := Nat.pow_le_pow_left hp A
    _=_ := by rw [mul_pow,← pow_mul]
end ThreeSum.WeightedGlobalArenaPairMass
