-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass.fixed_pow_clog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:57:40.917195+00:00
-- url     : https://prove2.me/submissions/a235eca6-88ac-4ada-9a02-7d13018864b0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPadding_clog_power_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeMomentBounds
open WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPairMass
