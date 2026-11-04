-- Prove2me | solution 1 for ThreeSum.TernaryEndBridge.solvedAt_of_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:46.339242+00:00
-- url     : https://prove2.me/submissions/e5de805b-8ea8-4ff3-9eea-11f3914ea91d

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_realized_of_solves
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_b08943e3ece6cc44
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section
namespace ThreeSum.TernaryEndBridge
theorem _root_.solution {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need} {a : ℝ}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in Filter.atTop,
      timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ a) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ a 0 := by
  apply ThreeSumApsp.FromClaims.solvedAt_of_realized
    (timeUpTo T) κ (realized_of_solves hs hp) (C := 1)
  simpa only [pow_zero, mul_one, one_mul] using ht
end ThreeSum.TernaryEndBridge
