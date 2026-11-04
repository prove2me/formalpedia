-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.F_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:26:16.230464+00:00
-- url     : https://prove2.me/submissions/b8276efb-9fc1-4244-879b-4b6416d12158

import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Theorems.Thm_ThreeSum_WeightedGlobalExecutableParameters_family_gt_one

set_option autoImplicit false

theorem solution {κ : ℕ} (P : ThreeSum.WeightedGlobalConcreteProfile.Profile κ) : 1 < P.F :=
  ThreeSum.WeightedGlobalExecutableParameters.family_gt_one P.K_pos P.m P.k
