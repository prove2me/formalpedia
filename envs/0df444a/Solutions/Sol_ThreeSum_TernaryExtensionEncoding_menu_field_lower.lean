-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.menu_field_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:59.061994+00:00
-- url     : https://prove2.me/submissions/f1fcaf1c-0563-4582-8ea8-be2d008a75b9

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (Λ K : ℕ) :
    8*(Λ+1)*p^(4*K)≤p^(menuDegree p Λ K) :=
  Nat.le_pow_clog (Fact.out : p.Prime).one_lt _
end ThreeSum.TernaryExtensionEncoding
