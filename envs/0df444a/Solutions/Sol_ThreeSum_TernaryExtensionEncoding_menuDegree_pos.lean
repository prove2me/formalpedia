-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.menuDegree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:06.200194+00:00
-- url     : https://prove2.me/submissions/ae752bed-e783-46f0-be1c-e50e848bae31

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
theorem _root_.solution (Λ K : ℕ) : 0<menuDegree p Λ K := by
  apply Nat.clog_pos (Fact.out : p.Prime).one_lt
  have hp : 0<p^(4*K) := pow_pos (Fact.out : p.Prime).pos _
  nlinarith
end ThreeSum.TernaryExtensionEncoding
