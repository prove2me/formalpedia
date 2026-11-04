-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.menu_field_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:05.540895+00:00
-- url     : https://prove2.me/submissions/1e869663-1a46-4826-873b-543f3bad64c8

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menuDegree_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (Λ K : ℕ) :
    p^(menuDegree p Λ K)≤8*p^(4*K+1)*(Λ+1) := by
  have hp := (Fact.out : p.Prime).one_lt
  have hpos := menuDegree_pos (p := p) Λ K
  have ht : 1<8*(Λ+1)*p^(4*K) := by
    have hh := pow_pos (Fact.out : p.Prime).pos (4*K)
    nlinarith
  have hprev := Nat.pow_pred_clog_lt_self hp ht
  have he : menuDegree p Λ K=(menuDegree p Λ K).pred+1 := Nat.succ_pred_eq_of_pos hpos |>.symm
  calc
    _ = p^(menuDegree p Λ K).pred*p := by
      conv_lhs => rw [he]
      rw [pow_succ]
    _ ≤ (8*(Λ+1)*p^(4*K))*p := Nat.mul_le_mul_right p (by simpa only [menuDegree] using hprev.le)
    _ = _ := by rw [pow_succ]; ring
end ThreeSum.TernaryExtensionEncoding
