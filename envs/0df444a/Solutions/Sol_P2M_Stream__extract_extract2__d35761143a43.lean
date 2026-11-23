-- Prove2me | solution 1 for P2M_Stream__extract_extract2__d35761143a43
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:18:15.13099+00:00
-- url     : https://prove2.me/submissions/a42f88e2-527f-4a4c-bd9f-ec6072ce5aab

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_eq_ofFn_8231fd1645c4

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := by
  ext k x ; rcases (show k < j - i ∨ ¬ k < j - i by omega) with h_k | h_k
    <;> simp [extract_eq_ofFn, h_k]
  · simp only [(show i + k < n - m by omega), (show k < m + j - (m + i) by omega), add_assoc]
  · simp only [(show ¬k < m + j - (m + i) by omega), IsEmpty.forall_iff]
end Stream'
