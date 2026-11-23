-- Prove2me | solution 1 for P2M_Stream__extract_eq_extract_14275bcbb551
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:20:46.664396+00:00
-- url     : https://prove2.me/submissions/b5a4f10a-2e97-4796-b21e-f2f178bcb73c

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_eq_ofFn_8231fd1645c4

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs xs' : Stream' X} {m n m' n' : ℕ}
    (h : xs.extract m n = xs'.extract m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by
  simp only [extract_eq_ofFn, List.ofFn_inj', Sigma.mk.injEq] at h
  obtain ⟨h_eq, h_fun⟩ := h
  rw [← h_eq] at h_fun ; simp only [heq_eq_eq, funext_iff, Fin.forall_iff] at h_fun
  simp only [← h_eq, true_and] ; intro k h_k ; simp only [h_fun k h_k]
end Stream'
