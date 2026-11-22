-- Prove2me | solution 1 for QECCertificates.length_lightVecs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:31.018748+00:00
-- url     : https://prove2.me/submissions/44d29358-ab6e-4abb-b487-81c75d71738e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Theorems.Thm_QECCertificates_lightVecs_nil
public import Theorems.Thm_QECCertificates_lightVecs_zero
public import Theorems.Thm_QECCertificates_lightVecs_succ_succ
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.lightVecs_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution : ∀ (n w : ℕ),
    (lightVecs n w).length = ∑ k ∈ Finset.range (w + 1), n.choose k := by
  intro n
  induction n with
  | zero =>
      intro w
      rw [lightVecs_nil]
      rw [Finset.sum_eq_single 0]
      · exact Nat.choose_self 0
      · intro b _ hb
        exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos w)) h
  | succ n ih =>
      intro w
      cases w with
      | zero =>
          rw [lightVecs_zero, Finset.sum_range_one, Nat.choose_zero_right]
          rfl
      | succ w =>
          rw [lightVecs_succ_succ, List.length_append, List.length_map, List.length_map,
            ih (w + 1), ih w]
          rw [Finset.sum_range_succ' (fun j => (n + 1).choose j) (w + 1)]
          rw [Finset.sum_congr rfl (fun j _ => Nat.choose_succ_succ n j), Finset.sum_add_distrib]
          rw [Finset.sum_range_succ' (fun j => n.choose j) (w + 1)]
          rw [Finset.sum_range_succ (fun j => n.choose j) w]
          rw [Nat.choose_zero_right n, Nat.choose_zero_right (n + 1)]
          ring
end QECCertificates
