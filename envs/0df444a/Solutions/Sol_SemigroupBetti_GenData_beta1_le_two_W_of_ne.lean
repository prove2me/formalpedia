-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_le_two_W_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:23:22.250868+00:00
-- url     : https://prove2.me/submissions/0c3d303f-5498-49a2-88fa-18ff06a353b9

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
public import Theorems.Thm_SemigroupBetti_GenData_beta1_le_general
public import Theorems.Thm_SemigroupBetti_GenData_general_bound_eq
public import Theorems.Thm_SemigroupBetti_GenData_dg_eq_s_of_s_eq_t
public import Theorems.Thm_SemigroupBetti_GenData_R_eq
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_p
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_q
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_p_add_q_eq
public import Theorems.Thm_SemigroupBetti_GenData_p_add_q_le
public import Theorems.Thm_SemigroupBetti_GenData_s_pos
public import Theorems.Thm_SemigroupBetti_GenData_t_pos
public import Theorems.Thm_SemigroupBetti_GenData_two_le_R
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (h : (G.s, G.t) ≠ (1, 1)) : G.beta1 ≤ 2 * G.W := by
  have hb := G.beta1_le_general
  rw [G.general_bound_eq] at hb
  have hs := G.s_pos
  have ht := G.t_pos
  have hR := G.two_le_R
  rw [G.R_eq] at hR
  rw [← G.p_add_q_eq] at hb
  have hpq := G.p_add_q_le
  rcases lt_trichotomy G.s G.t with hlt | heq | hgt
  · -- Case 1: `s < t`
    omega
  · -- Cases 3–4: `s = t`, so `d = s` and `p = q = 1`
    have hdg : G.dg = G.s := G.dg_eq_s_of_s_eq_t heq
    have hp : G.p = 1 := by
      have := G.dg_mul_p; rw [hdg, ← heq] at this
      exact (Nat.mul_eq_left (by omega)).1 this
    have hq : G.q = 1 := by
      have := G.dg_mul_q; rw [hdg] at this
      exact (Nat.mul_eq_left (by omega)).1 this
    have hs2 : 2 ≤ G.s := by
      by_contra hc
      exact h (Prod.ext (by simp only; omega) (by simp only; omega))
    omega
  · -- Case 2: `s > t`
    omega
end SemigroupBetti.GenData
