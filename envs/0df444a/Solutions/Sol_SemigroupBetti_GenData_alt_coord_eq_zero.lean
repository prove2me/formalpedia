-- Prove2me | solution 1 for SemigroupBetti.GenData.alt_coord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:26.888073+00:00
-- url     : https://prove2.me/submissions/c88108e1-78e5-45c3-95ce-bfbf8b4388bd

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_pair_le_nu
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_single
public import Theorems.Thm_SemigroupBetti_GenData_nu_sub
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_single_le_nu
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
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {i : Fin 4} {y : Fin 4 → ℕ} (hy : G.nu y = G.crit i * G.n i)
    (hne : y ≠ Pi.single i (G.crit i)) : y i = 0 := by
  by_contra hyi
  have hyi : 0 < y i := Nat.pos_of_ne_zero hyi
  have hni := G.n_pos i
  have hle : y i ≤ G.crit i := by
    have := G.single_le_nu y i
    rw [hy] at this
    exact Nat.le_of_mul_le_mul_right this hni
  rcases hle.lt_or_eq with hlt | heq
  · -- `v = y - yᵢ eᵢ` is an alternative for `r = cᵢ - yᵢ < cᵢ`
    have hsub : Pi.single i (y i) ≤ y := by
      intro k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    have hnu := G.nu_sub hsub
    rw [G.nu_single, hy] at hnu
    have hcand : G.IsCritCand i (G.crit i - y i) := by
      rw [isCritCand_iff]
      refine ⟨by omega, y - Pi.single i (y i), ?_, ?_⟩
      · rw [Nat.sub_mul]; omega
      · intro h
        have := congrFun h i
        simp at this; omega
    exact Nat.find_min (G.crit_exists i) (show G.crit i - y i < G.crit i by omega) hcand
  · -- `yᵢ = cᵢ` forces `y = cᵢ eᵢ`
    apply hne
    funext k
    by_cases hk : k = i
    · subst hk; simp [heq]
    · have h2 := G.pair_le_nu y hk
      rw [hy, heq] at h2
      have : y k * G.n k = 0 := by omega
      simp [hk, (G.n_pos k).ne'] at this ⊢; exact this
end SemigroupBetti.GenData
