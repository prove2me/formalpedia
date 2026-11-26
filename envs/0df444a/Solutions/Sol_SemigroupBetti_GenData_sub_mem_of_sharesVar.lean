-- Prove2me | solution 1 for SemigroupBetti.GenData.sub_mem_of_sharesVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:25.482991+00:00
-- url     : https://prove2.me/submissions/8482a05d-5ddd-45a6-9b51-7e2fd34bccda

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_X_mul_mono
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_add
public import Theorems.Thm_SemigroupBetti_GenData_nu_single
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
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
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {z z' : Fin 4 → ℕ} (hz : G.nu z = d) (hz' : G.nu z' = d) (h : SharesVar z z') :
    mono K z - mono K z' ∈ J := by
  obtain ⟨i, hi, hi'⟩ := h
  have key : ∀ y : Fin 4 → ℕ, 0 < y i → y = (y - Pi.single i 1) + Pi.single i 1 := by
    intro y hy; ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hdeg : ∀ y : Fin 4 → ℕ, 0 < y i → G.nu y = G.nu (y - Pi.single i 1) + G.n i := by
    intro y hy
    conv_lhs => rw [key y hy]
    rw [G.nu_add, G.nu_single, one_mul]
  rw [key z hi, key z' hi', ← X_mul_mono, ← X_mul_mono, ← mul_sub]
  refine J.mul_mem_left _ (IH (G.nu (z - Pi.single i 1)) ?_ _ _ rfl ?_)
  · have := hdeg z hi; have := G.n_pos i; omega
  · have := hdeg z hi; have := hdeg z' hi'; omega
end SemigroupBetti.GenData
