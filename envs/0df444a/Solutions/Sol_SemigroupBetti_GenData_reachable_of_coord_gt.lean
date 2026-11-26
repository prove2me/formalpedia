-- Prove2me | solution 1 for SemigroupBetti.GenData.reachable_of_coord_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:06:06.3067+00:00
-- url     : https://prove2.me/submissions/4bee5916-eacf-4e45-af32-1d7fce535eef

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_sharesVar
public import Theorems.Thm_SemigroupBetti_GenData_nu_replace
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_bridge
public import Theorems.Thm_SemigroupBetti_GenData_n_le_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_pos_of_pos
public import Theorems.Thm_SemigroupBetti_GenData_nu_single
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp


attribute [local simp] SemigroupBetti.GenData.mem_fiber

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (z y : G.fiber d) {i : Fin 4} (hzi : G.n 3 < z.1 i) :
    (G.nabla d).Reachable z y := by
  have hz := G.mem_fiber.1 z.2
  have hy := G.mem_fiber.1 y.2
  -- some coordinate `j` of `y` is positive
  obtain ⟨j, hj⟩ : ∃ j, 0 < y.1 j := by
    by_contra hc; push Not at hc
    have : y.1 = 0 := funext fun k => Nat.le_zero.1 (hc k)
    rw [this, nu_zero] at hy
    have := G.nu_pos_of_pos (z := z.1) (i := i) (by omega)
    omega
  by_cases hzj : 0 < z.1 j
  · exact G.reachable_of_sharesVar ⟨j, hzj, hj⟩
  have hij : i ≠ j := by rintro rfl; omega
  have hnj := G.n_le_n_three j
  -- the bridge `b = z - nⱼ eᵢ + nᵢ eⱼ`
  have hle : Pi.single i (G.n j) ≤ z.1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [hk]
  have heq : G.nu (Pi.single i (G.n j)) = G.nu (Pi.single j (G.n i)) := by
    rw [G.nu_single, G.nu_single, mul_comm]
  refine G.reachable_of_bridge (z.1 - Pi.single i (G.n j) + Pi.single j (G.n i))
    ((G.nu_replace hle heq).trans hz) ⟨i, ?_, by omega⟩ ⟨j, ?_, hj⟩
  · simp [hij]; omega
  · simp [hij.symm, G.n_pos i]
end SemigroupBetti.GenData
