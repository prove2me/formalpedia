-- Prove2me | solution 1 for ProcFlex.DMGI.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:47:10.154992+00:00
-- url     : https://prove2.me/submissions/36ec4ced-9c88-406b-a530-a0ac55157bc1

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model
import Theorems.Thm_ProcFlex_DMGI_theorem_2a
import Theorems.Thm_ProcFlex_DMGI_proposition_1

open ProcFlex.DMGI

theorem solution (k : ℕ) (hk : 1 ≤ k)
    (S : System (2 * k) (2 * k) 2) (hS : S.IsValid)
    (hC : ∀ j, S.C j = 1) (hcard : (S.s 1).card = k)
    (h : ℝ → (Fin 2 → ℝ) → ℝ)
    (hh : ∀ y, StrictMono (fun x => h x y))
    (hcont : ∀ A : Design (2 * k) (2 * k),
      ContinuousOn (f S h A) {d | ∀ i, 0 ≤ d i})
    (U : Set (Fin (2 * k) → ℝ)) (hU : IsPartwiseIndepSymmetric S U)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U)
    (πAL π : Equiv.Perm (Fin (2 * k))) (hAL : IsAlternate S πAL) :
    Rf S h (longChain π) U ≤ Rf S h (longChain πAL) U := by
  have hU0 : IsSymmetricAround S U 0 := by
    unfold IsSymmetricAround
    have : ((fun d => d - (0 : Fin (2 * k) → ℝ)) '' U) = U := by
      simp
    rw [this]; exact hU
  exact theorem_2a S hS (longChain πAL) (longChain π) h hh (hcont _) (hcont _)
    U 0 hU0 hUpos hUne hUc
    (fun K hK => proposition_1 k hk S hS hC hcard πAL π hAL K hK)
