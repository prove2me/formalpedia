-- Prove2me | solution 1 for Pseudorandom.pE_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:43.964684+00:00
-- url     : https://prove2.me/submissions/2976ae8c-19b4-46cf-b979-c58913e0215c

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_prod

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (i : ι) (g : α → ℝ) :
    pE P (fun ω => g (ω i)) = ∑ a, P i a * g a := by
  have h := pE_prod (P := P) (fun j a => if j = i then g a else 1)
  have hl : (fun ω : ι → α => ∏ j, (if j = i then g (ω j) else 1)) = fun ω => g (ω i) := by
    funext ω
    rw [prod_ite_eq' univ i (fun j => g (ω j))]
    simp
  simp only [hl] at h
  rw [h, prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj, hP.2 j]
  · simp
end Pseudorandom
