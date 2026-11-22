-- Prove2me | solution 1 for Pseudorandom.pE_resample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:44.109819+00:00
-- url     : https://prove2.me/submissions/f6cb4fda-e8f9-4818-be62-c85ae9d92a9d

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (i : ι) (g : (ι → α) → ℝ) :
    pE P (fun ω => ∑ a, P i a * g (Function.update ω i a)) = pE P g := by
  classical
  unfold pE pw
  set e := Equiv.funSplitAt i α
  have key : ∀ F : (ι → α) → ℝ, ∑ ω, F ω = ∑ x : α × ({j // j ≠ i} → α), F (e.symm x) :=
    fun F => (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
  have hpw : ∀ x : α × ({j // j ≠ i} → α),
      ∏ j, P j (e.symm x j) = P i x.1 * ∏ j : {j // j ≠ i}, P j (x.2 j) := by
    intro x
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    congr 1
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · refine Fintype.prod_congr _ _ fun j => ?_
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  have hupd : ∀ (x : α × ({j // j ≠ i} → α)) (a : α),
      Function.update (e.symm x) i a = e.symm (a, x.2) := by
    intro x a
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [key, key]
  simp_rw [hpw, hupd, Fintype.sum_prod_type]
  rw [sum_comm (γ := α)]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_mul, ← sum_mul, hP.2 i, one_mul, mul_sum]
  exact sum_congr rfl fun a _ => by ring
end Pseudorandom
