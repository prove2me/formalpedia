-- Prove2me | solution 1 for Pseudorandom.pE_upper_tail_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:37.128782+00:00
-- url     : https://prove2.me/submissions/2c296ca4-ef9b-4318-bbc2-e4d850ccc31d

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Theorems.Thm_Pseudorandom_pE_tail_le_of_lam_fin

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
namespace Pseudorandom
theorem _root_.solution {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set V := ∑ i, q i * c i ^ 2 with hVdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => (sum_nonneg fun a _ => hP.1 i a).trans (hq i)
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => mul_nonneg (hq0 i) (sq_nonneg _)
  have hcL : ∀ i, c i ≤ L := fun i => (hc i).2
  rcases hV0.lt_or_eq with hV | hV
  · have hD : 0 < V + L * t := by positivity
    set lam := t / (V + L * t)
    have hlam : 0 ≤ lam := by positivity
    have hlamL : lam * L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hD]; nlinarith
    refine (pE_tail_le_of_lam_fin P hP f c q R L lam t hcL hf hfR hq hlam hlamL).trans
      (le_of_eq (congrArg Real.exp ?_))
    have h1 : 1 - lam * L = V / (V + L * t) := by
      simp only [lam]; field_simp; ring
    rw [h1]
    simp only [lam]
    field_simp
    ring
  · have hlamL : 1 / (2 * L) * L < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    refine (pE_tail_le_of_lam_fin P hP f c q R L (1 / (2 * L)) t hcL hf hfR hq
      (by positivity) hlamL).trans (le_of_eq (congrArg Real.exp ?_))
    rw [← hVdef, ← hV]
    field_simp
    ring
end Pseudorandom
