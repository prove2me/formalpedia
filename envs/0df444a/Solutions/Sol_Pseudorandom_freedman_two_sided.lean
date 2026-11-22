-- Prove2me | solution 1 for Pseudorandom.freedman_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:28.698234+00:00
-- url     : https://prove2.me/submissions/1d4f6e07-751d-4aae-9ca2-6801346107fd

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_freedman_upper
public import Theorems.Thm_Pseudorandom_IsExposureMartingale_neg
public import Theorems.Thm_Pseudorandom_CoordGap_neg
public import Theorems.Thm_Pseudorandom_CoordRare_neg
public import Theorems.Thm_Pseudorandom_pProb_mono
public import Theorems.Thm_Pseudorandom_pProb_or_le


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (hG : ∀ k, Adapted k (G k)) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (hinc : ∀ (i : Fin n) ω, Alive G i ω → ∀ a, P i a ≠ 0 →
      |X (i + 1) (Function.update ω i a) - X i ω| ≤ C)
    (hacc : ∀ (i : Fin n) ω, Alive G i ω →
      ∑ j : Fin n with j ≤ i, condAbsInc P X j ω ≤ s) :
    pProb P (fun ω => lam ≤ |X n ω - X 0 ω| ∧ ∀ i : Fin n, G i ω) ≤
      2 * Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by
  have h1 := freedman_upper hP hX hG C s lam hC hs hlam hinc hacc
  have h2 := freedman_upper hP hX.neg hG C s lam hC hs hlam
    (fun i ω h a ha => by
      have := hinc i ω h a ha
      rw [← abs_neg]; convert this using 2; ring)
    (fun i ω h => by
      have := hacc i ω h
      refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) this
      unfold condAbsInc
      refine sum_congr rfl fun a _ => ?_
      rw [← abs_neg]; congr 2; ring)
  refine le_trans (pProb_mono hP (T := fun ω => (lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) ∨
    (lam ≤ -X n ω - -X 0 ω ∧ ∀ i : Fin n, G i ω)) fun ω h => ?_) ?_
  · rcases le_abs'.mp h.1 with h' | h'
    · right; exact ⟨by linarith, h.2⟩
    · left; exact ⟨h', h.2⟩
  · refine (pProb_or_le hP _ _).trans ?_
    linarith
end Pseudorandom
