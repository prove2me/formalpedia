-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.summable_and_tsum_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:48.468298+00:00
-- url     : https://prove2.me/submissions/91b56045-ea68-472a-9e31-efaa5310a2e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_LatSumPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open Module
namespace ReciprocityTheory.ThetaSummability.Est
theorem _root_.solution {α : Type*} {q : ℕ} (f : Fin q → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin q → α => ∏ i, f i (x i)) ∧
      ∑' x : Fin q → α, ∏ i, f i (x i) = ∏ i, ∑' a, f i a := by
  induction q with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨Summable.of_finite, by rw [tsum_const, Nat.card_unique, one_smul]⟩
  | succ q ih =>
    obtain ⟨hs, ht⟩ := ih (fun i => f i.succ) (fun i => hf0 i.succ) (fun i => hf i.succ)
    obtain ⟨e, he⟩ : ∃ e : α × (Fin q → α) ≃ (Fin (q + 1) → α),
        ∀ p, e p = (Fin.cons p.1 p.2 : Fin (q + 1) → α) :=
      ⟨Fin.consEquiv (fun _ : Fin (q + 1) => α), fun p => rfl⟩
    have key : ∀ p : α × (Fin q → α), ∏ i, f i (e p i) = f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
      intro p
      rw [he, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hprod : Summable (fun p : α × (Fin q → α) => f 0 p.1 * ∏ i, f i.succ (p.2 i)) := by
      have h1 : (0 : α → ℝ) ≤ f 0 := Pi.le_def.mpr fun a => hf0 0 a
      have h2 : (0 : (Fin q → α) → ℝ) ≤ fun x => ∏ i, f i.succ (x i) :=
        Pi.le_def.mpr fun x => Finset.prod_nonneg fun i _ => hf0 _ _
      have hs0 : Summable (fun x : Fin q → α => ∏ i, f i.succ (x i)) := hs
      have hf00 : Summable (f 0) := hf 0
      have := Summable.mul_of_nonneg hf00 hs0 h1 h2
      exact this
    have hs' : Summable (fun p : α × (Fin q → α) => ∏ i, f i (e p i)) :=
      hprod.congr fun p => (key p).symm
    refine ⟨(e.summable_iff (f := fun x : Fin (q + 1) → α => ∏ i, f i (x i))).mp hs', ?_⟩
    calc ∑' x : Fin (q + 1) → α, ∏ i, f i (x i)
        = ∑' p : α × (Fin q → α), ∏ i, f i (e p i) := (e.tsum_eq (fun x => ∏ i, f i (x i))).symm
      _ = ∑' p : α × (Fin q → α), f 0 p.1 * ∏ i, f i.succ (p.2 i) := tsum_congr key
      _ = (∑' a, f 0 a) * ∑' x : Fin q → α, ∏ i, f i.succ (x i) := (Summable.tsum_mul_tsum (hf 0) hs hprod).symm
      _ = ∏ i, ∑' a, f i a := by rw [ht, Fin.prod_univ_succ]
end ReciprocityTheory.ThetaSummability.Est
