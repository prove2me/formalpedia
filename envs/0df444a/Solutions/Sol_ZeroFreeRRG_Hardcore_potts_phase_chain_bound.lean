-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_phase_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.631981+00:00
-- url     : https://prove2.me/submissions/f2688185-0a60-445b-8e3d-f1595698213d

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_one_edge_phase_change
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_discrete_phase_budget
import Theorems.Thm_ZeroFreeRRG_Hardcore_sequential_phase_bound
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {ι : Type} (S : Finset ι) (d n : ℕ) (hd : 3 ≤ d) (hn : n ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (f : ℕ → ℂ) (z a b : ℕ → ι → ℂ) (hfirst : f 0 ≠ 0)
    (ha : ∀ k < n, ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ a k i = 1+(t:ℂ)*(β-1))
    (hb : ∀ k < n, ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ b k i = 1+(t:ℂ)*(β-1))
    (hsector : ∀ k < n, (7/8:ℝ)*(∑ i ∈ S, ‖z k i‖) ≤ ‖∑ i ∈ S, z k i‖)
    (hold : ∀ k < n, f k = ∑ i ∈ S, z k i)
    (hnew : ∀ k < n, f (k+1) = ∑ i ∈ S, (b k i/a k i)*z k i) :
    f n ≠ 0 ∧ ‖f 0/(‖f 0‖:ℂ)-f n/(‖f n‖:ℂ)‖ < 1/2 := by
  classical
  let δ := ‖β-1‖
  let r := δ/((7/8:ℝ)*(1-δ))
  let C := (25/23:ℝ)*r
  have hδ : 0 ≤ δ := norm_nonneg _
  have hbudget := potts_discrete_phase_budget d hd δ hδ hβ
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hbudget.1
  have hstep (k : ℕ) (hk : k < n) (hf : f k ≠ 0) :
      f (k+1) ≠ 0 ∧ ‖f k/(‖f k‖:ℂ)-f (k+1)/(‖f (k+1)‖:ℂ)‖ ≤ C := by
    have hne : (∑ i ∈ S, z k i) ≠ 0 := by simpa [←hold k hk] using hf
    have hh := potts_one_edge_phase_change S (z k) (a k) (b k) d hd β hβ
      (ha k hk) (hb k hk) (hsector k hk) hne
    dsimp only at hh
    rw [←hold k hk,←hnew k hk] at hh
    exact hh
  have hnz (k : ℕ) (hk : k ≤ n) : f k ≠ 0 := by
    induction k with
    | zero => exact hfirst
    | succ k ih => exact (hstep k (by omega) (ih (by omega))).1
  let phase := fun k => f k/(‖f k‖:ℂ)
  have hchain : ‖phase 0-phase n‖ ≤ (n:ℝ)*C := by
    apply sequential_phase_bound phase n C
    intro k hk
    exact (hstep k hk (hnz k (by omega))).2
  have hnd : (n:ℝ) ≤ d := by exact_mod_cast hn
  have hless : (n:ℝ)*C < 1/2 := by
    have hle := mul_le_mul_of_nonneg_right hnd hC
    have hdC : (d:ℝ)*C < 1/2 := by simpa only [C,r,mul_assoc] using hbudget.2.2
    exact hle.trans_lt hdC
  exact ⟨hnz n (le_refl n),hchain.trans_lt hless⟩
