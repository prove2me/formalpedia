-- Prove2me | solution 1 for RemanProcure.Noncongestive.lemma_1_vstar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:19:48.713665+00:00
-- url     : https://prove2.me/submissions/89417c32-6c72-4377-a46f-67711a1068c6

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model
import Theorems.Thm_RemanProcure_Noncongestive_eq_1
import Theorems.Thm_RemanProcure_Noncongestive_lemma_1_preserve

open RemanProcure.Noncongestive

theorem solution {K : ℕ} (P : Params K) (hP : Standing P) : VA P (vstar P) := by
  have hconv := (eq_1 P hP).1
  set f : ℕ → (Fin K → ℕ) → ℝ := fun n => (T P)^[n] 0 with hf
  have hlim : ∀ y, Filter.Tendsto (fun n => f n y) Filter.atTop (nhds (vstar P y)) := hconv
  have hVA0 : VA P (0 : (Fin K → ℕ) → ℝ) := by
    obtain ⟨-, -, -, hrm, -, -, -, hrc, -⟩ := hP
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x w; simp; exact (hrc w).le
    · intro x q w hqw; simp; exact hrm hqw.le
    · intro x d l q _ _; simp
    · intro x d l q w _ _ _; simp
    · intro x l q _; simp
    · intro x l q w _ _; simp
  have hVAn : ∀ n, VA P (f n) := by
    intro n
    induction n with
    | zero => simpa [hf] using hVA0
    | succ n ih =>
      have := lemma_1_preserve P hP (f n) ih
      simpa [hf, Function.iterate_succ_apply'] using this
  -- helper: sums over filters tend
  have hsum : ∀ (s : Finset (Fin K)) (y : Fin K → (Fin K → ℕ)),
      Filter.Tendsto (fun n => ∑ i ∈ s, P.p i * f n (y i)) Filter.atTop
        (nhds (∑ i ∈ s, P.p i * vstar P (y i))) :=
    fun s y => tendsto_finset_sum _ fun i _ => (hlim _).const_mul _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x w
    exact le_of_tendsto_of_tendsto' ((hlim _).add_const _) ((hlim _).add_const _)
        (fun n => (hVAn n).1 x w)
  · intro x q w hqw
    exact le_of_tendsto_of_tendsto' ((hlim _).add_const _) ((hlim _).add_const _)
      (fun n => (hVAn n).2.1 x q w hqw)
  · intro x d l q h1 h2
    exact le_of_tendsto_of_tendsto' ((hlim _).sub (hlim _)) ((hlim _).sub (hlim _))
      (fun n => (hVAn n).2.2.1 x d l q h1 h2)
  · intro x d l q w h1 h2 h3
    exact le_of_tendsto_of_tendsto' ((hlim _).sub (hlim _)) ((hlim _).sub (hlim _))
      (fun n => (hVAn n).2.2.2.1 x d l q w h1 h2 h3)
  · intro x l q h1
    exact le_of_tendsto_of_tendsto'
      (((hsum _ (fun _ => x + e l)).add (hsum _ (fun i => x + e i))).sub (hlim _))
      (((hsum _ (fun _ => x + e q + e l)).add (hsum _ (fun i => x + e q + e i))).sub (hlim _))
      (fun n => (hVAn n).2.2.2.2.1 x l q h1)
  · intro x l q w h1 h2
    exact le_of_tendsto_of_tendsto'
      (((hsum _ (fun _ => x + e w + e l)).add (hsum _ (fun i => x + e w + e i))).sub (hlim _))
      (((hsum _ (fun _ => x + e q + e l)).add (hsum _ (fun i => x + e q + e i))).sub (hlim _))
      (fun n => (hVAn n).2.2.2.2.2 x l q w h1 h2)
