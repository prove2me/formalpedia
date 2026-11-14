-- Prove2me | solution 1 for RvsCert.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T10:05:43.812992+00:00
-- url     : https://prove2.me/submissions/6e1aec0c-78a5-4d31-acfc-730ac18bcadb

import Theorems.Thm_RvsCert_lemma_4_hard_input
import Definitions.Def_RvsCert_C0

open RvsCert

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c * (n : ℝ) ^ 2 ≤ (C0 (champion n) : ℝ) := by
  refine ⟨1 / 2, by norm_num, fun n hn => ?_⟩
  obtain ⟨hzero, hcert⟩ := lemma_4_hard_input n hn
  -- The least certificate size at the all-`false` input is attained.
  have hne : {k : ℕ | ∃ S : Finset (Idx n),
      IsCertificate (champion n) (fun _ => false) S ∧ S.card = k}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, fun y hy => by
      have : y = fun _ => false := funext fun i => hy i (Finset.mem_univ i)
      rw [this], rfl⟩
  obtain ⟨S, hS, hScard⟩ := Nat.sInf_mem hne
  have hcertAt : (n : ℝ) ^ 2 / 2 < (certAt (champion n) (fun _ => false) : ℝ) := by
    have := hcert S hS
    unfold certAt
    rw [← hScard]
    exact this
  -- `C0` dominates the certificate complexity at any `0`-input.
  have hle : certAt (champion n) (fun _ => false) ≤ C0 (champion n) := by
    unfold C0
    have := Finset.le_sup (f := fun x : Idx n → Bool =>
      if champion n x = false then certAt (champion n) x else 0) (Finset.mem_univ (fun _ => false))
    simpa [hzero] using this
  have : (certAt (champion n) (fun _ => false) : ℝ) ≤ (C0 (champion n) : ℝ) := by
    exact_mod_cast hle
  linarith
