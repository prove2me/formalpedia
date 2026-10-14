-- Prove2me | solution 1 for SennottDP.SEN.prop_B_6_bounded_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:49:59.470043+00:00
-- url     : https://prove2.me/submissions/65e95a6c-2b41-4995-88bb-1f28c808db94

import Mathlib

open Filter Topology


namespace SennottDP.SEN

theorem b6_core {S : Type} [Countable S] (L M : S → ℝ)
    (hL : ∀ i, 0 ≤ L i) (hM : ∀ i, 0 ≤ M i) (u : ℕ → S → ℝ)
    (hu : ∀ r i, -L i ≤ u r i ∧ u r i ≤ M i) :
    ∃ rk : ℕ → ℕ, StrictMono rk ∧ ∃ w : S → ℝ, (∀ i, -L i ≤ w i ∧ w i ≤ M i) ∧
      ∀ i, Tendsto (fun k => u (rk k) i) atTop (𝓝 (w i)) := by
  have hc : IsCompact (Set.pi Set.univ (fun i => Set.Icc (-L i) (M i))) :=
    isCompact_univ_pi (fun i => isCompact_Icc)
  obtain ⟨w, hw, φ, hφ, ht⟩ := hc.tendsto_subseq (x := u) (fun r => by
    intro i _; exact hu r i)
  refine ⟨φ, hφ, w, fun i => hw i (Set.mem_univ _), fun i => ?_⟩
  exact (continuous_apply i).continuousAt.tendsto.comp ht

end SennottDP.SEN

open SennottDP.SEN


theorem solution {S : Type} [Countable S] (L M : S → ℝ)
    (hL : ∀ i, 0 ≤ L i) (hM : ∀ i, 0 ≤ M i) (u : ℕ → S → ℝ)
    (hu : ∀ r i, -L i ≤ u r i ∧ u r i ≤ M i) :
    ∃ rk : ℕ → ℕ, StrictMono rk ∧ ∃ w : S → ℝ, (∀ i, -L i ≤ w i ∧ w i ≤ M i) ∧
      ∀ i, Tendsto (fun k => u (rk k) i) atTop (𝓝 (w i)) := by
  exact b6_core L M hL hM u hu
