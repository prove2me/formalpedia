-- Prove2me | solution 1 for QRH.quasi_riemann_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:16:42.812975+00:00
-- url     : https://prove2.me/submissions/cef8fc83-b193-4f82-be1e-54e8c591de71

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

open QRH

theorem solution (W : QRHWorld.{u}) (S : QRHSums W)
    (L : QRHLWorld W S)
    (hms : ∀ (ν : L.HeckeChi) (Wt : ℝ → ℂ) (θ ε : ℝ),
      0 < θ → θ ≤ 1 / 10 → 0 < ε →
      ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
        msSum W S (fun n => W.mu n * L.hcoef ν n) Wt (D ^ (1 + θ)) D (2 * D)
          ≤ k * D ^ (2 + θ + ε)) :
    (∀ (ν : L.HeckeChi) (s : ℂ), 11 / 12 < s.re →
        s ≠ 1 ∨ ¬ L.IsTrivialH ν → L.Lk ν s ≠ 0)
      ∧ (∀ (χ : L.DirChi) (s : ℂ), 11 / 12 < s.re →
        ¬ L.IsTrivialD χ ∨ s ≠ 1 → L.Ld χ s ≠ 0) := by
  have hH : ∀ (ν : L.HeckeChi) (s : ℂ), 11 / 12 < s.re →
      s ≠ 1 ∨ ¬ L.IsTrivialH ν → L.Lk ν s ≠ 0 := by
    intro ν s hs _ h0
    have hsav : MobiusSaving W S (fun n => W.mu n * L.hcoef ν n) (fun _ => 0) := by
      intro ε _
      refine ⟨0, fun D _ => ?_⟩
      simp [A1sum, Asum]
    have := L.mellin_identity ν (fun _ => 0) hsav s hs
    rw [h0, zero_mul, zero_mul] at this
    exact L.Wf_pos ν (fun _ => 0) s hs this.symm
  refine ⟨hH, ?_⟩
  intro χ s hs hχ h0
  have hs0 : 0 < s.re := by linarith
  by_cases h1 : s = 1
  · subst h1
    have hnt : ¬ L.IsTrivialD χ := by
      rcases hχ with h | h
      · exact h
      · exact (h rfl).elim
    have := hH (L.bc χ) 1 hs (Or.inr (fun h => hnt ((L.bc_triv_iff χ).1 h)))
    rw [L.bc_at_one, h0, zero_mul, zero_mul] at this
    exact this rfl
  · have := hH (L.bc χ) s hs (Or.inl h1)
    rw [L.bc_eq χ s hs0 h1, h0, zero_mul, zero_mul] at this
    exact this rfl
