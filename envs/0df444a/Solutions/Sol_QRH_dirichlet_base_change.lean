-- Prove2me | solution 1 for QRH.dirichlet_base_change
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:15:18.358704+00:00
-- url     : https://prove2.me/submissions/bca5e93c-cbac-4110-9b15-11598ebc6b6d

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

open QRH

theorem solution (W : QRHWorld.{u}) (S : QRHSums W)
    (L : QRHLWorld W S)
    (hHecke : ∀ (ν : L.HeckeChi) (s : ℂ), 11 / 12 < s.re →
      s ≠ 1 ∨ ¬ L.IsTrivialH ν → L.Lk ν s ≠ 0)
    (χ : L.DirChi) (s : ℂ)
    (hs : 11 / 12 < s.re) (hχ : ¬ L.IsTrivialD χ ∨ s ≠ 1) :
    L.Ld χ s ≠ 0 := by
  intro h0
  have hs0 : 0 < s.re := by linarith
  by_cases h1 : s = 1
  · subst h1
    have hnt : ¬ L.IsTrivialD χ := by
      rcases hχ with h | h
      · exact h
      · exact (h rfl).elim
    have := hHecke (L.bc χ) 1 hs (Or.inr (fun h => hnt ((L.bc_triv_iff χ).1 h)))
    rw [L.bc_at_one, h0, zero_mul, zero_mul] at this
    exact this rfl
  · have := hHecke (L.bc χ) s hs (Or.inl h1)
    rw [L.bc_eq χ s hs0 h1, h0, zero_mul, zero_mul] at this
    exact this rfl
