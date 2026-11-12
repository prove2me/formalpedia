-- Prove2me | solution 1 for RH.Transport.PhysicalAnalytic.dirichlet_of_hecke_at_boundary
-- status  : ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-11T16:22:42.821216+00:00
-- url     : https://prove2.me/submissions/150cac39-aa4e-4dfd-98e9-4a0cc7d96d99

import Theorems.Thm_OAI_SevenEighths_HeckeDirichlet_exists_norm_base_change_factorization

open scoped DirichletCharacter
open OAI.SevenEighths

theorem solution {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), B < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : B < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    exact (not_lt_of_ge hB) hs
  obtain ⟨η, _hcoeff, hfactor⟩ :=
    HeckeDirichlet.exists_norm_base_change_factorization χ
  have hHecke := hH η s hs (Or.inl hs1)
  rw [hfactor s hs0 hs1] at hHecke
  exact (mul_ne_zero_iff.mp hHecke).1
