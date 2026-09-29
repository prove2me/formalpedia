-- Prove2me | solution 1 for Schanuel.gelfond_schneider
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T18:56:30.783825+00:00
-- url     : https://prove2.me/submissions/5dca33ff-6134-44e2-b303-8dce187f6a47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms

theorem solution (b l : ℂ) (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ (q : ℂ))
    (hl : IsAlgebraic ℚ (Complex.exp l)) (hl0 : l ≠ 0) :
    Transcendental ℚ (Complex.exp (b * l)) := by
  intro halg
  have hlin : LinearIndependent ℚ ![l, b * l] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : ((s : ℂ) + (t : ℂ) * b) * l = 0 := by
      have : (s : ℂ) * l + (t : ℂ) * (b * l) = 0 := by
        simpa [Rat.smul_def] using hst
      linear_combination this
    have h2 : (s : ℂ) + (t : ℂ) * b = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hl0
    have ht : t = 0 := by
      by_contra ht
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      refine hbq (-s / t) ?_
      push_cast
      field_simp
      linear_combination h2
    subst ht
    have hs : (s : ℂ) = 0 := by simpa using h2
    exact ⟨by exact_mod_cast hs, rfl⟩
  have hne := Schanuel.baker_linear_forms_in_logarithms 2 ![l, b * l] hlin
    (by
      intro i
      fin_cases i
      · exact hl
      · exact halg)
    0 ![-b, 1] isAlgebraic_zero
    (by
      intro i
      fin_cases i
      · exact hb.neg
      · exact isAlgebraic_one)
    (Or.inr ⟨1, by simp⟩)
  apply hne
  simp [Fin.sum_univ_two]
