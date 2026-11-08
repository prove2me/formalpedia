-- Prove2me | solution 1 for TucciCIT.eq_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:11:15.062007+00:00
-- url     : https://prove2.me/submissions/444705ff-9bf0-4759-8d39-517f39c09c4c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_TucciCIT_metaDensity

open QAlgorithms.Papers.Independent.Gap48.P20

open TucciCIT in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) :
    redistributionMarginal (metaDensity ψ) (fun p => p.2) (fun p => p.1) =
      Matrix.diagonal (fun q : X × Y => ψ q.1 q.2 * star (ψ q.1 q.2)) := by
  ext a b
  unfold redistributionMarginal metaDensity
  rw [Finset.sum_eq_single (a, a)]
  · rw [Finset.sum_eq_single (b, b)]
    · by_cases hab : a = b
      · subst hab
        simp [metaAmplitude]
      · simp [metaAmplitude, hab, Matrix.diagonal_apply_ne _ hab]
    · intro y _ hy
      obtain ⟨y1, y2⟩ := y
      by_cases hne : y1 = y2
      · rw [if_neg]
        rintro ⟨-, h2, -⟩
        have h2' : y2 = b := h2
        exact hy (Prod.ext (hne.trans h2') h2')
      · simp only [Matrix.of_apply, metaAmplitude, if_neg hne, star_zero, mul_zero, ite_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    obtain ⟨x1, x2⟩ := x
    by_cases hne : x1 = x2
    · rw [if_neg]
      rintro ⟨h1, -, -⟩
      have h1' : x2 = a := h1
      exact hx (Prod.ext (hne.trans h1') h1')
    · simp only [Matrix.of_apply, metaAmplitude, if_neg hne, zero_mul, ite_self]
  · intro h
    exact absurd (Finset.mem_univ _) h
