-- Prove2me | solution 1 for VanderbeiLP.Simplex.nonterminating_implies_cycling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:30:36.524793+00:00
-- url     : https://prove2.me/submissions/3388be52-0240-4a10-826f-b7ea7eecf927

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_PivotRules

set_option autoImplicit false

open VanderbeiLP.Simplex in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (D : ℕ → Dictionary A) (h0 : (D 0).IsFeasible b)
    (hstep : ∀ t, Dictionary.IsSimplexPivot b c (D t) (D (t + 1))) :
    ∃ s t, s < t ∧ D s = D t := by
  have hinj : Function.Injective (fun E : Dictionary A => E.B) := by
    rintro ⟨B1, h1, l1⟩ ⟨B2, h2, l2⟩ h
    simp only at h
    subst h
    rfl
  haveI : Finite (Dictionary A) := Finite.of_injective _ hinj
  obtain ⟨x, y, hne, hxy⟩ := Finite.exists_ne_map_eq_of_infinite D
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨x, y, h, hxy⟩
  · exact ⟨y, x, h, hxy.symm⟩
