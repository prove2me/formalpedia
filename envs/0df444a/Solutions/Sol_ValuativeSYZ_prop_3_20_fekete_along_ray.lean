-- Prove2me | solution 1 for ValuativeSYZ.prop_3_20_fekete_along_ray
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:40:06.517138+00:00
-- url     : https://prove2.me/submissions/c10132bb-4516-4e5f-991c-620ac3f66df2

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! 37f97467 ValuativeSYZ.prop_3_20_fekete_along_ray (Fekete's lemma along a ray).

Route. `u m := F (m * l) (m • q)` is subadditive by `hsub`; `u m / m` is bounded below by
`min (-C) 0` from `hC`. Mathlib's `Subadditive.tendsto_lim` gives `u m / m → hS.lim`, so
dividing by `l` gives the limit `g := hS.lim / l`, and `Subadditive.lim_le_div` gives the bound. -/

set_option autoImplicit false

open MeasureTheory



open ValuativeSYZ in
theorem solution {n : ℕ} (F : ℕ → (Fin n → ℤ) → ℝ)
    (hsub : ∀ (l l' : ℕ) (q q' : Fin n → ℤ), F (l + l') (q + q') ≤ F l q + F l' q')
    (l : ℕ) (hl : 0 < l) (q : Fin n → ℤ) (C : ℝ)
    (hC : ∀ m : ℕ, -(C * m) ≤ F (m * l) (m • q)) :
    ∃ g : ℝ, Filter.Tendsto (fun m : ℕ => F (m * l) (m • q) / (m * l)) Filter.atTop (nhds g) ∧
      ∀ m : ℕ, 0 < m → g ≤ F (m * l) (m • q) / (m * l) := by
  set u : ℕ → ℝ := fun m => F (m * l) (m • q) with hu
  have hS : Subadditive u := by
    intro a b
    simp only [hu]
    rw [add_mul, add_smul]
    exact hsub _ _ _ _
  have hbdd : BddBelow (Set.range fun m : ℕ => u m / m) := by
    refine ⟨min (-C) 0, ?_⟩
    rintro _ ⟨m, rfl⟩
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; simp
    · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have : -C ≤ u m / m := by
        rw [le_div_iff₀ hmR]
        have := hC m
        simp only [hu]
        linarith
      exact le_trans (min_le_left _ _) this
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have key : ∀ m : ℕ, F (m * l) (m • q) / ((m : ℝ) * l) = (u m / m) / l := by
    intro m
    simp only [hu]
    rw [div_div]
  refine ⟨hS.lim / l, ?_, ?_⟩
  · have h1 := (hS.tendsto_lim hbdd).div_const (l : ℝ)
    refine h1.congr' (Filter.Eventually.of_forall fun m => ?_)
    exact (key m).symm
  · intro m hm
    rw [key m]
    exact div_le_div_of_nonneg_right (hS.lim_le_div hbdd (Nat.pos_iff_ne_zero.mp hm)) hlR.le


