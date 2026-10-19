-- Prove2me | solution 1 for SubsetShrink.Events.F_subset_E
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:49:07.981411+00:00
-- url     : https://prove2.me/submissions/1c67f62b-a46e-4ab8-aa72-3b8aeaee8f20

/-
  DS8 target: SubsetShrink.Events.F_subset_E
  theorem_id 4218f4d4-bd18-4289-80cf-8991e8d22843 (Open milestone of mission
  b3f99725-2ef4-482e-8cc0-ff264fd019ff).

  Combines the two now-available platform theorems
    * SubsetShrink.Events.eq_28 (the sorted-ℓ1 bound), and
    * SubsetShrink.Events.eq_27 (the ℓ2(Xu) bound for unit columns),
  to get, for every u with l0 u ≤ s, the threshold bound of F with δ₀ = s/(2ep),
  and hence F X σ δ₀ ⊆ E X σ s.
-/
import Mathlib
import Definitions.Def_SubsetShrink_Events_Model
import Theorems.Thm_SubsetShrink_Events_eq_27
import Theorems.Thm_SubsetShrink_Events_eq_28

open MeasureTheory ProbabilityTheory
open SubsetShrink.Events
open scoped BigOperators

theorem solution {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (hs : 1 ≤ s) (hsp : s ≤ p) :
    (∀ u : Fin p → ℝ, l0 u ≤ s →
      (4 + Real.sqrt 2) * σ * max (sortedSum u)
          (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) *
          l2 u) ∧
      F X σ ((s : ℝ) / (2 * Real.exp 1 * p)) ⊆ E X σ s := by
  have hc : 0 ≤ (4 + Real.sqrt 2) * σ := mul_nonneg (by positivity) hσ.le
  have key : ∀ u : Fin p → ℝ, l0 u ≤ s →
      max (sortedSum u)
          (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u)) ≤
        Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u := by
    intro u hu
    apply max_le
    · exact le_trans (eq_28 hs hsp u hu).1 (eq_28 hs hsp u hu).2
    · exact (eq_27 X hX hs hsp u hu).2.2
  constructor
  · intro u hu
    calc (4 + Real.sqrt 2) * σ * max (sortedSum u)
            (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u))
        ≤ (4 + Real.sqrt 2) * σ *
            (Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u) :=
          mul_le_mul_of_nonneg_left (key u hu) hc
      _ = (4 + Real.sqrt 2) * σ * Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) *
            l2 u := by ring
  · intro ε hε u hu
    have h1 : dot ε (X.mulVec u) ≤ (4 + Real.sqrt 2) * σ *
        max (sortedSum u)
          (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u)) :=
      hε u
    have h2 : (4 + Real.sqrt 2) * σ *
        max (sortedSum u)
          (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) *
          l2 u := by
      calc (4 + Real.sqrt 2) * σ * max (sortedSum u)
              (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u))
          ≤ (4 + Real.sqrt 2) * σ *
              (Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u) :=
            mul_le_mul_of_nonneg_left (key u hu) hc
        _ = (4 + Real.sqrt 2) * σ * Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) *
              l2 u := by ring
    exact le_trans h1 h2
