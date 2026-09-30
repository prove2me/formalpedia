-- Prove2me | solution 1 for SupplyChainTheory.clark_scarf_sequential
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T17:00:18.734992+00:00
-- url     : https://prove2.me/submissions/2094ed69-1c7d-44db-b4db-8353e6a108ba

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

/-! Disproof of 73d61815 `SupplyChainTheory.clark_scarf_sequential`.

The statement allows `N = 0`. Then `CSSequential 0 h p D Sstar` quantifies over
`j ∈ Finset.Icc 1 0 = ∅` and is vacuous, so `Sstar` is unconstrained, while the conclusion
compares `csG … Sstar 0 (Sstar 0)` with `csG … S 0 (S 0)` at two DIFFERENT points `Sstar 0`
and `S 0` of the same function (`csBar _ 0` does not depend on the base-stock vector).
Take `h ≡ 1`, `p = 0`, `D ≡ dirac 0`, `Sstar ≡ 1`, `S ≡ 0`: then
`csG … Sstar 0 (Sstar 0) = 1 * 1 + 0 = 1` and `csG … S 0 (S 0) = 1 * 0 + 0 = 0`,
and `1 ≤ 0` fails. -/

set_option autoImplicit false

open MeasureTheory SupplyChainTheory in
theorem solution : ¬ (∀ (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar),
    ∀ S : ℕ → ℝ, csG N h p D Sstar N (Sstar N) ≤ csG N h p D S N (S N)) := by
  intro hT
  have hint : ∀ j : ℕ, Integrable (fun x : ℝ => x) ((fun _ : ℕ => Measure.dirac (0 : ℝ)) j) :=
    fun _ => integrable_dirac (by simp)
  have hseq : CSSequential 0 (fun _ => (1 : ℝ)) 0 (fun _ => Measure.dirac (0 : ℝ))
      (fun _ => (1 : ℝ)) := by
    intro j hj
    simp at hj
  have key := hT 0 (fun _ => (1 : ℝ)) 0 (fun _ => Measure.dirac (0 : ℝ)) hint
    (fun _ => zero_le_one) le_rfl (fun _ => (1 : ℝ)) hseq (fun _ => (0 : ℝ))
  have e0 : ∀ (S : ℕ → ℝ) (x : ℝ),
      csBar 0 (fun _ => (1 : ℝ)) 0 (fun _ => Measure.dirac (0 : ℝ)) S 0 x
        = (0 + localHolding 0 (fun _ => (1 : ℝ)) 1) * max (-x) 0 := fun _ _ => rfl
  simp only [csG, csHat, integral_dirac] at key
  rw [e0, e0] at key
  norm_num at key
