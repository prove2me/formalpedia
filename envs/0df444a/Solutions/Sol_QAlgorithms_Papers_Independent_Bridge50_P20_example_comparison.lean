-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P20.example_comparison
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:29:46.596843+00:00
-- url     : https://prove2.me/submissions/29abdcd4-c3ab-459d-83ad-2c3f54069afd

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

open QAlgorithms QAlgorithms.Entanglement

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Bridge50.P20 in
theorem solution (k : ℕ) (x lambda m : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hl : lambda ∈ Set.Icc (0 : ℝ) 1)
    (hm : 0 < m)
    (hden : 0 < (k : ℝ) * (dephasingSquashedBound x + dephasingRelativeValue x) +
      (dampingSquashedBound lambda + amplitudeValue lambda)) :
    exampleAdvantage k x lambda m =
      ((k : ℝ) * (dephasingSquashedBound x - dephasingRelativeValue x) +
        (dampingSquashedBound lambda - amplitudeValue lambda)) /
      ((k : ℝ) * (dephasingSquashedBound x + dephasingRelativeValue x) +
        (dampingSquashedBound lambda + amplitudeValue lambda)) := by
  unfold exampleAdvantage relativeAdvantage
  generalize dephasingSquashedBound x = a at hden ⊢
  generalize dephasingRelativeValue x = b at hden ⊢
  generalize dampingSquashedBound lambda = c at hden ⊢
  generalize amplitudeValue lambda = d at hden ⊢
  rw [show m * ((k : ℝ) * a + c) - m * ((k : ℝ) * b + d) =
      m * ((k : ℝ) * (a - b) + (c - d)) by ring,
    show m * ((k : ℝ) * a + c) + m * ((k : ℝ) * b + d) =
      m * ((k : ℝ) * (a + b) + (c + d)) by ring,
    mul_div_mul_left _ _ hm.ne']
