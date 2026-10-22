-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.sargAcceptance
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:15:28.221747+00:00
-- url     : https://prove2.me/submissions/272e39e5-bcef-4338-a985-b314a0e59f45

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(53)–(54), footnote 58, PDF p.32. Conditional error is asserted only
for a nonempty detection class; both source basis assumptions are in sargAccepted. -/
theorem solution (nu pa f e : ℝ) (hnu : 0 ≤ nu)
    (hpa : pa ∈ Set.Icc (0 : ℝ) 1) (hf : f ∈ Set.Icc (0 : ℝ) 1)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    sargAccepted nu pa f e = (nu/2)*pa*f*(1/2+e) ∧
    sargWrong nu pa f e = (nu/2)*pa*f*e ∧
    (0 < nu*pa*f → sargWrong nu pa f e/sargAccepted nu pa f e = e/(1/2+e)) ∧
    (∀ e2 : ℝ, e2 ∈ Set.Icc (0 : ℝ) 1 → e ≤ e2 →
      sargAccepted nu pa f e ≤ sargAccepted nu pa f e2) := by
  refine ⟨by unfold sargAccepted; ring, by unfold sargWrong; ring, fun h => ?_, fun e2 _ h2 => ?_⟩
  · unfold sargWrong sargAccepted
    have h1 : (0:ℝ) < 1/2 + e := by linarith [he.1]
    have hne : nu * pa * f ≠ 0 := h.ne'
    have h2 : nu * pa * f * ((1/2)*e + (1/2)*(1/2)) = nu * pa * f * ((1/2)*(1/2+e)) := by ring
    rw [h2, mul_div_mul_left _ _ hne]
    field_simp
  · unfold sargAccepted
    have : 0 ≤ nu * pa * f := mul_nonneg (mul_nonneg hnu hpa.1) hf.1
    nlinarith



