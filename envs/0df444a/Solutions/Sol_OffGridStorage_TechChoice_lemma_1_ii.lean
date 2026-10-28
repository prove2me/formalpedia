-- Prove2me | solution 1 for OffGridStorage.TechChoice.lemma_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:31:41.803372+00:00
-- url     : https://prove2.me/submissions/84cca33c-5a96-4b6b-bf8a-f21cb2a85491

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

open OffGridStorage.TechChoice in
theorem solution :
    (∀ p : Params, g0 p = g0ratio p.cQ (p.cK / p.e)) ∧
    (∀ cQ : ℝ, 0 < cQ → StrictMonoOn (g0ratio cQ) (Set.Ici 0)) := by
  refine ⟨fun p => ?_, fun cQ hcQ => ?_⟩
  · unfold g0 g0ratio
    rw [mul_div_assoc]
  · intro r hr s hs hrs
    unfold g0ratio
    have : Real.sqrt (cQ ^ 2 + 2 * cQ * r) ≤ Real.sqrt (cQ ^ 2 + 2 * cQ * s) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
