-- Prove2me | solution 1 for ZeroOneIALM.isCoercive_isBoundedBelow
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:03:41.364076+00:00
-- url     : https://prove2.me/submissions/74b53875-58b9-443f-894d-5b1cd6a442d0

import Mathlib
import Definitions.Def_ZeroOneIALM_Assumptions

open ZeroOneIALM in
theorem solution {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    (hcont : Continuous f) (hf : IsCoercive f) : IsBoundedBelow f := by
  obtain ⟨x, hx⟩ := hcont.exists_forall_le hf
  exact ⟨f x, by rintro _ ⟨y, rfl⟩; exact hx y⟩
