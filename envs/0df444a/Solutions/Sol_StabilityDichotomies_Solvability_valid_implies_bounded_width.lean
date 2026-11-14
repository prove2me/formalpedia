-- Prove2me | solution 1 for StabilityDichotomies.Solvability.valid_implies_bounded_width
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:22:34.0976+00:00
-- url     : https://prove2.me/submissions/1472682d-bfef-4b21-9c6f-6269ab904a50

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool) (hv : Valid Γ b) :
    BoundedWidth Γ := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro V _ I H hH
  refine ⟨fun _ => b, ?_⟩
  intro c hc
  exact hv c.rel.val c.rel.property

