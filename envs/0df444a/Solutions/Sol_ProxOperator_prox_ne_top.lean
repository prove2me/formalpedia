-- Prove2me | solution 1 for ProxOperator.prox_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:38.830953+00:00
-- url     : https://prove2.me/submissions/2be510cb-2ec1-46a6-9260-39b86eef625a

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

set_option autoImplicit false

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 38-45

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hP : ThreeOpSplitting.ConvexRates.IsProx γ f P) (x : H) :
    f (P x) ≠ ⊤ := by
  obtain ⟨hbot, ⟨x0, hx0⟩, _, _⟩ := hf
  intro htop
  have h1 := hP x x0
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hx0 (hbot x0), ← EReal.coe_add] at h1
  exact absurd h1 (not_le.2 (EReal.coe_lt_top _))
