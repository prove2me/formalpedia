-- Prove2me | solution 1 for ProxOperator.ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:19:06.445871+00:00
-- url     : https://prove2.me/submissions/9fe4a278-ed05-4d48-bf51-bf03c3496df3

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

-- carved verbatim out of submission e3454a9c-3502-4c6b-9794-7eebefc4332c, lines 90-98

section
open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f) (hP : IsProx γ f P)
    (x : H) : f (P x) ≠ ⊤ := by
  obtain ⟨hbot, ⟨x0, hx0⟩, _, _⟩ := hf
  intro htop
  have h1 := hP x x0
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hx0 (hbot x0), ← EReal.coe_add] at h1
  exact absurd h1 (not_le.2 (EReal.coe_lt_top _))

end
