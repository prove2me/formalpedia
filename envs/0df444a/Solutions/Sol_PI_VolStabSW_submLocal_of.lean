-- Prove2me | solution 1 for PI.VolStabSW.submLocal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:05.0608+00:00
-- url     : https://prove2.me/submissions/2176fc88-304a-44c1-8308-1bb5f6176f11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology
namespace PI.VolStabSW
theorem _root_.solution (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by
  intro n m μ ν hμ hν f hf x0 hx0
  obtain ⟨N, hN, hxN, A, hA, hG⟩ := h2 n m μ hμ f hf x0 hx0
  refine ⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩
  obtain ⟨G, hGc, hGs, hGe⟩ := hG φ hc hs hφ
  obtain ⟨g, hgc, hg⟩ := h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)
  refine ⟨g, hgc, fun S hS => ?_⟩
  have := hg S hS
  simp only [Set.image_id] at this ⊢
  rw [hGe S hS, this]
end PI.VolStabSW
