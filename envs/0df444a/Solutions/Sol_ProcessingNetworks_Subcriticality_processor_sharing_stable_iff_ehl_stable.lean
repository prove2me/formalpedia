-- Prove2me | solution 1 for ProcessingNetworks.Subcriticality.processor_sharing_stable_iff_ehl_stable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:16:46.170814+00:00
-- url     : https://prove2.me/submissions/72c842cd-4151-4a4a-9316-442c8fda486b

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Subcriticality_PSNetworkStability

set_option autoImplicit false

open ProcessingNetworks.Subcriticality MeasureTheory ProcessingNetworks.Stability in
theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (jump : Xstate → PMF Xstate) (rate : Xstate → ℝ) (M : MarkovRepresentation Xstate I J N Z)
    (h_same_generator : M.jump = jump ∧ M.rate = rate) :
    IsPSStable jump rate ↔ IsStable M := by
  obtain ⟨h1, h2⟩ := h_same_generator
  show PositiveRecurrent jump rate ↔ PositiveRecurrent M.jump M.rate
  rw [h1, h2]
