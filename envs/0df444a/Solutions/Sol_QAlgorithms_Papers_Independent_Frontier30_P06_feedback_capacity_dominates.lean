-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P06.feedback_capacity_dominates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:14:41.516477+00:00
-- url     : https://prove2.me/submissions/5685b3fb-281b-4b70-9d28-ed6c02526c4f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30 QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF p.1, equation (1): ignoring feedback gives C_FB >= C, for unrestricted
classical feedback and operational uniform-message average-error capacities. -/
theorem solution (N : Backward) (hN : ChannelValid N) :
    unassistedCapacity N ≤ operationalCapacity N (fun _ => True) := by
  unfold unassistedCapacity operationalCapacity
  apply sSup_le_sSup
  rintro r ⟨R, ⟨codes, h⟩, rfl⟩
  exact ⟨R, ⟨codes, h.1, fun k => ⟨(h.2.1 k).1, trivial⟩, h.2.2⟩, rfl⟩


end

