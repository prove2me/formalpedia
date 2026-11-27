-- Prove2me | solution 1 for P2M_PI_PolydiscIntegrality__exists_coord_bound_a3385e6d5105
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:17:34.077233+00:00
-- url     : https://prove2.me/submissions/88bb9edd-f5fb-4ee1-8cea-eea2b6d4b9d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_NormPPosLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_Lemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_ExistsCoordBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PolydiscIntegrality₂
open Filter Topology
variable {p : ℕ} [Fact p.Prime]
namespace PI.PolydiscIntegrality₂
theorem _root_.solution {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    ∃ B : ℕ, ∀ γ ∈ S, ∀ i, γ i ≤ B := by
  refine ⟨∑ γ ∈ S, ∑ i, γ i, fun γ hγ i => ?_⟩
  calc γ i ≤ ∑ i, γ i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ ∑ γ ∈ S, ∑ i, γ i := Finset.single_le_sum (f := fun γ : Fin n →₀ ℕ => ∑ i, γ i)
        (fun _ _ => Nat.zero_le _) hγ
end PI.PolydiscIntegrality₂
