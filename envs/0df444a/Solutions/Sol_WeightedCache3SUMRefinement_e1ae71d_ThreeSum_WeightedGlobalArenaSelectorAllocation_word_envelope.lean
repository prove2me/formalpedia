-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation.word_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:58.992353+00:00
-- url     : https://prove2.me/submissions/aecaf645-53c0-4126-bc6c-a425018ea049

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectorAllocation

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
theorem _root_.solution {T n score dB dC dP tB tC tP : ℕ}
    (hT : 1≤T) (hn : n≤T) (hs : score≤T)
    (hdB : dB≤T) (hdC : dC≤T) (hdP : dP≤T)
    (htB : tB≤T) (htC : tC≤T) (htP : tP≤T) :
    LightTernaryRowSelector.word n score dB dC dP tB tC tP≤(T+1)^4 := by
  have hm : score*(dB+dC+dP+1)≤T*(3*T+1) :=
    Nat.mul_le_mul hs (by omega)
  have h3 : T≤T^3 := by
    calc
      T≤T*T^2 := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
      _=T^3 := by ring
  have h4 : 1≤T^4 := Nat.one_le_pow 4 T hT
  unfold LightTernaryRowSelector.word
  nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
