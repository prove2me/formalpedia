-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectorAllocation.word_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:21:34.822109+00:00
-- url     : https://prove2.me/submissions/0aff781a-87fd-49bc-a3fd-2e43305fffdf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaSelectorAllocation
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
end ThreeSum.WeightedGlobalArenaSelectorAllocation
