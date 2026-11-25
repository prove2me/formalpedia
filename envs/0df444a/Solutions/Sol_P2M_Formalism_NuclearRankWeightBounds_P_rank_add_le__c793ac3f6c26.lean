-- Prove2me | solution 1 for P2M_Formalism_NuclearRankWeightBounds_P_rank_add_le__c793ac3f6c26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:22.350219+00:00
-- url     : https://prove2.me/submissions/f28de380-9d93-4e49-81fe-79cfe94091ef

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_RankLeOfSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : LinearMap.range (A + B).mulVecLin
      ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    intro x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hx
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨v, rfl⟩) (LinearMap.mem_range.2 ⟨v, rfl⟩)
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
end Formalism.NuclearRankWeightBounds.P
