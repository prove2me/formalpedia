-- Prove2me | solution 1 for P2M_Formalism_NuclearRankWeightBounds_P_PB___bbar_e0c4441375c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:21.123124+00:00
-- url     : https://prove2.me/submissions/69a9e50c-c070-49a6-a95a-45f6a942d57e

import Definitions.Def_Formalism_LogSumExpBounds_StatementC
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DescEquivLiftEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Formalism.NuclearRankWeightBounds.C
variable {RR K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]
variable {m : ℕ}
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (hZ' : IsUnit (toK K (blk Z)).det) :
    (PB Z hZ hZ').π (Submodule.Quotient.mk (Z *ᵥ eN)) = bbar Z := by
  change (Submodule.Quotient.mk (Pcs (Z *ᵥ eN)) : coker (blk Z)) = bbar Z
  unfold bbar
  congr 1
  funext i
  rw [Pcs, LinearMap.funLeft_apply, eN, mulVec_single_one]
  rfl
end Formalism.NuclearRankWeightBounds.P
