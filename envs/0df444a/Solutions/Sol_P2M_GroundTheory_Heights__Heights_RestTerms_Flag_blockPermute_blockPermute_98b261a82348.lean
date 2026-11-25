-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockPermute_98b261a82348
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:52.553628+00:00
-- url     : https://prove2.me/submissions/70a5706f-67bd-4570-bdd0-e06b9f52dc7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (blockPermute f N w H) = blockPermute f N (v * w) H := by
  simp only [blockPermute, rename_rename]
  rfl
end GroundTheory.Heights₂.Heights.RestTerms.Flag
