-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:20.30581+00:00
-- url     : https://prove2.me/submissions/6ec66110-5fb3-431b-b114-c87a6baec242

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
theorem _root_.solution (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (τ : Fin f) (i : Fin N) :
    blockPermute f N w (X (τ, i)) = X (τ, w τ i) := by
  simp [blockPermute]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
