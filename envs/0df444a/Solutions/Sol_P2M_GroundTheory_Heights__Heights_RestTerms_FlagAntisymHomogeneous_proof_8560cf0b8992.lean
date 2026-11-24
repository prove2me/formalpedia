-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagAntisymHomogeneous_proof_8560cf0b8992
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:22.661831+00:00
-- url     : https://prove2.me/submissions/32f5cf59-c313-4950-992c-515a0e627f8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagAntisymHomogeneous

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagAntisymHomogeneous
theorem _root_.solution : FlagAntisymHomogeneous.Statement := by
  intro f N H d hH
  have hmem : ∀ w : Fin f → Equiv.Perm (Fin N),
      blockSign f N w • blockPermute f N w H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d := by
    intro w
    refine Submodule.smul_mem _ _ ?_
    rw [mem_homogeneousSubmodule]
    exact hH.rename_isHomogeneous
  have hsum : antisymmetrize f N H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d :=
    Submodule.sum_mem _ (fun w _ => hmem w)
  rwa [mem_homogeneousSubmodule] at hsum
end FlagAntisymHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
