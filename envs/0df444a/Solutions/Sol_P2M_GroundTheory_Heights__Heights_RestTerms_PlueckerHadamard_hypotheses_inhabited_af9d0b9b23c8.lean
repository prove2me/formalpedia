-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:28.008789+00:00
-- url     : https://prove2.me/submissions/7695d3ce-fddb-4ce7-a9f9-80bfc0aa45f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace PlueckerHadamard
theorem _root_.solution :
    ∀ i j, ‖(Matrix.of fun (_ : Fin 2) (_ : Fin 3) => (1 : ℂ)) i j‖ = 1 := by simp
end PlueckerHadamard
end GroundTheory.Heights₂.Heights.RestTerms
