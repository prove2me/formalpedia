-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.440812+00:00
-- url     : https://prove2.me/submissions/f0f9e1df-f5ef-434b-9c2a-997d927f4da8

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
theorem _root_.solution (f N : ℕ) : Fintype.card (Fin f → Equiv.Perm (Fin N)) = N.factorial ^ f := by
  simp [Fintype.card_perm]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
