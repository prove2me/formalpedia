-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_eq_yIndex_iff_2a9541f0912b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:24.738703+00:00
-- url     : https://prove2.me/submissions/04679d32-4580-4823-944f-2af8f9c5962a

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
variable {f r a : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (c : SmallBlock) (τ σ : Fin f) (l i : Fin r) :
    yIndex f r a c τ l = yIndex f r a c σ i ↔ τ = σ ∧ l = i := by
  cases c <;> simp only [yIndex, Prod.mk.injEq, Fin.mk.injEq, Fin.ext_iff] <;> omega
end GroundTheory.Heights₂.Heights.RestTerms.Flag
