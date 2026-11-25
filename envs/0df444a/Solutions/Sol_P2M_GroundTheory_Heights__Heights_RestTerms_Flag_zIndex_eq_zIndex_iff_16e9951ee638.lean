-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_zIndex_eq_zIndex_iff_16e9951ee638
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:54.71631+00:00
-- url     : https://prove2.me/submissions/5ebb8625-377c-457c-bbf3-2e2f8b210d48

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
theorem _root_.solution (c : SmallBlock) (τ σ : Fin f) (l i : Fin a) :
    zIndex f r a c τ l = zIndex f r a c σ i ↔ τ = σ ∧ l = i := by
  cases c <;> simp only [zIndex, Prod.mk.injEq, Fin.mk.injEq, Fin.ext_iff] <;> omega
end GroundTheory.Heights₂.Heights.RestTerms.Flag
