-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_TwistData_hypH__461b564647c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:47.954026+00:00
-- url     : https://prove2.me/submissions/ea34cc79-8659-448c-b8f5-ca2244a207b1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_nxt_prv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (D : TwistData K) (p : ℕ) (kH : ℝ) (hH : D.HypH p kH) (j : Fin D.J) (m : Fin D.r)
    (i : Fin (D.nch j)) :
    (D.r : ℝ) * D.dLL (D.aux₃ j) / (D.P p (D.aux₃ j, m) : ℝ) + kH * D.r * D.c ≤ D.sl j i := by
  have h := hH (D.aux₃ j) m
  rw [D.nxt_prv j] at h
  exact h i
end Formalism.MainNotions.PlaneGram.TwistData
