-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_chartMonomial_b7a9a7dc5d3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:26.372015+00:00
-- url     : https://prove2.me/submissions/d44057d9-4c2f-4f2a-80db-65cbc1a3314a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_X_chart_705df892b54f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (chartMonomial i e) = 1 := by
  simp [chartMonomial, map_prod, map_pow, mk_X_chart]
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
