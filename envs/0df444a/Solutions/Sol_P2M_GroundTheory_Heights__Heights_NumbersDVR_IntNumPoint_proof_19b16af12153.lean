-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:28:15.491046+00:00
-- url     : https://prove2.me/submissions/f23faf48-92dd-4bc5-8c90-d6870f66ac78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_finrank_chart_eq_a442523a379e

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
theorem _root_.solution (hBase : FieldNumbers.IntNumBase.Statement.{u}) : IntNumPoint.Statement.{u} := by
  intro F _ K _ _ ι _ V i hV hdim hi
  haveI := hV.isPrime
  have hrel : FieldNumbers.relDim V = 0 := by
    rw [FieldNumbers.relDim, hdim]
    have : (((0 + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = 0 := by simp
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  obtain ⟨hfin, hnum⟩ := hBase F K ι V hV hrel
  rw [hnum, ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg, finrank_chart_eq V hV i hi hfin]
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
