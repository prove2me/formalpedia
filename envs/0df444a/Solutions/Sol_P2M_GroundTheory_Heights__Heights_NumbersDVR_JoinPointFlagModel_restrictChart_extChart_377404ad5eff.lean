-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_restrictChart_extChart_377404ad5eff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:28:20.140859+00:00
-- url     : https://prove2.me/submissions/302cb8a2-e3a5-4147-89ac-a9826e82232d

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointFlagModel
import Mathlib
import Mathlib.Tactic






-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel
variable {Ω : Type*} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem _root_.solution (t : ∀ k, ι k) : restrictChart (extChart t) = t := by
  first
    | exact Iff.rfl
    | (intros; exact Iff.rfl)
    | (intros; exact ⟨rfl, rfl⟩)
    | (intros; exact ⟨fun h => h, fun h => h⟩)
    | (intros; norm_num; done)
    | (intros; norm_num [extChart]; done)
    | (intros; simp [Matrix.PosDef.one]; done)
    | (intros; exact inferInstance)
    | (refine ⟨?_, ?_⟩ <;> norm_num [extChart])
    | (intros; unfold extChart; norm_num; done)
    | (intros; unfold extChart; exact Iff.rfl)
    | (intros; ext; simp [extChart]; done)
    | (intros; funext; rfl)
    | (intros; ext; exact Iff.rfl)
    | (intros; simpa [extChart] using ‹_›)
    | (intros; exact Subsingleton.elim _ _)
    | (intros; omega)
    | (intros; positivity)
  trace "HIT_50_0"



end 
