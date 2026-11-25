-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_locDens_congr_germ_cdbb9f70069d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:43.105237+00:00
-- url     : https://prove2.me/submissions/cd8338c0-942c-445f-8791-3a910b544b84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PZIntAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_hessC_congr_eventuallyEq


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ReciprocityTheory.AnForm.M Topology
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X)
    (Φ Ψ : Fin n → LocPot X) (j : Fin A.n) (y : Fin n → ℂ)
    (h : ∀ k, (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))) :
    locDens A Φ j y = locDens A Ψ j y := by
  unfold locDens ReciprocityTheory.AnForm.maDens
  congr 3
  funext k
  exact ReciprocityTheory.AnForm.M.PLAux.hessC_congr_eventuallyEq (h k)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
