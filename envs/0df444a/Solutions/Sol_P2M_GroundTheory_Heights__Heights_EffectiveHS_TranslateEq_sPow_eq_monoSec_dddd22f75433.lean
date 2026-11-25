-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:25.357493+00:00
-- url     : https://prove2.me/submissions/849a75e1-71fd-4497-9981-051b9085ba69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS (topForms topFormWeightedL2 twist wAdd fsPhi HermSpace FSData HSData
  secMul l2n tuples jacDet)
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {Y : Type} [TopologicalSpace Y] (d : FSData A Y)
namespace GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
theorem _root_.solution (s : Fin D → Fin d.W.n → ℂ) (α : Fin D → ℕ) :
    sPow (fun i => d.W.sec (s i)) α = d.monoSec s α := by
  funext j x
  simp [sPow, IndefiniteRowSideFullHecke.EffectiveHS.FSData.monoSec, Finset.prod_apply]
end GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
