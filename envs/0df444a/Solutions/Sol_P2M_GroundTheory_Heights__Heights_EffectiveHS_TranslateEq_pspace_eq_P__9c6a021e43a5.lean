-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_pspace_eq_P__9c6a021e43a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:59.516435+00:00
-- url     : https://prove2.me/submissions/9fe0a880-4a86-42d4-95cd-6768cb0c7d8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433

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
variable {Y : Type} [TopologicalSpace Y]
namespace GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
theorem _root_.solution (d : HSData A Y) (s : Fin D → Fin d.W.n → ℂ) :
    Pspace (fun i => d.W.sec (s i)) (d.V D).space d.T = d.Pσ s := by
  unfold Pspace IndefiniteRowSideFullHecke.EffectiveHS.HSData.Pσ
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq, sPow_eq_monoSec]
  rfl
end GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
