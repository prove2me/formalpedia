-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_locDens_perm_952114d1e445
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:55.080079+00:00
-- url     : https://prove2.me/submissions/b60c7a51-ed97-427b-bf57-511e60a756c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereCompactChange
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_mdisc_comp_perm__2bccc6921bd7


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (σ : Equiv.Perm (Fin e))
    (j : Fin A.n) (y : Fin e → ℂ) : locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
  unfold locDens maDens
  congr 2
  exact mdisc_comp_perm'
    (fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange
