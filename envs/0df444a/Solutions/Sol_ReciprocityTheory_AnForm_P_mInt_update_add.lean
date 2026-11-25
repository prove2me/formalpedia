-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.mInt_update_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:44.793419+00:00
-- url     : https://prove2.me/submissions/b6323538-bbf3-4484-a0fa-3ef33d84bb90

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_Energy
import Theorems.Thm_ReciprocityTheory_AnForm_P_mInt_update_eq
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution : MIntUpdateAddStatement := by
  intro e X _ _ _ A F k P Q hF hP hQ g hg
  have hΦ : ∀ i, IsPotential A (Fin.tail (F ∘ Equiv.swap 0 k) i) := fun i => hF _
  rw [mInt_update_eq, mInt_update_eq A F k P, mInt_update_eq A F k Q]
  exact mIntAdd A P Q _ hP hQ hΦ g (mIntegrableCont A _ (fun i => Fin.cases hP hΦ i) g hg)
    (mIntegrableCont A _ (fun i => Fin.cases hQ hΦ i) g hg)
end ReciprocityTheory.AnForm.P
