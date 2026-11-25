-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.mixFam_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:26.107161+00:00
-- url     : https://prove2.me/submissions/4fea839b-ce82-430e-aa6f-8905bceffd37

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_Energy
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution : MixFamSuccStatement := by
  intro e X _ Φ w i hi
  refine ⟨?_, by simp [mixFam]⟩
  funext k
  by_cases hk : k = ⟨i, hi⟩
  · subst hk
    simp [mixFam]
  · rw [Function.update_of_ne hk]
    have hk' : k.val ≠ i := fun h => hk (Fin.ext h)
    simp only [mixFam]
    by_cases h1 : k.val < i
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
end ReciprocityTheory.AnForm.P
