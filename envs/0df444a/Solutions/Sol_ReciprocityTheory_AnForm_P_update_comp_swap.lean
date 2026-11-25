-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.update_comp_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:06.139995+00:00
-- url     : https://prove2.me/submissions/5a26b4e3-4982-4777-957a-c2a597d56494

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
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (F : Fin (e + 1) → LocPot X)
    (k : Fin (e + 1)) (P : LocPot X) :
    Function.update F k P ∘ Equiv.swap 0 k = Fin.cons P (Fin.tail (F ∘ Equiv.swap 0 k)) := by
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
    rw [Function.update_of_ne]
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero j'
end ReciprocityTheory.AnForm.P
