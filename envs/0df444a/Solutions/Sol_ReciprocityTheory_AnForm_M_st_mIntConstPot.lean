-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mIntConstPot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:46.174864+00:00
-- url     : https://prove2.me/submissions/fdfa2490-8e90-493b-8508-ada65d79cf90

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_hessC_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_maDens_cons_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas (e + 1) X) (c : ℝ) (Φ : Fin e → LocPot X)
    (g : X → ℝ) : mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by
  unfold mInt integralWith
  split_ifs
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : ∀ y, locDens A (Fin.cons (LocPot.ofFun fun _ => c) Φ) j y = 0 := by
      intro y
      unfold locDens
      apply st_maDens_cons_eq_zero
      exact st_hessC_eq_zero c (Filter.Eventually.of_forall fun _ => rfl)
    simp [h0]
  · rfl
end ReciprocityTheory.AnForm.M
