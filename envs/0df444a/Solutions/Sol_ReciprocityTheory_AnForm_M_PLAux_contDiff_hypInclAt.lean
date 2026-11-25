-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.contDiff_hypInclAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:25.391977+00:00
-- url     : https://prove2.me/submissions/32bf5070-106e-47a9-b574-7dadc0c3abf5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt jacC maDens_comp integral_image_eq_integral_normSq_det_smul
  integrableOn_image_iff_analytic)
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution (i : Fin (e + 1)) : ContDiff ℝ ∞ (hypInclAt (n := e) i) := by
  refine contDiff_pi.2 fun j => ?_
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp only [hypInclAt, Fin.insertNth_apply_same]
    exact contDiff_const
  · simp only [hypInclAt, Fin.insertNth_apply_succAbove]
    exact contDiff_pi.1 contDiff_id k
end ReciprocityTheory.AnForm.M.PLAux
