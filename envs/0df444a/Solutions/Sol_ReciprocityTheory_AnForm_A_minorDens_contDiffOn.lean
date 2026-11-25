-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.minorDens_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:49.264181+00:00
-- url     : https://prove2.me/submissions/b4b96dc0-1110-454b-94af-efd37afac3e8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_contDiffOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_contDiffOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_cdo_of_infty
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_contDiffOn_re__3be3b0114f88

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) (m : ℕ) :
    ContDiffOn ℝ m (minorDens i φ) U := by
  unfold minorDens
  refine contDiffOn_re' ?_
  refine mdisc_contDiffOn (fun k z => (hessC (φ k) z).submatrix i.succAbove i.succAbove)
    fun k a b => ?_
  exact hessC_contDiffOn hU (cdo_of_infty (hφ k) m) (i.succAbove a) (i.succAbove b)
end ReciprocityTheory.AnForm.A
