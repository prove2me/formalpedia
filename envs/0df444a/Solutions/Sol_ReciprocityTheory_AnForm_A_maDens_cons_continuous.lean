-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_cons_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:12.78114+00:00
-- url     : https://prove2.me/submissions/813d8cb8-1f7a-4d06-8d53-5d7d5026b3e4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_of_contDiffOn_zero_off
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_contDiffOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_contDiffOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_cdo_of_infty
import Theorems.Thm_ReciprocityTheory_AnForm_A_cdo_of_three
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
theorem _root_.solution {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {f : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 3 f) (hfU : tsupport f ⊆ U)
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) :
    Continuous (maDens (Fin.cons f φ)) := by
  have h : ContDiffOn ℝ (1 : ℕ) (maDens (Fin.cons f φ)) U := by
    unfold maDens
    refine contDiffOn_const.mul (contDiffOn_re' ?_)
    refine mdisc_contDiffOn (fun k z => hessC ((Fin.cons f φ : Fin (n + 1) → _) k) z)
      fun k i j => ?_
    cases k using Fin.cases with
    | zero => simpa using hessC_contDiffOn hU (cdo_of_three hf) i j
    | succ k => simpa using hessC_contDiffOn hU (cdo_of_infty (hφ k) 1) i j
  exact (contDiff_of_contDiffOn_zero_off hU (isClosed_tsupport f) hfU h
    (fun z hz => maDens_cons_eq_zero φ hz)).continuous
end ReciprocityTheory.AnForm.A
