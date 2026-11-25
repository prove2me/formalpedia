-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.cntF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:18.75497+00:00
-- url     : https://prove2.me/submissions/e2145ffb-3e04-44eb-90b7-c615d09789ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_card_filter_sum
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cntQ
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cnt1
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cnt2
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (nu : ι → Fin n → ℕ) (H : Finset ι)
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun p => lab3 bar (labQ nu) (tl H) p = τ ∧ bF nu H p = i).card = nu τ i + i := by
  refine (card_filter_sum _).trans ?_
  refine (congrArg₂ (· + ·) (cntQ nu τ i)
    ((card_filter_sum _).trans (congrArg₂ (· + ·) (cnt1 H τ i) (cnt2 H bar hinv τ i)))).trans ?_
  by_cases h : τ ∈ H
  · have := (hH τ).1 h
    simp [h, this]
  · have : bar τ ∈ H := by
      by_contra h'
      exact h ((hH τ).2 h')
    simp [h, this]
end PositivityTheory.Rg.Cz.KTy
