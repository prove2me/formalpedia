-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.cntQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:19.442058+00:00
-- url     : https://prove2.me/submissions/de210911-07e2-4dc1-8fd7-c85cf6284d71

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_card_filter_comp
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
theorem _root_.solution (τ : ι) (i : Fin n) : (Finset.univ.filter fun p => labQ nu p = τ ∧ bQ nu p = i).card = nu τ i := by
  refine (card_filter_comp (eB nu) (fun x => x.1 = τ ∧ x.2.1 = i)).trans ?_
  rw [Finset.card_filter, Fintype.sum_sigma]
  simp [Fintype.sum_sigma, ite_and]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp
end PositivityTheory.Rg.Cz.KTy
