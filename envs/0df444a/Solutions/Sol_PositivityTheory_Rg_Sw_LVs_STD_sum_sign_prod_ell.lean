-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.sum_sign_prod_ell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:18.180731+00:00
-- url     : https://prove2.me/submissions/bac16647-0ab2-4f79-bbe8-9816ba99b443

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_ell_apply
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_STD_trace_mul_single__8682ea6fcbf3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (β : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod =
      (2 * Real.pi * Complex.I) ^ Fintype.card (Fin n) * β.det := by
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, ml, ell_apply, trace_mul_single', Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (∏ i : Fin (Fintype.card (Fin n)), β (σ ((Fintype.equivFin (Fin n)).symm i))
      ((Fintype.equivFin (Fin n)).symm i)) = ∏ a : Fin n, β (σ a) a from
    Fintype.prod_equiv (Fintype.equivFin (Fin n)).symm _ _ (fun _ => rfl)]
  rw [Units.smul_def, zsmul_eq_mul]
  push_cast
  ring
end PositivityTheory.Rg.Sw.LVs.STD
