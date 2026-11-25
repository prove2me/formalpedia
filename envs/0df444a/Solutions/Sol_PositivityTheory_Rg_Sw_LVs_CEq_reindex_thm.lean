-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.reindex_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:47.013731+00:00
-- url     : https://prove2.me/submissions/5612c7af-ee9b-4f87-8368-b4e0c9efa9d8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_iteratedFDeriv_comp_clm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_detD_eq_Dg
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_Dg_indep
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_reindex_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution : Reindex := by
  intro ι κ _ _ _ _ e F hF
  rw [detD_eq_Dg, detD_eq_Dg,
    ← Dg_indep F hF (e.symm.trans (Fintype.equivFin ι)) (Fintype.equivFin κ)]
  unfold Dg
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ => ?_
  rw [Equiv.Perm.sign_permCongr]
  congr 1
  have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (Matrix.reindex e e T)) 0
      (fun i => Matrix.single ((Fintype.equivFin ι).symm i) (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ)) =
      iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i =>
        Matrix.reindex e e (Matrix.single ((Fintype.equivFin ι).symm i)
          (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ))) :=
    iteratedFDeriv_comp_clm F hF
      (LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) _ _
  rw [h1]
  congr 1
  funext i
  rw [reindex_single]
  simp
end PositivityTheory.Rg.Sw.LVs.CEq
