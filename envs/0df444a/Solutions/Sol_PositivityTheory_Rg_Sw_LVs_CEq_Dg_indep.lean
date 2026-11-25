-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.Dg_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:33.325322+00:00
-- url     : https://prove2.me/submissions/2ae7ae56-f228-455c-88d7-0e985be21dd8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_symm_perm

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
theorem _root_.solution (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n m : ℕ} (f : κ ≃ Fin n) (g : κ ≃ Fin m) :
    Dg f F = Dg g F := by
  have hnm : n = m := by simpa using Fintype.card_congr (f.symm.trans g)
  subst hnm
  unfold Dg
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hv : (fun i => Matrix.single (f.symm i) (σ (f.symm i)) (1 : ℂ)) =
      (fun i => Matrix.single (g.symm i) (σ (g.symm i)) (1 : ℂ)) ∘ (f.symm.trans g) := by
    funext i
    simp
  rw [hv]
  exact symm_perm F hF _ _
end PositivityTheory.Rg.Sw.LVs.CEq
