-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:12.883386+00:00
-- url     : https://prove2.me/submissions/7a8e5763-064a-4d64-b0b4-3d134af69769

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
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
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (hne : ∀ τ, bar τ ≠ τ) :
    ∃ H : Finset ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by
  refine ⟨Finset.univ.filter fun τ => Fintype.equivFin ι τ < Fintype.equivFin ι (bar τ), fun τ => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hinv, not_lt]
  have : Fintype.equivFin ι τ ≠ Fintype.equivFin ι (bar τ) := fun h => hne τ ((Fintype.equivFin ι).injective h).symm
  exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h this⟩
end PositivityTheory.Rg.Cz.KTy
