-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.exists_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:25.342548+00:00
-- url     : https://prove2.me/submissions/7d8a7fb9-0708-471d-a4c5-56b7cffc8def

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA
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
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
namespace PositivityTheory.Rg.Cz.SWS
theorem _root_.solution (bar : ι → ι) (h1 : ∀ τ, bar (bar τ) = τ) (h2 : ∀ τ, bar τ ≠ τ) :
    ∃ H : Set ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨{τ | e τ < e (bar τ)}, fun τ => ?_⟩
  simp only [Set.mem_setOf_eq, h1, not_lt]
  have hne : e τ ≠ e (bar τ) := fun h => h2 τ (e.injective h).symm
  constructor
  · intro h
    exact h.le
  · intro h
    exact lt_of_le_of_ne h hne
end PositivityTheory.Rg.Cz.SWS
