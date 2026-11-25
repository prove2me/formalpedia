-- Prove2me | solution 1 for PI.ZuckTensorWork.cjSub_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:46.199743+00:00
-- url     : https://prove2.me/submissions/12cfcfbd-2760-42e0-9b63-1f6418c5b005

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution (s : Set H) : cjSub (Submodule.span ℂ s) = Submodule.span ℂ (Cj.mk '' s) := by
  apply le_antisymm
  · intro x hx
    have key : ∀ y ∈ Submodule.span ℂ s, Cj.mk y ∈ Submodule.span ℂ (Cj.mk '' s) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [Cj.mk_smul]; exact Submodule.smul_mem _ _ ha
    exact key (Cj.un x) hx
  · rw [Submodule.span_le]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    show y ∈ Submodule.span ℂ s
    exact Submodule.subset_span hy
end PI.ZuckTensorWork
