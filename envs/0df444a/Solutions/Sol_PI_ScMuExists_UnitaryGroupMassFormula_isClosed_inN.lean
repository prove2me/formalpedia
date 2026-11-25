-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.isClosed_inN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:58.665539+00:00
-- url     : https://prove2.me/submissions/42c8392e-5a66-433f-b602-01b44ad79c1d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_sub_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have h1 : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a : Fin r, {g | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩ {g | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
        ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0}, {g | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, InN, InS]
  rw [h1]
  exact ((isClosed_iInter fun a => isClosed_sub_mem _ _).inter (isClosed_sub_mem _ _)).inter
    (isClosed_biInter fun y _ => isClosed_sub_mem _ _)
end PI.ScMuExists.UnitaryGroupMassFormula
