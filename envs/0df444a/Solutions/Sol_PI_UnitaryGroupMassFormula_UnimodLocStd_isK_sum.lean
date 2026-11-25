-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:21.785078+00:00
-- url     : https://prove2.me/submissions/3375ea96-d133-47d1-ae61-bff322981d9a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}
variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsK b d (f i)) : IsK b d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end PI.UnitaryGroupMassFormula.UnimodLocStd
