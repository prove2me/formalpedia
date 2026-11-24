-- Prove2me | solution 1 for PI.FockOneDegW.Swap.mem_hwSub_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:28.143479+00:00
-- url     : https://prove2.me/submissions/5f021e7d-35d8-4653-871e-42746cb19810

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {m n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace PI.FockOneDegW.Swap
theorem _root_.solution (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (ν : Ix m n → ℚ) (w : V) :
    w ∈ hwSub act ν ↔ (∀ a, act (Eab a a) w = ((ν a : ℚ) : ℂ) • w) ∧
      ∀ a b, posC a b → act (Eab a b) w = 0 := by
  unfold hwSub wtSub
  simp [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
end PI.FockOneDegW.Swap
