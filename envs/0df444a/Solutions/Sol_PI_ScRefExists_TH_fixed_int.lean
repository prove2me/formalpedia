-- Prove2me | solution 1 for PI.ScRefExists.TH.fixed_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:21.220326+00:00
-- url     : https://prove2.me/submissions/a1f63144-00cb-4ab3-b9fb-e3cc9656d834

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Theorems.Thm_PI_ScRefExists_TH_coe_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution (y : 𝓞 I.E) (hy : star (y : I.E) = y) :
    ∃ c : 𝓞 I.F, algebraMap (𝓞 I.F) (𝓞 I.E) c = y := by
  obtain ⟨a, ha⟩ := (I.cm.fixed (y : I.E)).1 hy
  have hi : IsIntegral ℤ (algebraMap I.F I.E a) := by
    rw [ha]; exact y.isIntegral_coe
  have hi' : IsIntegral ℤ a := (isIntegral_algebraMap_iff (algebraMap I.F I.E).injective).mp hi
  let c : 𝓞 I.F := ⟨a, (mem_integralClosure_iff _ _).mpr hi'⟩
  refine ⟨c, ?_⟩
  apply NumberField.RingOfIntegers.ext
  rw [coe_alg]
  exact ha
end PI.ScRefExists.TH
