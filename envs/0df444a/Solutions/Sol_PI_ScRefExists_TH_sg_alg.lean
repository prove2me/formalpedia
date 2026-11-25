-- Prove2me | solution 1 for PI.ScRefExists.TH.sg_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:19.189975+00:00
-- url     : https://prove2.me/submissions/cb8a03e9-8397-45b6-9e59-689983e54abf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA

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
theorem _root_.solution (c : 𝓞 I.F) : sg I (algebraMap (𝓞 I.F) (𝓞 I.E) c) = algebraMap (𝓞 I.F) (𝓞 I.E) c := by
  apply NumberField.RingOfIntegers.ext
  rw [sg_coe]
  have h : ((algebraMap (𝓞 I.F) (𝓞 I.E) c : 𝓞 I.E) : I.E) = algebraMap I.F I.E (c : I.F) := by
    show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E,
      IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]
  rw [h]
  exact (I.cm.fixed _).2 ⟨_, rfl⟩
end PI.ScRefExists.TH
