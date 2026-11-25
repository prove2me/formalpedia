-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.crdBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:53.537399+00:00
-- url     : https://prove2.me/submissions/e4564f65-f28c-47a9-9078-97d32487019a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_intF_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_upper
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_int_smul_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_lower
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_intCast_ne_zero_OF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : CrdBounds := by
  intro F E _ _ _ _ _ V _ _ _ _ _ M b L0 hL
  obtain ⟨y1, hy1, h1⟩ := crd_upper b L0 hL.fg
  obtain ⟨y2, hy2, h2⟩ := crd_lower b L0 hL.span_eq_top
  refine ⟨⟨(y1 : 𝓞 F), intCast_ne_zero_OF y1 hy1, fun x hx i => ?_⟩,
    ⟨(y2 : 𝓞 F), intCast_ne_zero_OF y2 hy2, fun i e he => ?_⟩⟩
  · rw [intF_smul]
    exact h1 x hx i
  · show ∑ j, (Pi.single i ((((y2 : 𝓞 F) : F)) • e) : Fin M → E) j • b j ∈ L0
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
      Pi.single_eq_same, intF_smul, smul_assoc, smul_comm]
    exact int_smul_mem L0 he (h2 i)
end PI.UnitaryGroupMassFormula.UJClassMass
