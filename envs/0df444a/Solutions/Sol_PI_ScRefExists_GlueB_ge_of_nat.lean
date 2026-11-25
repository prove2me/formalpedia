-- Prove2me | solution 1 for PI.ScRefExists.GlueB.ge_of_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:58.678541+00:00
-- url     : https://prove2.me/submissions/7558611e-372d-49dc-a256-cc02d244106b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueB
open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)
namespace PI.ScRefExists.GlueB
theorem _root_.solution {x : I.E} (m : ℕ) (h : x = (g : I.E) * (m : I.E)) : GE I g x :=
  ⟨(m : 𝓞 I.E), by rw [h]; exact congrArg _ (map_natCast (algebraMap (𝓞 I.E) I.E) m).symm⟩
end PI.ScRefExists.GlueB
