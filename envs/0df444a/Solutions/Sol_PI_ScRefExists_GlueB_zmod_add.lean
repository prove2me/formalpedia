-- Prove2me | solution 1 for PI.ScRefExists.GlueB.zmod_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:39.242958+00:00
-- url     : https://prove2.me/submissions/1841fd12-b1df-4e9f-b493-cebd3d3c70d6

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
theorem _root_.solution {x y : I.E ⊗[I.F] Af I.F} (h1 : ZMod' I g x) (h2 : ZMod' I g y) :
    ZMod' I g (x + y) := by
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  exact ⟨a + b, add_mem ha hb, (mul_add _ _ _).symm⟩
end PI.ScRefExists.GlueB
