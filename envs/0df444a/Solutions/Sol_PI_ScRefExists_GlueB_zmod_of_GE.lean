-- Prove2me | solution 1 for PI.ScRefExists.GlueB.zmod_of_GE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:33.78949+00:00
-- url     : https://prove2.me/submissions/5fb961e9-90d6-4757-b98b-1a7191b2611a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
import Theorems.Thm_P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed


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
theorem _root_.solution {x : I.E} (h : GE I g x) : ZMod' I g (Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E), inclE_mem' I t, by rw [map_mul, map_natCast]⟩
end PI.ScRefExists.GlueB
