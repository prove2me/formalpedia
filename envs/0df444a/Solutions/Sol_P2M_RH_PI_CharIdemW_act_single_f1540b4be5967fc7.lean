-- Prove2me | solution 1 for P2M_RH_PI_CharIdemW_act_single_f1540b4be5967fc7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:40.379803+00:00
-- url     : https://prove2.me/submissions/446782f9-0000-4407-b20e-abd9aff6a78c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Central
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_CoeffMulCharIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (W : FDRep ℂ G) (g : G) (r : ℂ) :
    act W (MonoidAlgebra.single g r) = r • W.ρ g := by
  simp [act, MonoidAlgebra.lift_single]
end PI.CharIdemW
