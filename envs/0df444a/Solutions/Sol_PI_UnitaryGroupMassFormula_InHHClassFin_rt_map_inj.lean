-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.rt_map_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:01.226033+00:00
-- url     : https://prove2.me/submissions/abcb1ef9-75a4-4383-b041-4e72cb24f077

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) {p q : Type} (M N : Matrix p q I.E)
    (h : M.map (rtι I) = N.map (rtι I)) : M = N := by
  ext i j
  exact rt_inj I (congrFun (congrFun h i) j)
end PI.UnitaryGroupMassFormula.InHHClassFin
