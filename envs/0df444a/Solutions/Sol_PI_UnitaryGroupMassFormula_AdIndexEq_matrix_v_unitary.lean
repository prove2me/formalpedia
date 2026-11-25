-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.matrix_v_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:58.340872+00:00
-- url     : https://prove2.me/submissions/33d52043-b20f-4e24-8b4f-028c3d39fe30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_matV_coe
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mapJ
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_map_unitary
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mem_Uv_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mem_Gf_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution : MatVU := by
  unfold MatVU
  intro I v y
  rw [mem_Uv_iff, matV_coe]
  have hy := (mem_Gf_iff I y).1 y.2
  rw [← map_unitary, hy]
  exact mapJ I v
end PI.UnitaryGroupMassFormula.AdIndexEq
