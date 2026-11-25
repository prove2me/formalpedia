-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DualI.mem_latSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:58.900228+00:00
-- url     : https://prove2.me/submissions/8d254c5d-d2a8-4161-b33e-5d278a19d44b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_DualIncl
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_LatIs_lamAf_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DualI
open Formalism.UG Formalism.UG.P
namespace PI.UnitaryGroupMassFormula.LCG.DualI
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (y : I.GA) (u : Fin I.n → I.E) :
    u ∈ PI.LatCountG.latSet I y ↔
      (((y.2 : GL (Fin I.n) (AA I))⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
        (fun i => iA I (u i)) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := by
  unfold PI.LatCountG.latSet
  rw [Set.mem_setOf_eq, PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq I]
  rfl
end PI.UnitaryGroupMassFormula.LCG.DualI
