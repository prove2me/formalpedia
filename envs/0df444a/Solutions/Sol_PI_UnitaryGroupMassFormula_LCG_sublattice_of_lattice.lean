-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.sublattice_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:53.534977+00:00
-- url     : https://prove2.me/submissions/dff902bc-181e-4d32-8440-e7e062319a8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SublatticeOfLattice
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : LatSub := by
  intro I x u u' hu hu'
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu hu' ⊢
  have h : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((u - u') i)) =
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) -
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u' i)) := by
    funext i
    simp [map_sub]
  rw [h, Matrix.mulVec_sub]
  exact Submodule.sub_mem _ hu hu'
end PI.UnitaryGroupMassFormula.LCG
