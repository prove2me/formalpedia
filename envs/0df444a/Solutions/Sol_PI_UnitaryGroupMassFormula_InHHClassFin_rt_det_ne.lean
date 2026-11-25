-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.rt_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:58.695884+00:00
-- url     : https://prove2.me/submissions/af41843b-7cde-4149-844e-f4572829c1e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_inj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) {k : Type} [Fintype k] [DecidableEq k]
    (M : Matrix k k I.E) (u : GL k (rtA I)) (hu : (u : Matrix k k (rtA I)) = M.map (rtι I)) :
    M.det ≠ 0 := by
  intro h0
  haveI : Nontrivial (rtA I) :=
    nontrivial_of_ne _ _ (by simpa using (rt_inj I).ne (one_ne_zero (α := I.E)))
  have h1 : IsUnit ((u : Matrix k k (rtA I)).det) := (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
  rw [hu, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
  exact not_isUnit_zero h1
end PI.UnitaryGroupMassFormula.InHHClassFin
