-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.q_reflection_generation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:45.681387+00:00
-- url     : https://prove2.me/submissions/357483c9-8feb-4343-b68b-ce0ddce94603

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_sigV_invol
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_herm_V
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_mem_S


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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution : QReflGen := by
  intro I v hv g
  let _ : Field (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := hv.toField
  have hinj : Function.Injective (inclV I v) := (inclV I v).injective
  have hdet : (I.J.map (inclV I v)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h
    exact I.J_det (hinj (by rw [h, map_zero]))
  have h2 : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ≠ 0 := by
    intro h
    have : inclV I v 2 = inclV I v 0 := by rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero (hinj this)
  exact QRG.mem_S (sigV I v) (I.J.map (inclV I v)) (sigV_invol I v) (herm_V I v) hdet h2 g
end PI.UnitaryGroupMassFormula.AdIndexEq
