-- Prove2me | solution 1 for PI.ScRefExists.PPA.GE_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:40.495293+00:00
-- url     : https://prove2.me/submissions/a4c0b0b4-1ab7-406e-a821-32c30c1ec9a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_SpanSmulInto
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
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (g : ℕ) {x : I.E} (h : GE I g x) : GE I g (star x) := by
  obtain ⟨t, ht⟩ := h
  have hint : IsIntegral ℤ (starRingEnd I.E (t : I.E)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
    | exact (t.2).map (starRingEnd I.E).toIntAlgHom
  refine ⟨⟨starRingEnd I.E (t : I.E), hint⟩, ?_⟩
  rw [ht]
  first
  | (rw [star_mul', star_natCast]; rfl)
  | simp [star_mul']
end PI.ScRefExists.PPA
