-- Prove2me | solution 1 for PI.FinKW.LocTo.ov_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:19.776066+00:00
-- url     : https://prove2.me/submissions/6766a1b9-c100-4f2f-be20-0cab2d88fcd7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
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
open PI PI.FinKW PI.FinKW.LocTo
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW.LocTo
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • t = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) * t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add a b ha hb => rw [smul_add, ha, hb, mul_add]
end PI.FinKW.LocTo
