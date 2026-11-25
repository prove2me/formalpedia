-- Prove2me | solution 1 for PI.FinKW.psiV_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:54.716566+00:00
-- url     : https://prove2.me/submissions/c545805f-b324-4134-a04d-082c8ff80f54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
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
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : Formalism.MainNotions.S.Af I.F) (e : I.E) :
    psiV I v (((1 : I.E) ⊗ₜ[I.F] a) * (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a) ⊗ₜ[I.F] e := by
  simp [psiV, Algebra.TensorProduct.tmul_mul_tmul]
end PI.FinKW
