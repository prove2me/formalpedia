-- Prove2me | solution 1 for PI.FinKW.psiV_liftOne_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:44.259242+00:00
-- url     : https://prove2.me/submissions/4a8fd7ee-76ae-4a7f-8331-4c13de31c1fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Theorems.Thm_PI_FinKW_evalV_singleV_same
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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : psiV I v (liftOne I v y) = y := by
  classical
  have hy : (TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E)).symm
      (TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E) y) = y :=
    LinearEquiv.symm_apply_apply _ y
  conv_rhs => rw [← hy]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, liftOne, Finsupp.sum, Finsupp.sum,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [psiV, evalV_singleV_same]
end PI.FinKW
