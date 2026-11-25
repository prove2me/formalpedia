-- Prove2me | solution 1 for P2M_PI_Dv_Tr_fcoord_smul__c8813a010909
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:44.982866+00:00
-- url     : https://prove2.me/submissions/626db693-81af-4999-b581-a95e8b1c94a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
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
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace PI.Dv.Tr
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, map_smul, smul_eq_mul, map_mul]
  rw [h, Matrix.mulVec_smul]
end PI.Dv.Tr
