-- Prove2me | solution 1 for P2M_PI_Dv_Tr_normAt_smul__30a616144aad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:42.497793+00:00
-- url     : https://prove2.me/submissions/6303ce03-6111-43c4-ab91-b4561f73fd79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_P2M_PI_Dv_Tr_fcoord_smul__c8813a010909
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
    Formalism.HermitianLatticesTheory.normAt b X v (c • x) = ‖v.embedding c‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [fcoord_smul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
end PI.Dv.Tr
