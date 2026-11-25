-- Prove2me | solution 1 for P2M_PI_Dv_Tr_normAt_zero__9806172384b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:37.257821+00:00
-- url     : https://prove2.me/submissions/ba17edd6-0ad5-415c-b91f-5518593af66b

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) :
    Formalism.HermitianLatticesTheory.normAt b X v 0 = 0 := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord
  have h : Formalism.HermitianLatticesTheory.vecAt b v (0 : V) = 0 := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [h, Matrix.mulVec_zero]
  simp
end PI.Dv.Tr
