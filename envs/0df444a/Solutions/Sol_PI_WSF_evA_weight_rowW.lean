-- Prove2me | solution 1 for PI.WSF.evA_weight_rowW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:31.292865+00:00
-- url     : https://prove2.me/submissions/d56c0a29-4144-4b51-84d5-5961ce2fe56b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory
namespace PI.WSF
theorem _root_.solution {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d a = Formalism.GradedWeylDivisibility.rowDeg d a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • Formalism.GradedWeylDivisibility.rowW N N i) (fun i => zero_smul _ _),
    Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.rowDeg]
  · intro b _ hb
    simp [Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Ne.symm hb]
  · simp
end PI.WSF
