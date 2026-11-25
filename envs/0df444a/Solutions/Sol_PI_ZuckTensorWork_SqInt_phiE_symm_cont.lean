-- Prove2me | solution 1 for PI.ZuckTensorWork.SqInt.phiE_symm_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:43.019673+00:00
-- url     : https://prove2.me/submissions/245725da-a82e-40c0-8091-738683254516

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_SquareIntegrableConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
open PI.ZuckTensorWork.SqInt
variable {n : ℕ}
namespace PI.ZuckTensorWork.SqInt
theorem _root_.solution (ε : Fin n → Bool) : Continuous (phiE ε).symm := by
  rw [(isClosedEmbeddingMatrix n (revE ε)).1.isInducing.continuous_iff]
  show Continuous (fun g : UJ ε => (coeMatrixAlt ε g).submatrix Fin.rev Fin.rev)
  exact (continuous_coeMatrix ε).matrix_submatrix Fin.rev Fin.rev
end PI.ZuckTensorWork.SqInt
