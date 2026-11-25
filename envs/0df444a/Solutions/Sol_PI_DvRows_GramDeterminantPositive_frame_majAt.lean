-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.frame_majAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:24.083162+00:00
-- url     : https://prove2.me/submissions/ed446f31-1b62-4d5c-a24e-ad8450e6f01b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
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
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (A : HLat K) (v : InfinitePlace K) :
    ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ =
      Matrix.of fun k l => Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b k) (A.b l) := by
  ext k l
  simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, conjTranspose_apply, Finsupp.single_apply, apply_ite]
end PI.DvRows.GramDeterminantPositive
