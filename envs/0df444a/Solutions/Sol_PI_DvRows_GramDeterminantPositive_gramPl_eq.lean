-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.gramPl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:28.031585+00:00
-- url     : https://prove2.me/submissions/435dedf7-38db-453e-92a8-5bf029f577c4

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
theorem _root_.solution (A : HLat K) (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    Formalism.HN.gramPl A.b A.X v f =
      ((A.X v)⁻¹ * cmat A v.embedding f)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding f) := by
  ext a c
  simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, cmat, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end PI.DvRows.GramDeterminantPositive
