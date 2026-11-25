-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.gramPl_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:10.438306+00:00
-- url     : https://prove2.me/submissions/d23cd103-c0fb-4cd3-b461-1852ce346bf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_gramPl_eq
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_cmat_injective
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
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (A : HLat K) (v : InfinitePlace K) (hX : IsUnit (A.X v).det) {m : ℕ}
    (f : Fin m → A.V) (hf : LinearIndependent K f) : (Formalism.HN.gramPl A.b A.X v f).PosDef := by
  rw [gramPl_eq]
  apply PosDef.conjTranspose_mul_self
  have hXi : Function.Injective ((A.X v)⁻¹).mulVec :=
    (mulVec_injective_iff_isUnit).2 ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hX))
  intro a b hab
  simp only [← mulVec_mulVec] at hab
  exact cmat_injective A v.embedding f hf (hXi hab)
end PI.DvRows.GramDeterminantPositive
