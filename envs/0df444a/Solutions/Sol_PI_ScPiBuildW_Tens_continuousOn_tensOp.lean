-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.continuousOn_tensOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:36.161133+00:00
-- url     : https://prove2.me/submissions/e0b6944b-87b4-4c6d-88b8-dc62fef45ccf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Module
open PI PI.ScPiBuildW PI.ScPiBuildW.Tens
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]
namespace PI.ScPiBuildW.Tens
theorem _root_.solution {X : Type*} [TopologicalSpace X] (A : X → ∀ i, Vl i →L[ℂ] Vl i) (S : Set X)
    (hA : ∀ i (y : Vl i), ContinuousOn (fun s => A s i y) S) (v : TV Vl) :
    ContinuousOn (fun s => tensOp (A s) v) S := by
  have hrep : (fun s => tensOp (A s) v) =
      fun s => ∑ p, (tensOp (A s) v p) • EuclideanSpace.basisFun (Idx Vl) ℂ p := by
    funext s
    conv_lhs => rw [← (EuclideanSpace.basisFun (Idx Vl) ℂ).sum_repr' (tensOp (A s) v)]
    simp only [EuclideanSpace.basisFun_inner]
  rw [hrep]
  refine continuousOn_finsetSum _ fun p _ =>
    (show ContinuousOn (fun s => tensOp (A s) v p) S from ?_).smul continuousOn_const
  simp only [tensOp_apply]
  refine continuousOn_finsetSum _ fun q _ =>
    (show ContinuousOn (fun s => opMat (A s) p q) S from ?_).mul continuousOn_const
  simp only [opMat]
  refine continuousOn_finsetProd _ fun i _ => ?_
  exact ContinuousOn.inner continuousOn_const (hA i _)
end PI.ScPiBuildW.Tens
