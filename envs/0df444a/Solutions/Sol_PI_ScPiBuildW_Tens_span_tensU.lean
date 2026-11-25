-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.span_tensU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:52.736009+00:00
-- url     : https://prove2.me/submissions/25f2bac6-9d38-45ce-b710-61a0cb1b9c07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_tensU_basis

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
theorem _root_.solution : Submodule.span ℂ (Set.range (tensU (Vl := Vl))) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (EuclideanSpace.basisFun (Idx Vl) ℂ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨p, rfl⟩
  refine ⟨fun i => bas Vl i (p i), ?_⟩
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, tensU_basis]
end PI.ScPiBuildW.Tens
