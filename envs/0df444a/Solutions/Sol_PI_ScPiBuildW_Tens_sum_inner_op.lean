-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.sum_inner_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:39.707158+00:00
-- url     : https://prove2.me/submissions/96c22d15-26e4-4568-a9bc-de7c96bc536e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp

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
theorem _root_.solution {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (A : V' →L[ℂ] V')
    {m : Type} [Fintype m] (b : OrthonormalBasis m ℂ V') (u x : V') :
    ∑ j, ⟪u, A (b j)⟫_ℂ * ⟪b j, x⟫_ℂ = ⟪u, A x⟫_ℂ := by
  conv_rhs => rw [← b.sum_repr' x]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]
end PI.ScPiBuildW.Tens
