-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.prod_sum_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:50.282696+00:00
-- url     : https://prove2.me/submissions/46149858-4a54-4c99-bfdc-fa71c2820573

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
theorem _root_.solution {κ : ι → Type} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∏ i, ∑ j, f i j = ∑ p : (∀ i, κ i), ∏ i, f i (p i) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
end PI.ScPiBuildW.Tens
