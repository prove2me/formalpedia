-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.clm_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:55.59508+00:00
-- url     : https://prove2.me/submissions/815592b6-034c-4e17-b2a1-643b615bb732

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_span_tensU

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
theorem _root_.solution {T T' : TV Vl →L[ℂ] TV Vl} (h : ∀ x, T (tensU x) = T' (tensU x)) : T = T' :=
  ContinuousLinearMap.coe_inj.1 (LinearMap.ext_on_range span_tensU h)
end PI.ScPiBuildW.Tens
