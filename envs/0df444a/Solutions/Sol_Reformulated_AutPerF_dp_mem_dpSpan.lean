-- Prove2me | solution 1 for Reformulated.AutPerF.dp_mem_dpSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:11.891737+00:00
-- url     : https://prove2.me/submissions/495249dd-bee4-48df-bc14-fc66e5aa57fd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
namespace Reformulated.AutPerF
theorem _root_.solution {s : Set ℕ} {m : ℕ} (h : m ∈ s) : dp m (algebraMap A B ξ) ∈ dpSpan B ξ s :=
  Submodule.subset_span ⟨m, h, rfl⟩
end Reformulated.AutPerF
