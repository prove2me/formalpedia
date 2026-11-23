-- Prove2me | solution 1 for Reformulated.AutPerF.dpSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:11.067194+00:00
-- url     : https://prove2.me/submissions/5d81ac25-62b6-42a6-8632-11065e436d68

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
theorem _root_.solution {s t : Set ℕ} (h : s ⊆ t) : dpSpan B ξ s ≤ dpSpan B ξ t :=
  Submodule.span_mono (Set.image_mono h)
end Reformulated.AutPerF
