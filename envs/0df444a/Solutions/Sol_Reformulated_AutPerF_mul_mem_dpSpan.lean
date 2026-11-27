-- Prove2me | solution 1 for Reformulated.AutPerF.mul_mem_dpSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:00.942268+00:00
-- url     : https://prove2.me/submissions/d3b1f09c-d1bf-492c-99cd-7d4821bd8344

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_dp_mul_dp
import Theorems.Thm_Reformulated_AutPerF_dp_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_natCast_mul_mem

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
theorem _root_.solution {x y : B} (hx : x ∈ dpSpan B ξ Set.univ) (hy : y ∈ dpSpan B ξ Set.univ) :
    x * y ∈ dpSpan B ξ Set.univ := by
  have := Submodule.mul_mem_mul hx hy
  rw [dpSpan, Submodule.span_mul_span] at this
  refine (Submodule.span_le.2 ?_) this
  rintro _ ⟨_, ⟨a, -, rfl⟩, _, ⟨b, -, rfl⟩, rfl⟩
  change dp a _ * dp b _ ∈ dpSpan B ξ Set.univ
  rw [dp_mul_dp]
  exact natCast_mul_mem _ (dp_mem_dpSpan trivial)
end Reformulated.AutPerF
