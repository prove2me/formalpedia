-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:20.602887+00:00
-- url     : https://prove2.me/submissions/063cd3e5-e673-4fa8-9d8c-0bc119d50a05

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
namespace GroundTheory.Variant₂.N1
theorem _root_.solution {R : Type*} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule R R))] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
end GroundTheory.Variant₂.N1
