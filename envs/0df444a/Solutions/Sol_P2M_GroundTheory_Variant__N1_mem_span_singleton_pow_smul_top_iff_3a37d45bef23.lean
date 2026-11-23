-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_mem_span_singleton_pow_smul_top_iff_3a37d45bef23
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.938822+00:00
-- url     : https://prove2.me/submissions/b578d7c2-77ec-49b6-b788-034106d20d64

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_FontainePhiPowerSubgroups

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
theorem _root_.solution {A : Type*} [CommRing A] (a x : A) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
end GroundTheory.Variant₂.N1
