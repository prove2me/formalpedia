-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_exists_limit_sum_pow_mul_b1bf9280078e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:33.295028+00:00
-- url     : https://prove2.me/submissions/3b2d6f5c-c914-4916-b8da-3e2b00095289

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_FontainePhiPowerSubgroups
import Theorems.Thm_P2M_GroundTheory_Variant__N1_mem_span_singleton_pow_smul_top_iff_3a37d45bef23

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
theorem _root_.solution {A : Type*} [CommRing A] {a : A}
    [IsPrecomplete (Ideal.span {a}) A] (b : ℕ → A) :
    ∃ L : A, ∀ n : ℕ, a ^ n ∣ (∑ k ∈ Finset.range n, a ^ k * b k) - L := by
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (Ideal.span {a}) A).prec'
    (fun n => ∑ k ∈ Finset.range n, a ^ k * b k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff,
        ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow a (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun n => (mem_span_singleton_pow_smul_top_iff a _ n).1 ((SModEq.sub_mem).1 (hL n))⟩
end GroundTheory.Variant₂.N1
