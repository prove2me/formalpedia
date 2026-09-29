-- Prove2me | solution 1 for RingHom.mem_range_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fd97b0fa-36a8-5af4-8c37-5f44dcdd0473

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_mem_range_of_pow_eq_one

theorem solution {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ σ.range := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.prim (M := F) (n := n)
  obtain ⟨i, -, hi⟩ := (hζ₀.map_of_injective σ.injective).eq_pow_of_pow_eq_one hζ
  exact ⟨ζ₀ ^ i, by rw [map_pow, hi]⟩

end S_RingHom_mem_range_of_pow_eq_one
end P2MW
export P2MW.S_RingHom_mem_range_of_pow_eq_one (solution)
