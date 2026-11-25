-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exc_dvd_d9a51d8e164a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:39.386701+00:00
-- url     : https://prove2.me/submissions/a5d53bbb-346d-4d9f-b94d-b07158d475a2

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution {g d l : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ d) (h9 : d ≤ 9) (h : Formalism.CyclotomicNorms.Exc g d l) : l ∣ prodPowSubOne g := by
  have hv : padicValNat l (g ^ d - 1) ≠ 0 := by
    intro h0
    have := h.2
    rw [h0, mul_zero, pow_zero] at this
    have := Nat.one_le_pow d g hg
    omega
  refine ((dvd_pow_self l hv).trans pow_padicValNat_dvd).trans (List.dvd_prod ?_)
  exact List.mem_map.mpr ⟨d - 1, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel h1]⟩
end Formalism.BasicNotions.Examples₂
