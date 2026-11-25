-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__not_exc_97c622bd5aa4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:42.863223+00:00
-- url     : https://prove2.me/submissions/95da2b82-79b7-4402-a436-73d75e7cbbee

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
theorem _root_.solution {g d l k : ℕ} (h1 : ¬ l ^ (k + 1) ∣ g ^ d - 1) (h2 : l ^ (4 * k) ≤ g ^ d) :
    ¬ Formalism.CyclotomicNorms.Exc g d l := by
  rintro ⟨hl, h⟩
  have hv : padicValNat l (g ^ d - 1) ≤ k := by
    by_contra hc
    exact h1 ((pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd)
  have := Nat.pow_le_pow_right hl.pos (Nat.mul_le_mul_left 4 hv)
  omega
end Formalism.BasicNotions.Examples₂
