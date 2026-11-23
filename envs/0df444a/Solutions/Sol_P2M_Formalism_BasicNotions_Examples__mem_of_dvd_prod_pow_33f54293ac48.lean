-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:24.107455+00:00
-- url     : https://prove2.me/submissions/391ad5e4-a258-4a01-8bd4-44fd6971b1f3

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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (ps : List ℕ) (K : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (h : l ∣ ps.prod ^ K) : l ∈ ps := by
  have h' : l ∣ ps.prod := (Nat.Prime.prime hl).dvd_of_dvd_pow h
  obtain ⟨p, hps, hlp⟩ := ((Nat.Prime.prime hl).dvd_prod_iff).1 h'
  rwa [(Nat.prime_dvd_prime_iff_eq hl (hp p hps)).1 hlp]
end Formalism.BasicNotions.Examples₂
