-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__lucas_list_6f32cc34af5b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:24.251028+00:00
-- url     : https://prove2.me/submissions/abe82c74-29de-4168-86ee-796c5eade43f

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48

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
theorem _root_.solution (n a : ℕ) (ps : List ℕ) (K : ℕ) (hd : n - 1 ∣ ps.prod ^ K) (hp : ∀ p ∈ ps, p.Prime)
    (h1 : (a : ZMod n) ^ (n - 1) = 1) (h2 : ∀ p ∈ ps, (a : ZMod n) ^ ((n - 1) / p) ≠ 1) : n.Prime := by
  refine lucas_primality n (a : ZMod n) h1 fun q hq hqd => h2 q ?_
  exact mem_of_dvd_prod_pow hq ps K hp (hqd.trans hd)
end Formalism.BasicNotions.Examples₂
