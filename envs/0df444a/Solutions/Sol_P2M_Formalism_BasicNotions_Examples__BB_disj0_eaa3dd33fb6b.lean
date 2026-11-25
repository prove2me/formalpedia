-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__BB_disj0_eaa3dd33fb6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:59.231805+00:00
-- url     : https://prove2.me/submissions/09e81d32-c629-46b9-b7f4-a4d011392729

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exc_dvd_d9a51d8e164a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__not_exc_97c622bd5aa4

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
theorem _root_.solution : Disjoint (Formalism.CyclotomicNorms.BB 9 413718278401) (Formalism.CyclotomicNorms.BB 9 603339156001) := by
  rw [Set.disjoint_left]
  rintro l (rfl | ⟨d, h1, h9, h⟩) (h' | ⟨d', h1', h9', h'⟩)
  · exact absurd (Set.mem_singleton_iff.mp h') (by norm_num)
  · exact absurd (exc_dvd (by norm_num) h1' h9' h') (by decide +kernel)
  · rw [Set.mem_singleton_iff.mp h'] at h
    exact absurd (exc_dvd (by norm_num) h1 h9 h) (by decide +kernel)
  · have hg : Nat.gcd (prodPowSubOne 413718278401) (prodPowSubOne 603339156001) ∣ [2, 3, 5, 7, 11, 13, 37, 571, 599].prod ^ 52 := by decide +kernel
    have hm := mem_of_dvd_prod_pow h.1 _ _ (by decide +kernel)
      ((Nat.dvd_gcd (exc_dvd (by norm_num) h1 h9 h) (exc_dvd (by norm_num) h1' h9' h')).trans hg)
    have key : ∀ l ∈ [2, 3, 5, 7, 11, 13, 37, 571, 599], ∀ d ∈ List.range 10, 1 ≤ d → ∃ k ∈ List.range 20,
        ¬ l ^ (k + 1) ∣ 413718278401 ^ d - 1 ∧ l ^ (4 * k) ≤ 413718278401 ^ d := by decide +kernel
    obtain ⟨k, -, hk1, hk2⟩ := key l hm d (List.mem_range.mpr (by omega)) h1
    exact not_exc hk1 hk2 h
end Formalism.BasicNotions.Examples₂
