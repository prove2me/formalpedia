-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.tch_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:30.873116+00:00
-- url     : https://prove2.me/submissions/e12c6db1-870b-48fe-b913-26a086caec4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ξ ξ' : ℂ_[l]} (h : ξ ∈ Tch l) (h' : ξ' ∈ Tch l) : ξ * ξ' ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [zero_mul]; exact Set.mem_insert _ _
  rcases h' with rfl | ⟨m, hm, hlm, hζ'⟩
  · rw [mul_zero]; exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · intro hd
    rcases ((Fact.out : l.Prime).dvd_mul).1 hd with h1 | h1
    · exact hln h1
    · exact hlm h1
  · rw [mul_pow, pow_mul, hζ, one_pow, one_mul, mul_comm n m, pow_mul, hζ', one_pow]
end ReciprocityTheory.ChartRestriction.L1
