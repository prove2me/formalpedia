-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitA_finite_not_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:49:39.22302+00:00
-- url     : https://prove2.me/submissions/6cbe7b58-6f08-4f51-9f80-81762017ac2e

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Theorems.Thm_ReciprocityTheory_Cheb_natCast_mem_of_not_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] (n : ℕ) (hn : n ≠ 0) :
    {q : Prm E | ¬ Nat.Coprime (Nrm q) n}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun q hq => ?_
  exact (Ideal.dvd_span_singleton).mpr (natCast_mem_of_not_coprime E n q hq)
end ReciprocityTheory.Cheb
