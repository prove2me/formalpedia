-- Prove2me | solution 1 for ReciprocityTheory.Cheb.chebyshev_split_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:23.765904+00:00
-- url     : https://prove2.me/submissions/314542cf-cc7d-43fb-90a3-1287c9f81579

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitE
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Theorems.Thm_ReciprocityTheory_Cheb_splitA_finite_not_coprime
import Theorems.Thm_ReciprocityTheory_Cheb_splitC_not_almost_split
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_split_ext


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
theorem _root_.solution : S2 := by
  intro E _ _ l _ hirr χ hχ m hm
  by_contra H
  push Not at H
  obtain ⟨E', _, _, _, k, hk, hsplit⟩ := splitE_split_ext E l hirr χ hχ
  have hlp : l.Prime := Fact.out
  have hml : m * l ≠ 0 := mul_ne_zero hm hlp.ne_zero
  apply splitC_not_almost_split E E' k hk
  refine (splitA_finite_not_coprime E (m * l) hml).subset ?_
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq ⊢
  intro hcop
  apply hq
  apply hsplit q
  · intro hdvd
    have h1 : Nat.Coprime (Nrm q) l := Nat.Coprime.coprime_dvd_right (dvd_mul_left l m) hcop
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 h1.symm hdvd
  · exact H q hcop
end ReciprocityTheory.Cheb
