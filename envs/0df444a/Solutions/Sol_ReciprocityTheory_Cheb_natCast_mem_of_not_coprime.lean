-- Prove2me | solution 1 for ReciprocityTheory.Cheb.natCast_mem_of_not_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:54.578062+00:00
-- url     : https://prove2.me/submissions/6cabc9c3-8634-4340-9aa4-846e54037dd2

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (n : ℕ) (q : Prm E)
    (h : ¬ Nat.Coprime (Nrm q) n) : ((n : ℕ) : 𝓞 E) ∈ q.asIdeal := by
  have : q.asIdeal.IsMaximal := q.isMaximal
  let _ := Ideal.Quotient.field q.asIdeal
  let _ : Fintype (𝓞 E ⧸ q.asIdeal) := Fintype.ofFinite _
  have := ringChar.charP (𝓞 E ⧸ q.asIdeal)
  obtain ⟨k, hcp, hcard⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) (ringChar (𝓞 E ⧸ q.asIdeal))
  have hN : Nrm q = ringChar (𝓞 E ⧸ q.asIdeal) ^ (k : ℕ) := by
    rw [← hcard, Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝓞 E ⧸ q.asIdeal) (ringChar (𝓞 E ⧸ q.asIdeal))]
  by_contra hd
  exact h (hN ▸ Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hcp).mpr hd))
end ReciprocityTheory.Cheb
