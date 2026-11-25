-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitD_natCast_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:53.6686+00:00
-- url     : https://prove2.me/submissions/02a584f8-329d-4dc0-b288-54661c921b1d

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (hl : ¬ l ∣ Nrm q) : (l : 𝓞 E) ∉ q.asIdeal := by
  intro h
  have hmax : q.asIdeal.IsMaximal := q.isMaximal
  let : Field (𝓞 E ⧸ q.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 E ⧸ q.asIdeal) := by
    have := (Ideal.absNorm_ne_zero_iff q.asIdeal).1 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot)
    exact this
  let := Fintype.ofFinite (𝓞 E ⧸ q.asIdeal)
  have h0 : ((l : 𝓞 E ⧸ q.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk q.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact h
  set p := ringChar (𝓞 E ⧸ q.asIdeal)
  have hpl : p ∣ l := (ringChar.spec _ l).1 h0
  have hp1 : p ≠ 1 := CharP.ringChar_ne_one
  have hpeq : p = l := ((Fact.out : l.Prime).eq_one_or_self_of_dvd p hpl).resolve_left hp1
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) p
  apply hl
  have : Nrm q = Fintype.card (𝓞 E ⧸ q.asIdeal) := by
    rw [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [this, hn, hpeq]
  exact dvd_pow_self l n.ne_zero
end ReciprocityTheory.Cheb
