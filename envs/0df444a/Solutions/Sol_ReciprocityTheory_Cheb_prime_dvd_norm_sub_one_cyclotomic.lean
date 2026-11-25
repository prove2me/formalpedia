-- Prove2me | solution 1 for ReciprocityTheory.Cheb.prime_dvd_norm_sub_one_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:47.1395+00:00
-- url     : https://prove2.me/submissions/d1f18a4b-e794-4954-a903-d85c18759a4f

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l) : l ∣ Nrm P - 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have hz := (IsCyclotomicExtension.zeta_spec l E M).toInteger_isPrimitiveRoot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq := hz.idealQuotient_mk (I := P.asIdeal) h1 hl
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have hu := hq.isUnit hlp.ne_zero
  have hu' : IsPrimitiveRoot hu.unit l := IsPrimitiveRoot.coe_units_iff.mp hq
  have hd : orderOf hu.unit ∣ Nat.card (𝓞 M ⧸ P.asIdeal)ˣ := orderOf_dvd_natCard _
  rw [← hu'.eq_orderOf, Nat.card_units] at hd
  simpa [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hd
end ReciprocityTheory.Cheb
