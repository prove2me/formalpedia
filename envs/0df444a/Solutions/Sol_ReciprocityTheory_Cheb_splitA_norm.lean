-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitA_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:08.772157+00:00
-- url     : https://prove2.me/submissions/85381a6c-eb5b-4d57-8034-5c8a929522df

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Theorems.Thm_ReciprocityTheory_Cheb_liesOver_of_under_eq
import Theorems.Thm_ReciprocityTheory_Cheb_prime_dvd_norm_sub_one_cyclotomic

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
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    (Nrm P = Nrm q ∧ ((Nrm q : ℕ) : ZMod l) = 1) ∨ Nrm q ^ 2 ≤ Nrm P := by
  have hlp : l.Prime := Fact.out
  have := liesOver_of_under_eq P q hP
  have hN : Nrm q ^ P.asIdeal.inertiaDeg (𝓞 E) = Nrm P :=
    Ideal.absNorm_pow_inertiaDeg q.asIdeal P.asIdeal
  have hf := Ideal.inertiaDeg_pos P.asIdeal (𝓞 E)
  have hcq : Nat.Coprime (Nrm q) l := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl)
  have hcP : Nat.Coprime (Nrm P) l := hN ▸ Nat.Coprime.pow_left _ hcq
  have hd := prime_dvd_norm_sub_one_cyclotomic E l P hcP
  have hq0 : Nrm q ≠ 0 := by
    intro h; exact hl (h ▸ dvd_zero l)
  rcases Nat.lt_or_ge (P.asIdeal.inertiaDeg (𝓞 E)) 2 with h2 | h2
  · have h1 : P.asIdeal.inertiaDeg (𝓞 E) = 1 := by omega
    rw [h1, pow_one] at hN
    refine Or.inl ⟨hN.symm, ?_⟩
    rw [← hN] at hd
    have h3 : ((Nrm q - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have h4 : Nrm q = (Nrm q - 1) + 1 := by omega
    rw [h4, Nat.cast_add, h3, Nat.cast_one, zero_add]
  · exact Or.inr (hN ▸ Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq0) h2)
end ReciprocityTheory.Cheb
