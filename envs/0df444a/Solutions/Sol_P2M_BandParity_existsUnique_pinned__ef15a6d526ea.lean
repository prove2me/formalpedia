-- Prove2me | solution 1 for P2M_BandParity_existsUnique_pinned__ef15a6d526ea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:23.604066+00:00
-- url     : https://prove2.me/submissions/cb6c8159-8100-480f-9f64-1d6d54574e37

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
public import Theorems.Thm_BandParity_isPrimitiveRoot_gi
public import Theorems.Thm_BandParity_orderOf_pow_three
public import Theorems.Thm_BandParity_quartic_ext
public import Theorems.Thm_BandParity_pow_three_apply_of_pm_gi
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_gi_ne_neg_gi
public import Theorems.Thm_BandParity_quartic_apply_generator
public import Theorems.Thm_BandParity_quartic_apply_two
public import Theorems.Thm_BandParity_two_eq_generator_pow_odd


set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := by
  have hdvd : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd isPrimitiveRoot_gi
  have existence : ∃ χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := by
    rcases quartic_apply_two χ hχ hp8 with h | h
    · exact ⟨χ, hχ, h⟩
    · refine ⟨χ ^ 3, orderOf_pow_three hχ, ?_⟩
      rw [pow_three_apply_of_pm_gi χ (Or.inr h), h, neg_neg]
  obtain ⟨χ, hχ, h2⟩ := existence
  refine ⟨χ, ⟨hχ, h2⟩, fun ψ ⟨hψ, h2'⟩ => ?_⟩
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  obtain ⟨e, he, hge⟩ := two_eq_generator_pow_odd hp8 hg
  refine quartic_ext hg ?_
  rcases quartic_apply_generator χ hχ hg with hc | hc <;>
    rcases quartic_apply_generator ψ hψ hg with hs | hs
  · rw [hc, hs]
  · exfalso
    have e1 : ψ 2 = (-gi) ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hs]
    have e2 : χ 2 = gi ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hc]
    rw [h2', Odd.neg_pow he, ← e2, h2] at e1
    exact gi_ne_neg_gi e1
  · exfalso
    have e1 : ψ 2 = gi ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hs]
    have e2 : χ 2 = (-gi) ^ e := by rw [← hge, Units.val_pow_eq_pow_val, map_pow, hc]
    rw [Odd.neg_pow he, h2] at e2
    rw [h2'] at e1
    rw [← e1] at e2
    exact gi_ne_neg_gi e2
  · rw [hc, hs]
end BandParity
