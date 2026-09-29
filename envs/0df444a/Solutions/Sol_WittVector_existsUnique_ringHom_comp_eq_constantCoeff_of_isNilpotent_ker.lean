-- Prove2me | solution 1 for WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a327fc99-43f7-587b-80ab-df99dde36380

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker

set_option autoImplicit false

universe u

namespace WittLift

open WittVector

variable {p : ℕ} [hp : Fact p.Prime]

theorem isAdicComplete_span_of_pow_eq_zero {B : Type u} [CommRing B] (x : B) {N : ℕ} (hN : x ^ N = 0) :
    IsAdicComplete (Ideal.span {x}) B := by
  have hbot : ∀ n, N ≤ n → (Ideal.span {x} ^ n • ⊤ : Submodule B B) = ⊥ := by
    intro n hn
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_eq_bot]
    exact pow_eq_zero_of_le hn hN
  haveI : IsHausdorff (Ideal.span {x}) B := ⟨fun y hy => by
    have := hy N
    rw [hbot N le_rfl, SModEq.bot] at this
    exact this⟩
  haveI : IsPrecomplete (Ideal.span {x}) B := ⟨fun f hf => by
    refine ⟨f N, fun n => ?_⟩
    rcases le_or_gt n N with h | h
    · exact hf h
    · have := hf h.le
      rw [hbot N le_rfl, SModEq.bot] at this
      rw [this]⟩
  exact ⟨⟩

end WittLift

open WittVector in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B : Type u) [CommRing B] (ρ : B →+* k) (hρ : Function.Surjective ρ) (hnil : IsNilpotent (RingHom.ker ρ)) :
    ∃! f : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff := by
  classical
  obtain ⟨N, hN⟩ := hnil
  set I : Ideal B := RingHom.ker ρ with hIdef
  have hIN : I ^ N = ⊥ := by simpa using hN
  have hIN1 : I ^ (N + 1) = ⊥ := by rw [pow_succ, hIN, Ideal.bot_mul]

  have hpI : ((p : ℕ) : B) ∈ I := by
    rw [hIdef, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hpN : ((p : ℕ) : B) ^ N = 0 := by
    have : ((p : ℕ) : B) ^ N ∈ I ^ N := Ideal.pow_mem_pow hpI N
    rwa [hIN, Ideal.mem_bot] at this

  haveI hpu : Fact (¬ IsUnit ((p : ℕ) : B)) := ⟨fun h => by
    have := h.map ρ
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this⟩
  haveI : IsAdicComplete (Ideal.span {((p : ℕ) : B)}) B := WittLift.isAdicComplete_span_of_pow_eq_zero _ hpN

  have huniq : ∀ f g : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff → ρ.comp g = WittVector.constantCoeff → f = g := by
    intro f g hf hg
    apply WittVector.eq_of_apply_teichmuller_eq f g ⟨N, hpN⟩
    intro x

    set y : k := (iterateFrobeniusEquiv k p N).symm x with hy
    have hx : x = y ^ p ^ N := by
      rw [hy, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    have hmod : f (teichmuller p y) ≡ g (teichmuller p y) [SMOD I] := by
      rw [SModEq.sub_mem, hIdef, RingHom.mem_ker, map_sub, sub_eq_zero]
      have h1 := congrArg (fun φ : WittVector p k →+* k => φ (teichmuller p y)) hf
      have h2 := congrArg (fun φ : WittVector p k →+* k => φ (teichmuller p y)) hg
      simp only [RingHom.comp_apply] at h1 h2
      rw [h1, h2]
    have := SModEq.pow_pow_add_one hpI hmod N
    rw [hIN1, SModEq.bot] at this
    rw [hx, map_pow, map_pow, map_pow, this]

  set ρbar : ModP B p →+* k := Ideal.Quotient.lift (Ideal.span {((p : ℕ) : B)}) ρ (fun b hb => by
      rw [Ideal.mem_span_singleton] at hb
      obtain ⟨c, rfl⟩ := hb
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]) with hρbar
  have hρbar_mk : ∀ b : B, ρbar (Ideal.Quotient.mk _ b) = ρ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have hρbar_surj : Function.Surjective ρbar := by
    intro a; obtain ⟨b, rfl⟩ := hρ a; exact ⟨Ideal.Quotient.mk _ b, hρbar_mk b⟩

  set ψ : ModP B p →+* ModP B p := iterateFrobenius (ModP B p) p N with hψ
  have hψker : ∀ z : ModP B p, z ∈ RingHom.ker ρbar → ψ z = 0 := by
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, hρbar_mk] at hz
    have hb : b ^ N = 0 := by
      have : b ^ N ∈ I ^ N := Ideal.pow_mem_pow (by rw [hIdef, RingHom.mem_ker]; exact hz) N
      rwa [hIN, Ideal.mem_bot] at this
    rw [hψ, iterateFrobenius_def, ← map_pow]
    rw [pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hb, map_zero]

  set ψ' : k →+* ModP B p :=
    (Ideal.Quotient.lift (RingHom.ker ρbar) ψ hψker).comp (RingHom.quotientKerEquivOfSurjective hρbar_surj).symm.toRingHom with hψ'
  have hψ'_apply : ∀ z : ModP B p, ψ' (ρbar z) = z ^ p ^ N := by
    intro z
    rw [hψ', RingHom.comp_apply]
    have : (RingHom.quotientKerEquivOfSurjective hρbar_surj).symm.toRingHom (ρbar z) = Ideal.Quotient.mk _ z := by
      apply (RingHom.quotientKerEquivOfSurjective hρbar_surj).injective
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk, hψ, iterateFrobenius_def]

  set sbar : k →+* ModP B p := ψ'.comp (iterateFrobeniusEquiv k p N).symm.toRingHom with hsbar
  have hsbar : ∀ a : k, ρbar (sbar a) = a := by
    intro a
    set a' : k := (iterateFrobeniusEquiv k p N).symm a with ha'
    obtain ⟨z, hz⟩ := hρbar_surj a'
    have : sbar a = ψ' a' := by rw [hsbar, RingHom.comp_apply]; rfl
    rw [this, ← hz, hψ'_apply, map_pow, hz, ha', ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]

  let e : k →+* PreTilt B p := Perfection.lift p k (ModP B p) sbar
  have he0 : ∀ a : k, PreTilt.coeff 0 (e a) = sbar a := by
    intro a
    rw [PreTilt.coeff_def]
    show Perfection.coeff (ModP B p) p 0 (Perfection.lift p k (ModP B p) sbar a) = sbar a
    simp [Perfection.lift]
  let F : WittVector p k →+* B := (WittVector.fontaineTheta B p).comp (WittVector.map e)
  have hF : ρ.comp F = WittVector.constantCoeff := by
    apply WittVector.eq_of_apply_teichmuller_eq _ _ (⟨1, by rw [pow_one, CharP.cast_eq_zero]⟩ : IsNilpotent ((p : ℕ) : k))
    intro x
    rw [RingHom.comp_apply]
    show ρ (WittVector.fontaineTheta B p (WittVector.map e (teichmuller p x))) = WittVector.constantCoeff (teichmuller p x)
    rw [WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
    have : ρ (PreTilt.untilt (e x)) = ρbar (Ideal.Quotient.mk _ (PreTilt.untilt (e x))) := (hρbar_mk _).symm
    rw [this, PreTilt.mk_untilt_eq_coeff_zero, he0, hsbar]
    show x = (teichmuller p x).coeff 0
    rw [WittVector.teichmuller_coeff_zero]
  exact ⟨F, hF, fun g hg => huniq g F hg hF⟩

#print axioms solution

end S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker
end P2MW
export P2MW.S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker (solution)
