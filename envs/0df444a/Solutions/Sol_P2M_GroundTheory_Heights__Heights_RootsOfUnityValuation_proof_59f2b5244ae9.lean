-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_proof_59f2b5244ae9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:04.992505+00:00
-- url     : https://prove2.me/submissions/5cb2f8fa-2c34-4fcc-a581-9975710f6473

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PRootsOfUnityValuation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_one_sub_pow_associated_33a809d88cd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_sub_pow_associated_fa5ff3311338

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RootsOfUnityValuation
theorem _root_.solution : RootsOfUnityValuation.Statement := by
  intro E _ _ l hl ζ hζ c c' hc hc' hne
  have : NeZero l := ⟨hl.ne_zero⟩
  have hmem : ∀ x : 𝓞 E, x ^ l = 1 → x ∈ Algebra.adjoin ℤ {ζ} := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) i
  let z : Algebra.adjoin ℤ {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton ℤ ζ⟩
  have hz : IsPrimitiveRoot z l :=
    IsPrimitiveRoot.of_map_of_injective (f := (Algebra.adjoin ℤ {ζ}).val) hζ Subtype.val_injective
  let a : Algebra.adjoin ℤ {ζ} := ⟨c, hmem c hc⟩
  let a' : Algebra.adjoin ℤ {ζ} := ⟨c', hmem c' hc'⟩
  have ha : a ^ l = 1 := Subtype.ext (by simpa [a] using hc)
  have ha' : a' ^ l = 1 := Subtype.ext (by simpa [a'] using hc')
  have haa : a ≠ a' := fun h => hne (congrArg Subtype.val h)
  refine ⟨?_, ?_, fun v => ?_⟩
  · obtain ⟨u, hu⟩ := hz.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hl
      ((Polynomial.mem_nthRootsFinset hl.pos 1).2 ha) ((Polynomial.mem_nthRootsFinset hl.pos 1).2 ha')
      haa
    refine ⟨-u, ?_⟩
    have h := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, z, a, a'] at h
    rw [← h, Units.val_neg, NegMemClass.coe_neg]
    ring
  · obtain ⟨w, hw⟩ := RootsOfUnityValuation.one_sub_pow_associated hl hz
    refine ⟨w⁻¹, ?_⟩
    have key : (1 - z) ^ (l - 1) = ((w⁻¹ : (Algebra.adjoin ℤ {ζ})ˣ) : Algebra.adjoin ℤ {ζ}) * l := by
      rw [← hw, mul_comm, Units.mul_inv_cancel_right]
    have h := congrArg Subtype.val key
    simpa [z] using h
  · have hass := RootsOfUnityValuation.sub_pow_associated hl hζ hc hc' hne
    have hv : ∀ x y : 𝓞 E, x ^ l = 1 → y ^ l = 1 → x ≠ y → x - y ∈ v.asIdeal →
        (l : 𝓞 E) ∈ v.asIdeal := by
      intro x y hx hy hxy hm
      obtain ⟨t, ht⟩ := (RootsOfUnityValuation.sub_pow_associated hl hζ hx hy hxy).dvd
      rw [ht]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hm _ (by have := hl.two_le; omega))
    have hcard : 0 < Nat.card (𝓞 E ⧸ v.asIdeal) := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
      omega
    have : Finite (𝓞 E ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero hcard.ne'
    refine ⟨fun hl' => ⟨?_, ?_, ?_⟩, fun hl' => ⟨?_, ?_⟩⟩
    · rw [RingOfIntegers.coe_eq_algebraMap, NumberField.HeightOneSpectrum.adicAbv,
        IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]
      exact fun hm => hl' (hv c c' hc hc' hne hm)
    · intro x hx y hy hxy
      by_contra hne'
      exact hl' (hv x y hx hy hne' (Ideal.Quotient.eq.1 hxy))
    · have hunit : ∀ i : ℕ, Ideal.Quotient.mk v.asIdeal (ζ ^ i) ≠ 0 := by
        intro i h
        rw [Ideal.Quotient.eq_zero_iff_mem] at h
        exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((hζ.isUnit NeZero.out).pow i))
      let f : Option (Fin l) → 𝓞 E ⧸ v.asIdeal :=
        fun o => o.elim 0 (fun i => Ideal.Quotient.mk v.asIdeal (ζ ^ (i : ℕ)))
      have hroot : ∀ i : ℕ, (ζ ^ i) ^ l = 1 := fun i => by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      have hinj : Function.Injective f := by
        rintro (_ | i) (_ | j) h
        · rfl
        · exact absurd h.symm (hunit j)
        · exact absurd h (hunit i)
        · congr 1
          apply Fin.ext
          apply hζ.pow_inj i.2 j.2
          by_contra hne'
          exact hl' (hv _ _ (hroot i) (hroot j) hne' (Ideal.Quotient.eq.1 h))
      have := Nat.card_le_card_of_injective f hinj
      simpa [Finite.card_option] using this
    · obtain ⟨w, hw⟩ := hass
      have hwE := congrArg (algebraMap (𝓞 E) E) hw
      rw [map_mul, map_pow, map_natCast] at hwE
      have hw1 : NumberField.HeightOneSpectrum.adicAbv E v (algebraMap (𝓞 E) E (w : 𝓞 E)) = 1 := by
        rw [NumberField.HeightOneSpectrum.adicAbv,
          IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]
        exact fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h w.isUnit)
      rw [← hwE, map_mul, map_pow, hw1, mul_one]
    · have : Fact l.Prime := ⟨hl⟩
      have h0 : ((l : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact hl'
      have : CharP (𝓞 E ⧸ v.asIdeal) l := (CharP.charP_iff_prime_eq_zero hl).2 h0
      have := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl l) (𝓞 E ⧸ v.asIdeal)).injective
      simpa [Nat.card_zmod] using this
end RootsOfUnityValuation
end GroundTheory.Heights₂.Heights
