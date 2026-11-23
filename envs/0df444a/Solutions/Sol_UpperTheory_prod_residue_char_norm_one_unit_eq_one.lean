-- Prove2me | solution 1 for UpperTheory.prod_residue_char_norm_one_unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:04.405843+00:00
-- url     : https://prove2.me/submissions/1c29cedc-bd0f-4085-aeaa-c32f15e242f6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdResidueCharNormOneUnitEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
open scoped Pointwise
private theorem exists_nat_residue {L : Type} [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hn : Ideal.absNorm v.asIdeal = p)
    (x : 𝓞 L) : ∃ a : ℕ, Ideal.Quotient.mk v.asIdeal x = (a : 𝓞 L ⧸ v.asIdeal) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : CharP (𝓞 L ⧸ v.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hv)
  have hcard : Nat.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hn]
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ v.asIdeal)) :=
    (ZMod.castHom (dvd_refl p) _).injective
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨k, hk⟩ := hbij.2 (Ideal.Quotient.mk v.asIdeal x)
  refine ⟨k.val, ?_⟩
  rw [← hk, ZMod.castHom_apply, ZMod.natCast_val]
private theorem smul_natCast_eq {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (n : ℕ) :
    σ • (n : 𝓞 L) = n :=
  map_natCast (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ) n
private theorem stab_trivial {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (hn : Ideal.absNorm w.asIdeal = p) (h2 : ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2)
    (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) : σ = 1 := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  haveI := w.isPrime
  let Q := w.under (𝓞 K)
  haveI := Q.isPrime
  haveI := Q.isMaximal
  haveI : w.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hin : σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
    intro x
    obtain ⟨a, ha⟩ := exists_nat_residue hp w hv hn x
    have h1 : x - (a : 𝓞 L) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, ha, map_natCast]
    have h3 : σ • (x - (a : 𝓞 L)) ∈ w.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul _ _ _ h1
    rw [smul_sub, smul_natCast_eq] at h3
    have h4 := w.asIdeal.sub_mem h3 h1
    rw [sub_sub_sub_cancel_right] at h4
    exact h4
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx Q.asIdeal w.asIdeal Q.ne_bot]
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one]; exact Ideal.map_le_iff_le_comap.2 le_rfl
    · intro h
      apply h2
      have h1 : ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
        show ((p : ℕ) : 𝓞 K) ∈ Ideal.under (𝓞 K) w.asIdeal
        rw [Ideal.mem_under, map_natCast]; exact hv
      have h5 := h (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h1)
      rwa [map_natCast] at h5
  have hc : Nat.card (w.asIdeal.inertia (L ≃ₐ[K] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn Q.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal w.asIdeal (L ≃ₐ[K] L), he]
  rw [Subgroup.card_eq_one.1 hc] at hin
  exact Subgroup.mem_bot.1 hin
end

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Pointwise
namespace UpperTheory
theorem _root_.solution :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (p : ℕ), p.Prime →
      ∀ (Q : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∈ S ↔ w.under (𝓞 K) = Q) →
      (∀ w ∈ S, Ideal.absNorm w.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2) →
      ∀ (ω : (ZMod p)ˣ →* ℂˣ) (θ : ∀ w : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ),
      (∀ w ∈ S, ∀ (a : ℕ) (ha : a.Coprime p), ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ,
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧ θ w b = ω (ZMod.unitOfCoprime a ha)) →
      ∀ u : (𝓞 L)ˣ, Algebra.norm K ((u : 𝓞 L) : L) = 1 →
        ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom u) = 1 := by
  intro K L _ _ _ _ _ _ p hp Q S memS hs ω θ hθ ζ hζ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have overp : ∀ w ∈ S, ((p : ℕ) : 𝓞 L) ∈ w.asIdeal := by
    intro w hw
    rw [← (hs w hw).1]
    exact Ideal.absNorm_mem _
  rcases S.eq_empty_or_nonempty with hE | ⟨w₀, hw₀⟩
  · rw [hE, Finset.prod_empty]

  have hres : ∀ w ∈ S, ∃ a : ℕ, Ideal.Quotient.mk w.asIdeal (ζ : 𝓞 L) = (a : 𝓞 L ⧸ w.asIdeal) := fun w hw =>
    exists_nat_residue hp w (overp w hw) (hs w hw).1 _
  choose! a ha using hres
  have hcop : ∀ w ∈ S, (a w).Coprime p := by
    intro w hw
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
    have h0 : ((a w : ℕ) : 𝓞 L ⧸ w.asIdeal) = 0 := by
      obtain ⟨c, hc⟩ := hd
      rw [hc, Nat.cast_mul, ← map_natCast (Ideal.Quotient.mk w.asIdeal) p,
        Ideal.Quotient.eq_zero_iff_mem.2 (overp w hw), zero_mul]
    have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (ζ : 𝓞 L)) := ζ.isUnit.map _
    rw [ha w hw, h0] at hu
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    exact not_isUnit_zero hu

  have hσ : ∀ w ∈ S, ∃ σ : L ≃ₐ[K] L, σ • w.asIdeal = w₀.asIdeal := by
    intro w hw
    haveI := w.isPrime
    haveI := w₀.isPrime
    haveI : w.asIdeal.LiesOver Q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal ((memS w).1 hw).symm⟩
    haveI : w₀.asIdeal.LiesOver Q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal ((memS w₀).1 hw₀).symm⟩
    exact Ideal.exists_smul_eq_of_isGaloisGroup Q.asIdeal w.asIdeal w₀.asIdeal (L ≃ₐ[K] L)
  choose! σ hσw using hσ

  have hσres : ∀ w ∈ S, Ideal.Quotient.mk w₀.asIdeal (σ w • (ζ : 𝓞 L)) = (a w : 𝓞 L ⧸ w₀.asIdeal) := by
    intro w hw
    have h1 : (ζ : 𝓞 L) - (a w : 𝓞 L) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, ha w hw, map_natCast]
    have h2 : σ w • ((ζ : 𝓞 L) - (a w : 𝓞 L)) ∈ w₀.asIdeal := by
      rw [← hσw w hw]; exact Ideal.smul_mem_pointwise_smul _ _ _ h1
    rw [smul_sub, smul_natCast_eq] at h2
    rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal)]
    exact Ideal.Quotient.eq.2 h2

  have hprod : ∏ w ∈ S, σ w • (ζ : 𝓞 L) = 1 := by
    have hre : ∏ w ∈ S, σ w • (ζ : 𝓞 L) = ∏ τ : L ≃ₐ[K] L, τ • (ζ : 𝓞 L) := by
      refine Finset.prod_bij (fun w _ => σ w) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro w₁ h₁ w₂ h₂ h'
        apply HeightOneSpectrum.ext
        rw [eq_inv_smul_iff.2 (hσw w₁ h₁), eq_inv_smul_iff.2 (hσw w₂ h₂), h']
      · intro τ _
        haveI := w₀.isPrime
        have hne : τ⁻¹ • w₀.asIdeal ≠ ⊥ := by
          intro h
          apply w₀.ne_bot
          rw [← smul_inv_smul τ w₀.asIdeal, h]
          ext x
          simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        let w : HeightOneSpectrum (𝓞 L) := ⟨τ⁻¹ • w₀.asIdeal, inferInstance, hne⟩
        have hw : w ∈ S := by
          rw [memS, ← (memS w₀).1 hw₀]
          apply HeightOneSpectrum.ext
          exact Ideal.under_smul (𝓞 K) w₀.asIdeal τ⁻¹
        refine ⟨w, hw, ?_⟩
        have h1 := stab_trivial hp w (overp w hw) (hs w hw).1 (hs w hw).2 (τ⁻¹ * σ w)
          (by rw [mul_smul, hσw w hw])
        exact (inv_mul_eq_one.1 h1).symm
      · intro w hw
        rfl
    rw [hre]
    apply RingOfIntegers.ext
    have h := Algebra.norm_eq_prod_automorphisms K ((ζ : 𝓞 L) : L)
    rw [hζ, map_one] at h
    have h' : ∀ τ : L ≃ₐ[K] L, algebraMap (𝓞 L) L (τ • (ζ : 𝓞 L)) = τ ((ζ : 𝓞 L) : L) :=
      fun τ => rfl
    show algebraMap (𝓞 L) L (∏ τ : L ≃ₐ[K] L, τ • (ζ : 𝓞 L)) = algebraMap (𝓞 L) L 1
    rw [map_prod, map_one]
    exact (Finset.prod_congr rfl fun τ _ => h' τ).trans h.symm

  haveI : w₀.asIdeal.IsMaximal := w₀.isMaximal
  haveI : CharP (𝓞 L ⧸ w₀.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal)]; exact Ideal.Quotient.eq_zero_iff_mem.2 (overp w₀ hw₀))
  have hmod : ∏ w ∈ S, ((a w : ℕ) : ZMod p) = 1 := by
    apply (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ w₀.asIdeal)).injective
    rw [map_prod, map_one]
    have : ∏ w ∈ S, (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ w₀.asIdeal)) ((a w : ℕ) : ZMod p) =
        ∏ w ∈ S, Ideal.Quotient.mk w₀.asIdeal (σ w • (ζ : 𝓞 L)) :=
      Finset.prod_congr rfl fun w hw => by rw [map_natCast, hσres w hw]
    rw [this, ← map_prod, hprod, map_one]

  let u : HeightOneSpectrum (𝓞 L) → (ZMod p)ˣ := fun w =>
    if h : (a w).Coprime p then ZMod.unitOfCoprime (a w) h else 1
  have hval : ∀ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = ω (u w) := by
    intro w hw
    simp only [u, dif_pos (hcop w hw)]
    obtain ⟨b, hb, hθb⟩ := hθ w hw (a w) (hcop w hw)
    rw [← hθb]
    congr 1
    apply Units.ext
    rw [hb, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ha w hw, map_natCast]
  rw [Finset.prod_congr rfl hval, ← map_prod]
  have hu1 : ∏ w ∈ S, u w = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one, ← hmod]
    refine Finset.prod_congr rfl fun w hw => ?_
    simp only [u, dif_pos (hcop w hw), ZMod.coe_unitOfCoprime]
  rw [hu1, map_one]
end UpperTheory
