-- Prove2me | solution 1 for Representation.finrank_compactH2_sub_finrank_compactH1_eq_finrank_sub_swanConductor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:12:14.968802+00:00
-- url     : https://prove2.me/submissions/95bad9a2-cf8e-4f9f-b3fb-ca4e387036cc

import Mathlib
import Definitions.Def_RPLib_FX_GOSC_BR

set_option autoImplicit false

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (KU : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hKU : KU = ⨆ L : {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) //
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L,
              ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hΓ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (S : Type)
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring
      (RatFunc Fq)) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring
        (RatFunc Fq)) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
          b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
        b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hI : ∀ s (g : KU ≃ₐ[RatFunc Fq] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
        ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hMf : FiniteDimensional (RatFunc Fq) Mf ∧ IsGalois (RatFunc Fq) Mf ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) Mf), P.IsPrime →
        ∀ g : Mf ≃ₐ[RatFunc Fq] Mf,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) Mf,
            ∃ c ∈ P, (c : Mf) = g b - b) → g = 1)
    (Gf : Type) [Group Gf] [Finite Gf] (π : (KU ≃ₐ[RatFunc Fq] KU) →* Gf)
    (hπ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, π g = 1 ↔ ∀ x : KU, (x : AlgebraicClosure (RatFunc Fq)) ∈ Mf → g x = x)
    (hπs : Function.Surjective π)
    (ι : (Mf ≃ₐ[RatFunc Fq] Mf) →* Gf)
    (hι : ∀ (g : KU ≃ₐ[RatFunc Fq] KU) (σ : Mf ≃ₐ[RatFunc Fq] Mf),
      (∀ (x : KU) (hx : (x : AlgebraicClosure (RatFunc Fq)) ∈ Mf),
        ((g x : KU) : AlgebraicClosure (RatFunc Fq)) = ((σ ⟨x, hx⟩ : Mf) : AlgebraicClosure (RatFunc Fq))) →
      π g = ι σ)
    (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq)
    (M : Type) [AddCommGroup M] [Module (ZMod l) M] [Module.Finite (ZMod l) M]
    (τ : Representation (ZMod l) Gf M)
    (Z : Submodule (ZMod l) ((Γ → M) × (S → M)))
    (hZ : ∀ x : (Γ → M) × (S → M), x ∈ Z ↔
      IsLocallyConstant x.1 ∧ (∀ g h : Γ, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
        ∀ s (g : Γ), (g : KU ≃ₐ[RatFunc Fq] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s)
    (B : Submodule (ZMod l) ((Γ → M) × (S → M)))
    (hB : ∀ x : (Γ → M) × (S → M), x ∈ B ↔
      ∃ m : M, (∀ g : Γ, x.1 g = τ (π g) m - m) ∧ ∀ s, x.2 s = m)
    (Q0 : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf)) :
    (Module.finrank (ZMod l) (Representation.Coinvariants ((τ.comp π).comp Γ.subtype)) : ℚ) -
        Module.finrank (ZMod l) (Z ⧸ B.comap Z.subtype) =
      Module.finrank (ZMod l) M -
        ∑ᶠ i : ℕ,
          (Nat.card {σ : Mf ≃ₐ[RatFunc Fq] Mf //
              ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal ^ (i + 2), (c : Mf) = σ b - b} : ℚ) /
            (Nat.card {σ : Mf ≃ₐ[RatFunc Fq] Mf //
              ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal, (c : Mf) = σ b - b} : ℚ) *
          ((Module.finrank (ZMod l) M : ℚ) -
            Module.finrank (ZMod l) ↥(⨅ (σ : Mf ≃ₐ[RatFunc Fq] Mf)
              (_ : ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal ^ (i + 2), (c : Mf) = σ b - b),
              LinearMap.ker (τ (ι σ) - 1))) := by
  exact RamanujanPetersson.GOSCU.main Fq KU hKU Γ hΓ S P hP hcover hdisj I hI Mf hMf Gf π hπ hπs ι hι l hlq M τ Z hZ B hB Q0
