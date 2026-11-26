-- Prove2me | solution 1 for Polynomial.exists_continuousMulEquiv_galois_maxUnramified_algClosed_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T09:15:56.107007+00:00
-- url     : https://prove2.me/submissions/cce73431-bfed-48f3-96a6-16f4ad9b37f8

import Mathlib
import Definitions.Def_RPLib_FX_EtPi1Geo_03

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPi1GeoU

open Polynomial IntermediateField CurveCoh RamanujanPetersson.EtPi1Geo

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

theorem maxUnram_eq (A K : Type) [CommRing A] [Field K] [Algebra A K] :
    maxUnram A K = ⨆ L : {L : IntermediateField K (AlgebraicClosure K) //
        FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure A L), P.IsPrime →
          ∀ g : L ≃ₐ[K] L,
            (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1 := by
  have hset : unramSet A K =
      {L : IntermediateField K (AlgebraicClosure K) | FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure A L), P.IsPrime →
          ∀ g : L ≃ₐ[K] L,
            (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = g b - b) → g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (unram_iff A K L))
  rw [maxUnram, hset]
  rfl

section PhiMap

variable (p : ℕ) [Fact p.Prime] (Fq k : Type) [Field Fq] [Fintype Fq] [CharP Fq p] [Field k] [IsAlgClosed k]
  [Algebra Fq k] [Algebra.IsAlgebraic Fq k]

omit [IsAlgClosed k] in
theorem phiA1_map' (P : Fq[X]) : phiA1 p Fq k (RatFunc k) (algebraMap k[X] (RatFunc k) (P.map (algebraMap Fq k))) =
    algebraMap (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) (algebraMap Fq[X] (RatFunc Fq) P) := by
  letI := algRF Fq k (RatFunc k)
  haveI := isAlgebraic_A1 Fq k (RatFunc k) p
  have h : algebraMap k[X] (RatFunc k) (P.map (algebraMap Fq k)) =
      algebraMap (RatFunc Fq) (RatFunc k) (algebraMap Fq[X] _ P) :=
    (IsFractionRing.lift_algebraMap (injective_PF Fq k (RatFunc k)) P).symm
  rw [h]
  exact (phiFK (RatFunc Fq) (RatFunc k)).commutes _

end PhiMap

theorem main
    (Fq : Type) [Field Fq] [Fintype Fq]
    (k : Type) [Field k] [IsAlgClosed k] [Algebra Fq k] [Algebra.IsAlgebraic Fq k]
    (KU : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hKU : KU = ⨆ L : {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) //
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (Polynomial Fq) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (Polynomial Fq) L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (KUk : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)))
    (hKUk : KUk = ⨆ L : {L : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)) //
        FiniteDimensional (RatFunc k) L ∧ IsGalois (RatFunc k) L ∧
        ∀ P : Ideal (integralClosure (Polynomial k) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc k] L,
            (∀ b : integralClosure (Polynomial k) L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hΓ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ n : ℕ, 0 < n ∧ x ^ (Fintype.card Fq) ^ n = x) → g x = x) :
    ∃ ι : KUk ≃+* KU,
      (∀ f : Polynomial Fq,
        ι (algebraMap (RatFunc k) KUk (algebraMap (Polynomial k) (RatFunc k) (f.map (algebraMap Fq k)))) =
          algebraMap (RatFunc Fq) KU (algebraMap (Polynomial Fq) (RatFunc Fq) f)) ∧
      (∀ x : KU, (∃ n : ℕ, 0 < n ∧ x ^ (Fintype.card Fq) ^ n = x) →
        ∃ c : k, ι (algebraMap (RatFunc k) KUk (algebraMap k (RatFunc k) c)) = x) ∧
      ∃ e : (KUk ≃ₐ[RatFunc k] KUk) ≃ₜ* Γ,
        ∀ (σ : KUk ≃ₐ[RatFunc k] KUk) (x : KU), (e σ : KU ≃ₐ[RatFunc Fq] KU) x = ι (σ (ι.symm x)) := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists Fq
  have := hchar
  have : Fact p.Prime := ⟨CharP.char_is_prime Fq p⟩
  obtain ⟨e, -, hq⟩ := FiniteField.card Fq p
  have hKU' : KU = maxUnram Fq[X] (RatFunc Fq) := hKU.trans (maxUnram_eq _ _).symm
  subst hKU'
  have hKUk' : KUk = maxUnram k[X] (RatFunc k) := hKUk.trans (maxUnram_eq _ _).symm
  subst hKUk'
  have hΓ' : Γ = pi1geo Fq[X] (RatFunc Fq) (Fintype.card Fq) := by
    ext g
    rw [hΓ, mem_pi1geo]
    rfl
  subst hΓ'
  refine ⟨iotaA1 p Fq k (RatFunc k), fun f => ?_, fun x hx => ?_, cmpA1 p Fq k (RatFunc k), fun σ x => ?_⟩
  · apply Subtype.ext
    rw [iotaA1_algebraMap, phiA1_map']
    rfl
  · obtain ⟨n, hn, hxn⟩ := hx
    have hc : IsConst p (x : AlgebraicClosure (RatFunc Fq)) := by
      refine ⟨(e : ℕ) * n, Nat.mul_pos e.pos hn, ?_⟩
      rw [pow_mul, ← hq]
      exact congrArg Subtype.val hxn
    obtain ⟨c, hc⟩ := kA1_surj p Fq k (RatFunc k) _ hc
    refine ⟨c, Subtype.ext ?_⟩
    rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, iotaA1_C, hc]
  · exact cmpA1_apply p Fq k (RatFunc k) σ x

end RamanujanPetersson.EtPi1GeoU

end

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq]
    (k : Type) [Field k] [IsAlgClosed k] [Algebra Fq k] [Algebra.IsAlgebraic Fq k]
    (KU : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hKU : KU = ⨆ L : {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) //
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (Polynomial Fq) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (Polynomial Fq) L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (KUk : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)))
    (hKUk : KUk = ⨆ L : {L : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)) //
        FiniteDimensional (RatFunc k) L ∧ IsGalois (RatFunc k) L ∧
        ∀ P : Ideal (integralClosure (Polynomial k) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc k] L,
            (∀ b : integralClosure (Polynomial k) L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hΓ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ n : ℕ, 0 < n ∧ x ^ (Fintype.card Fq) ^ n = x) → g x = x) :
    ∃ ι : KUk ≃+* KU,
      (∀ f : Polynomial Fq,
        ι (algebraMap (RatFunc k) KUk (algebraMap (Polynomial k) (RatFunc k) (f.map (algebraMap Fq k)))) =
          algebraMap (RatFunc Fq) KU (algebraMap (Polynomial Fq) (RatFunc Fq) f)) ∧
      (∀ x : KU, (∃ n : ℕ, 0 < n ∧ x ^ (Fintype.card Fq) ^ n = x) →
        ∃ c : k, ι (algebraMap (RatFunc k) KUk (algebraMap k (RatFunc k) c)) = x) ∧
      ∃ e : (KUk ≃ₐ[RatFunc k] KUk) ≃ₜ* Γ,
        ∀ (σ : KUk ≃ₐ[RatFunc k] KUk) (x : KU), (e σ : KU ≃ₐ[RatFunc Fq] KU) x = ι (σ (ι.symm x)) := by
  exact RamanujanPetersson.EtPi1GeoU.main Fq k KU hKU KUk hKUk Γ hΓ
