-- Prove2me | solution 1 for WeierstrassEllipticZeta.frontier_projection_count_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T22:57:46.782164+00:00
-- url     : https://prove2.me/submissions/21ea700f-7f5c-4eff-9340-3e483b8b750d

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Classical

private lemma projection_pullback_ncard
    {R A V : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup V] [Module R V]
    (φ : A →ₗ[R] V) (H : Submodule R V) (X : Finset A) :
    ((H.comap φ).mkQ '' (X : Set A)).ncard =
      (H.mkQ '' (φ '' (X : Set A))).ncard := by
  let f := (H.comap φ).mapQ H φ le_rfl
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    exact (Submodule.ker_mapQ _ _ _ _).trans (Submodule.mkQ_map_self _)
  have himage : f '' ((H.comap φ).mkQ '' (X : Set A)) =
      H.mkQ '' (φ '' (X : Set A)) := by
    rw [Set.image_image, Set.image_image]
    rfl
  rw [← himage, Set.ncard_image_of_injective _ hf]

private lemma projection_quotient_ncard_mono
    {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (K Λ : Submodule R A) (hK : K ≤ Λ) (X : Finset A) :
    (Λ.mkQ '' (X : Set A)).ncard ≤ (K.mkQ '' (X : Set A)).ncard := by
  have himage : Λ.mkQ '' (X : Set A) =
      Submodule.factor hK '' (K.mkQ '' (X : Set A)) := by
    rw [Set.image_image]
    rfl
  rw [himage]
  exact Set.ncard_image_le (X.finite_toSet.image K.mkQ)

/-- The subgroup estimate is equivalent to a point-count or period-class-count bound. -/
theorem solution
    (G : Frontier.Geometry) (C : ℝ) (hC : 0 ≤ C)
    (m n U : ℕ) (hn : 1 ≤ n) (X : Finset ℂ) :
    Frontier.SubgroupBound G C m n U X ↔
      ((U + 1 : ℕ) : ℝ) * X.card ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∨
      ((U + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
        C * (n : ℝ) ^ 2 := by
  let φ := extensionCurve G.L.lattice G.η
  let A := extensionAdditiveProjection G.L.lattice G.η
  let E := extensionEllipticProjection G.L.lattice G.η
  have hA : A.comp φ = LinearMap.id := by ext; rfl
  have hE : E.comp φ = G.L.lattice.mkQ := by ext; rfl
  have hkerA : (LinearMap.ker A).comap φ = ⊥ := by
    rw [← LinearMap.ker_comp, hA, LinearMap.ker_id]
  have hkerE : (LinearMap.ker E).comap φ = G.L.lattice := by
    rw [← LinearMap.ker_comp, hE, Submodule.ker_mkQ]
  have hbot : ((⊥ : Submodule ℤ ℂ).mkQ '' (X : Set ℂ)).ncard = X.card := by
    have hinj : Function.Injective (⊥ : Submodule ℤ ℂ).mkQ :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ _)
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
  have hcardA : ((LinearMap.ker A).mkQ '' (φ '' (X : Set ℂ))).ncard = X.card := by
    rw [← projection_pullback_ncard φ (LinearMap.ker A) X, hkerA, hbot]
  have hcardE : ((LinearMap.ker E).mkQ '' (φ '' (X : Set ℂ))).ncard =
      (G.L.lattice.mkQ '' (X : Set ℂ)).ncard := by
    rw [← projection_pullback_ncard φ (LinearMap.ker E) X, hkerE]
  constructor
  · rintro ⟨H, a, b, hprofile, hb, hbound⟩
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ b ≤ (n : ℝ) ^ 2 := pow_le_pow_right₀ hn' hb
    have hcard := projection_pullback_ncard φ H X
    rcases hprofile with ⟨rfl, hH⟩ | ⟨rfl, hH⟩
    · left
      have hK : H.comap φ = ⊥ := by
        apply le_antisymm _ bot_le
        intro z hz
        have hzero := hH hz
        change z = 0 at hzero
        exact hzero
      rw [hK, hbot] at hcard
      rw [← hcard, pow_one] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_left hpow
        (mul_nonneg hC (Nat.cast_nonneg m)))
    · right
      have hK : H.comap φ ≤ G.L.lattice := by
        intro z hz
        have hzero := hH hz
        change G.L.lattice.mkQ z = 0 at hzero
        simpa using hzero
      have hcount := projection_quotient_ncard_mono (H.comap φ) G.L.lattice hK X
      rw [hcard] at hcount
      have hcount' : ((G.L.lattice.mkQ '' (X : Set ℂ)).ncard : ℝ) ≤
          (H.mkQ '' (φ '' (X : Set ℂ))).ncard := by exact_mod_cast hcount
      have hmul := mul_le_mul_of_nonneg_left hcount' (Nat.cast_nonneg (α := ℝ) (U + 1))
      rw [pow_zero, mul_one] at hbound
      exact hmul.trans (hbound.trans (mul_le_mul_of_nonneg_left hpow hC))
  · rintro (hcount | hcount)
    · refine ⟨LinearMap.ker A, 1, 2, Or.inl ⟨rfl, le_rfl⟩, le_rfl, ?_⟩
      rw [← hcardA] at hcount
      simpa only [pow_one] using hcount
    · refine ⟨LinearMap.ker E, 0, 2, Or.inr ⟨rfl, le_rfl⟩, le_rfl, ?_⟩
      rw [← hcardE] at hcount
      simpa only [pow_zero, mul_one] using hcount
