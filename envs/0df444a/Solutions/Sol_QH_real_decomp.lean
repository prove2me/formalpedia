-- Prove2me | solution 1 for QH.real_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:13.243621+00:00
-- url     : https://prove2.me/submissions/7aab1a69-5798-4800-9671-3120317bb22a

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_realDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
private theorem real_split (M p : ℕ) (h : M.Coprime p) (χ : DirichletCharacter ℂ (M * p))
    (hχ : χ ^ 2 = 1) :
    ∃ (ξ : DirichletCharacter ℂ M) (η : DirichletCharacter ℂ p), ξ ^ 2 = 1 ∧ η ^ 2 = 1 ∧
      ∀ n : ℕ, n.Coprime (M * p) →
        χ (n : ZMod (M * p)) = ξ (n : ZMod M) * η (n : ZMod p) := by
  let E : (ZMod (M * p))ˣ ≃* (ZMod M)ˣ × (ZMod p)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  let φ : (ZMod M)ˣ × (ZMod p)ˣ →* ℂˣ := χ.toUnitHom.comp E.symm.toMonoidHom
  have hφ : ∀ x, ((φ x : ℂˣ) : ℂ) ^ 2 = 1 := by
    intro x
    have h1 : ((φ x : ℂˣ) : ℂ) = χ ((E.symm x : (ZMod (M * p))ˣ) : ZMod (M * p)) := by
      simp [φ]
    rw [h1, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  refine ⟨MulChar.ofUnitHom (φ.comp (MonoidHom.inl _ _)),
    MulChar.ofUnitHom (φ.comp (MonoidHom.inr _ _)), ?_, ?_, ?_⟩
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe]
    exact hφ _
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe]
    exact hφ _
  · intro n hn
    have hM : n.Coprime M := Nat.Coprime.coprime_mul_right_right hn
    have hp : n.Coprime p := Nat.Coprime.coprime_mul_left_right hn
    have hE : E (ZMod.unitOfCoprime n hn) = (ZMod.unitOfCoprime n hM, ZMod.unitOfCoprime n hp) := by
      have hc : (ZMod.chineseRemainder h) (n : ZMod (M * p)) = ((n : ZMod M), (n : ZMod p)) := by
        rw [map_natCast]; rfl
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · exact congrArg Prod.fst hc
      · exact congrArg Prod.snd hc
    rw [← ZMod.coe_unitOfCoprime n hn, ← ZMod.coe_unitOfCoprime n hM,
      ← ZMod.coe_unitOfCoprime n hp, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe,
      ← Units.val_mul, MonoidHom.comp_apply φ, MonoidHom.comp_apply φ, ← map_mul]
    have : (MonoidHom.inl _ _ (ZMod.unitOfCoprime n hM) * MonoidHom.inr _ _ (ZMod.unitOfCoprime n hp)
        : (ZMod M)ˣ × (ZMod p)ˣ) = E (ZMod.unitOfCoprime n hn) := by
      rw [hE]; simp
    rw [this]
    simp [φ]
private theorem real_prime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (η : DirichletCharacter ℂ p)
    (hη : η ^ 2 = 1) :
    ∃ a : ℕ, a ≤ 1 ∧ ∀ n : ℕ, n.Coprime p → η (n : ZMod p) = J p n ^ a := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have key : ∀ θ : MulChar (ZMod p) ℂ, θ ^ 2 = 1 → θ ≠ 1 → θ g = -1 := by
    intro θ h1 hne
    have h3 : θ g ^ 2 = 1 := by rw [← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp (by rw [← sq]; exact h3 : θ g * θ g = 1) with h | h
    · exfalso
      apply hne
      rw [MulChar.eq_iff hg, h, MulChar.one_apply_coe]
    · exact h
  by_cases h1 : η = 1
  · refine ⟨0, by norm_num, fun n hn => ?_⟩
    rw [h1, pow_zero, ← ZMod.coe_unitOfCoprime n hn, MulChar.one_apply_coe]
  · refine ⟨1, le_rfl, fun n _ => ?_⟩
    let ψ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
    have hψ1 : ψ ≠ 1 := by
      refine (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).mpr ?_
      exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact h2)
    have hψ2 : ψ ^ 2 = 1 :=
      ((quadraticChar_isQuadratic (ZMod p)).comp _).sq_eq_one
    have he : η = ψ := by
      rw [MulChar.eq_iff hg, key η hη h1, key ψ hψ2 hψ1]
    rw [he, pow_one, J, ← jacobiSym.legendreSym.to_jacobiSym]
    simp [ψ, legendreSym]
private theorem real_one_step (M p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hM : ¬ p ∣ M)
    (χ : DirichletCharacter ℂ (M * p)) (hχ : χ ^ 2 = 1) :
    ∃ (ξ : DirichletCharacter ℂ M) (a : ℕ), ξ ^ 2 = 1 ∧ a ≤ 1 ∧
      ∀ n : ℕ, n.Coprime (M * p) → χ (n : ZMod (M * p)) = ξ (n : ZMod M) * J p n ^ a := by
  obtain ⟨ξ, η, h1, h3, h4⟩ :=
    real_split M p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hM).symm χ hχ
  obtain ⟨a, ha, h5⟩ := real_prime p hp h2 η h3
  exact ⟨ξ, a, h1, ha, fun n hn => by
    rw [h4 n hn, h5 n (Nat.Coprime.coprime_mul_left_right hn)]⟩
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (N₀ q d : ℕ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → 0 < N₀ → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → ¬ q ∣ N₀ → ¬ d ∣ N₀ →
      N ∣ N₀ * q * d → ∃ (ξ : DirichletCharacter ℂ N₀) (a b : ℕ), a ≤ 1 ∧ b ≤ 1 ∧
        ∀ n : ℕ, n.Coprime (N₀ * q * d) → χ (n : ZMod N) = ξ (n : ZMod N₀) * J q n ^ a * J d n ^ b := by
  intro N₀ q d N _ χ hχ _ hq hd hq2 hd2 hqd hqN hdN hN
  have hdq : ¬ d ∣ N₀ * q := by
    intro h
    rcases (Nat.Prime.dvd_mul hd).mp h with h | h
    · exact hdN h
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).mp h).symm
  have hχ' : (DirichletCharacter.changeLevel hN χ) ^ 2 = 1 := by
    rw [← map_pow, hχ, map_one]
  obtain ⟨ξ₁, b, h1, hb, h3⟩ := real_one_step (N₀ * q) d hd hd2 hdq _ hχ'
  obtain ⟨ξ, a, _, ha, h4⟩ := real_one_step N₀ q hq hq2 hqN ξ₁ h1
  refine ⟨ξ, a, b, ha, hb, fun n hn => ?_⟩
  rw [← h4 n (Nat.Coprime.coprime_mul_right_right hn), ← h3 n hn,
    ← ZMod.coe_unitOfCoprime n hn, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast hN]
end QH
