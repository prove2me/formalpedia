-- Prove2me | solution 1 for UpperTheory.Mu.autApprox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:11:30.394298+00:00
-- url     : https://prove2.me/submissions/fda3addb-fe41-45d1-9da7-7938166357e7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_AutApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField KStar.Tree
private theorem UpperTheory.Mu.exists_aut_pow (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) (hM : M ≠ 0)
    (a : ℕ) (ha : a.Coprime M) : ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ t : Ω, t ^ M = 1 → σ t = t ^ a := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hξ' : IsPrimitiveRoot (ξ ^ a) M := hξ.pow_of_coprime a ha
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  have hc : IsConjRoot ℚ (ξ ^ a) ξ := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hξ hpos, ← Polynomial.cyclotomic_eq_minpoly_rat hξ' hpos]
  obtain ⟨σ, hσ⟩ := hc.exists_algEquiv
  refine ⟨σ, fun t ht => ?_⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one ht
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]
private theorem UpperTheory.Mu.dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
end

set_option autoImplicit false
open NumberField KStar.Tree
namespace UpperTheory.Mu
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ), N ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (v : (ZMod N)ˣ) (u : ℤ_[l]ˣ), (l : ℤ_[l]) ^ N.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ (v : ZMod N).val ∧ (l : ℤ_[l]) ^ k ∣ ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro l hl Ω _ _ _ N hN ζ hζ v u huv k
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp : l.Prime := hl.out
  set s := N.factorization l with hs
  set N' := N / l ^ s with hN'
  have hNN : l ^ s * N' = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hcop : Nat.Coprime l N' := Nat.coprime_ordCompl hp hN
  have hcP : Nat.Coprime N' (l ^ (s + k)) := hcop.symm.pow_right _
  have hN'0 : N' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNN
    exact hN hNN.symm
  have hP0 : l ^ (s + k) ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (l ^ (s + k)) := ⟨hP0⟩
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcP (v : ZMod N).val
    (PadicInt.toZModPow (s + k) (u : ℤ_[l])).val
  have hau : ((a : ℕ) : ZMod (l ^ (s + k))) = PadicInt.toZModPow (s + k) (u : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val]
  have hcoP : a.Coprime (l ^ (s + k)) := by
    rw [← ZMod.isUnit_iff_coprime, hau]
    exact (Units.isUnit u).map _
  have hcoN' : a.Coprime N' := by
    have h1 : (v : ZMod N).val.Coprime N' :=
      (ZMod.val_coe_unit_coprime v).coprime_dvd_right (Dvd.intro_left _ hNN)
    unfold Nat.Coprime at h1 ⊢
    rw [ha1.gcd_eq, h1]
  have hdu : (l : ℤ_[l]) ^ (s + k) ∣ (u : ℤ_[l]) - (a : ℤ_[l]) := by
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, hau]
  have has : a ≡ (v : ZMod N).val [MOD l ^ s] := by
    have h1 : (l : ℤ_[l]) ^ s ∣ (a : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) := by
      have h2 := dvd_sub huv ((pow_dvd_pow _ (Nat.le_add_right s k)).trans hdu)
      convert h2 using 1
      ring
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, map_natCast] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  have haN : a ≡ (v : ZMod N).val [MOD N] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul (hcop.pow_left s)).1 ⟨has, ha1⟩
    rwa [hNN] at this
  obtain ⟨σ, hσ⟩ := UpperTheory.Mu.exists_aut_pow Ω (N' * l ^ (s + k)) (mul_ne_zero hN'0 hP0) a
    (Nat.Coprime.mul_right hcoN' hcoP)
  refine ⟨σ, ?_, ?_⟩
  · have h1 : ζ ^ (N' * l ^ (s + k)) = 1 := by
      have : N' * l ^ (s + k) = N * l ^ k := by rw [← hNN]; ring
      rw [this, pow_mul, hζ.pow_eq_one, one_pow]
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hN, hζ.pow_eq_one⟩
    rw [hσ ζ h1, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
    exact haN
  · refine (pow_dvd_pow _ (Nat.le_add_left k s)).trans ?_
    rw [UpperTheory.Mu.dvd_sub_iff, ← hau]
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (s + k))
    haveI (i : ℕ) : HasEnoughRootsOfUnity Ω (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    have h1 := cyclotomicCharacter.spec l (n := s + k) (σ : Ω ≃+* Ω) η hη.pow_eq_one
    have h2 : σ η = η ^ a := hσ η (by rw [mul_comm, pow_mul, hη.pow_eq_one, one_pow])
    have h3 : η ^ (PadicInt.toZModPow (s + k) ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l])).val = η ^ a :=
      h1.symm.trans h2
    have hfin : IsOfFinOrder η := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hP0, hη.pow_eq_one⟩
    rw [hfin.pow_eq_pow_iff_modEq, ← hη.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h3
    exact h3
end UpperTheory.Mu
