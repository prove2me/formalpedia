-- Prove2me | solution 1 for UpperTheory.Top.realSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:08.803049+00:00
-- url     : https://prove2.me/submissions/0b8c8529-3341-4372-8318-cd9e863c3678

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_realDecomp
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_realCond
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_IndUnique
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TwistPrim
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_RealSplit
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_QH_ind_unique
import Theorems.Thm_QH_real_cond
import Theorems.Thm_QH_real_decomp
import Theorems.Thm_QH_twist_prim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Formalism.HC UpperTheory.Top
private theorem UpperTheory.Top.realSplit_step (f q i : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f) (hξ : ξ.IsPrimitive)
    (hq : q.Prime) (h2 : q ≠ 2) (hf : ¬ q ∣ f) (hi : i ≤ 1) :
    ∃ (M : ℕ) (ψ : DirichletCharacter ℂ M), M = f * q ^ i ∧ ψ.IsPrimitive ∧
      ∀ n : ℕ, ψ (n : ZMod M) = ξ (n : ZMod f) * QH.J q n ^ i := by
  interval_cases i
  · exact ⟨f, ξ, by simp, hξ, fun n => by simp⟩
  · obtain ⟨ψ, h1, -, h3⟩ := QH.twist_prim f q ξ hξ hq h2 hf
    exact ⟨f * q, ψ, by simp, h1, fun n => by simpa using h3 n⟩
private theorem UpperTheory.Top.realSplit_J (q n i : ℕ) (h : n.Coprime q) : (QH.J q n ^ i) ^ 2 = 1 := by
  have h1 : jacobiSym (n : ℤ) q = 1 ∨ jacobiSym (n : ℤ) q = -1 :=
    jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact h)
  rw [← pow_mul, mul_comm, pow_mul]
  unfold QH.J
  rcases h1 with h1 | h1 <;> simp [h1]
private theorem im_dirichletCharacter_eq_zero_of_coprime (c N₀ : ℕ) [NeZero c] [NeZero N₀] (ρ : DirichletCharacter ℂ c)
    (hc : c ∣ N₀) (h : ∀ n : ℕ, n.Coprime N₀ → (ρ n).im = 0) : ∀ x : ZMod c, (ρ x).im = 0 := by
  intro x
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hc u
    have hn : (v : ZMod N₀).val.Coprime N₀ :=
      (ZMod.isUnit_iff_coprime _ _).1 (by rw [ZMod.natCast_zmod_val]; exact v.isUnit)
    have hux : (u : ZMod c) = ((v : ZMod N₀).val : ZMod c) := by
      rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val]
    rw [hux]
    exact h _ hn
  · rw [MulChar.map_nonunit _ hx]
    simp
private theorem im_mul_intCast_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) (A B : ℤ) : (z * (A : ℂ) * (B : ℂ)).im = 0 := by
  simp [Complex.mul_im, hz]
private theorem exists_real_pchar_twist_decomposition (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχp : χ.IsPrimitive) (S q d : ℕ) (hreal' : ∀ x : ZMod N, (χ x).im = 0) (hS : 0 < S)
    (hq : q.Prime) (hd : d.Prime) (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hcop : Nat.Coprime S (q * d)) (hdvd : N ∣ S * q * d) :
    ∃ (ρ : PChar) (i j : Fin 2), ρ.IsReal ∧ ρ.N ∣ 8 * ordCompl[2] S ∧
      N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) ∧ ∀ a : ℕ, χ a = tw ρ.val q d i j a := by
  have hN₀ : 0 < 8 * ordCompl[2] S := Nat.mul_pos (by norm_num) (Nat.ordCompl_pos 2 hS.ne')
  have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ S → ¬ r ∣ 8 * ordCompl[2] S := by
    intro r hr hr2 hrS h
    rcases (hr.dvd_mul).1 h with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
        (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 3 by norm_num; exact h)))
    · exact hrS (h.trans (Nat.ordCompl_dvd S 2))
  have hqS : ¬ q ∣ S := fun h => (Nat.Prime.coprime_iff_not_dvd hq).1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right q d) hcop).symm h
  have hdS : ¬ d ∣ S := fun h => (Nat.Prime.coprime_iff_not_dvd hd).1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left d q) hcop).symm h
  have hq8 := hnd q hq hq2 hqS
  have hd8 := hnd d hd hd2 hdS
  have hsq : χ ^ 2 = 1 := MulChar.ext fun u => by
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have h1 := DirichletCharacter.unit_norm_eq_one χ u
    have h2 : (starRingEnd ℂ) (χ u) = χ u := Complex.conj_eq_iff_im.2 (hreal' u)
    calc χ u ^ 2 = χ u * (starRingEnd ℂ) (χ u) := by rw [h2, sq]
      _ = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; norm_num
  have hNdvd : N ∣ 8 * ordCompl[2] S * q * d := by
    refine QH.real_cond _ q d N χ hχp hsq (dvd_mul_right 8 _) hq hd fun p hp hpN => ?_
    have h := hpN.trans hdvd
    rcases (hp.dvd_mul).1 h with h | h
    · rcases (hp.dvd_mul).1 h with h | h
      · left
        by_cases hp2 : p = 2
        · subst hp2
          exact Dvd.dvd.mul_right (by norm_num) _
        · refine Dvd.dvd.mul_left ?_ 8
          have hc2 : p.Coprime (2 ^ S.factorization 2) :=
            ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right _
          refine Nat.Coprime.dvd_of_dvd_mul_left hc2 ?_
          rw [Nat.ordProj_mul_ordCompl_eq_self]
          exact h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
  obtain ⟨ξ, a, b, ha, hb, hξ⟩ :=
    QH.real_decomp _ q d N χ hsq hN₀ hq hd hq2 hd2 hqd hq8 hd8 hNdvd
  haveI : NeZero (8 * ordCompl[2] S) := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero (8 * ordCompl[2] S * q * d) :=
    ⟨mul_ne_zero (mul_ne_zero hN₀.ne' hq.ne_zero) hd.ne_zero⟩
  have hprim : ∀ n : ℕ, n.Coprime (8 * ordCompl[2] S) → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have hcN₀ : ξ.conductor ∣ 8 * ordCompl[2] S := ξ.conductor_dvd_level
  have hqc : ¬ q ∣ ξ.conductor := fun h => hq8 (h.trans hcN₀)
  obtain ⟨M1, ψ1, hM1, hψ1, hψ1eq⟩ := UpperTheory.Top.realSplit_step ξ.conductor q a
    ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqc ha
  subst hM1
  haveI : NeZero (ξ.conductor * q ^ a) := ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hq.ne_zero)⟩
  have hdc : ¬ d ∣ ξ.conductor * q ^ a := by
    intro h
    rcases (hd.dvd_mul).1 h with h | h
    · exact hd8 (h.trans hcN₀)
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 (hd.dvd_of_dvd_pow h)).symm
  obtain ⟨M2, ψ2, hM2, hψ2, hψ2eq⟩ :=
    UpperTheory.Top.realSplit_step (ξ.conductor * q ^ a) d b ψ1 hψ1 hd hd2 hdc hb
  subst hM2
  haveI : NeZero (ξ.conductor * q ^ a * d ^ b) :=
    ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hd.ne_zero)⟩
  have hbig : ξ.conductor ∣ 8 * ordCompl[2] S * q * d := hcN₀.trans (Dvd.intro (q * d) (by ring))
  have heq := QH.ind_unique N (ξ.conductor * q ^ a * d ^ b) (8 * ordCompl[2] S * q * d) χ ψ2
    (mul_ne_zero (mul_ne_zero hN₀.ne' hq.ne_zero) hd.ne_zero) hχp hψ2 (fun n hn => by
      rw [hξ n hn, hψ2eq, hψ1eq,
        hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (q * d) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ2 := eq_of_heq hχψ
  subst hc
  have hρreal := im_dirichletCharacter_eq_zero_of_coprime ξ.conductor (8 * ordCompl[2] S * q * d) ξ.primitiveCharacter hbig
    (fun n hn => by
      rw [← hprim _ (Nat.Coprime.coprime_dvd_right (Dvd.intro (q * d) (by ring)) hn)]
      have hJq := UpperTheory.Top.realSplit_J q n a
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) (Nat.Coprime.coprime_dvd_right
          (Dvd.intro d rfl) hn))
      have hJd := UpperTheory.Top.realSplit_J d n b
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hn)
      have hξn : ξ n = χ n * QH.J q n ^ a * QH.J d n ^ b := by
        rw [hξ n hn]
        linear_combination (-(ξ n) * (QH.J d n ^ b) ^ 2) * hJq + (-(ξ n)) * hJd
      have e1 : QH.J q n ^ a = ((jacobiSym n q ^ a : ℤ) : ℂ) := by
        unfold QH.J
        push_cast
        rfl
      have e2 : QH.J d n ^ b = ((jacobiSym n d ^ b : ℤ) : ℂ) := by
        unfold QH.J
        push_cast
        rfl
      rw [hξn, e1, e2]
      exact im_mul_intCast_eq_zero_of_im_eq_zero _ (hreal' n) _ _)
  refine ⟨⟨ξ.conductor, ξ.primitiveCharacter, ξ.primitiveCharacter_isPrimitive⟩, ⟨a, by omega⟩,
    ⟨b, by omega⟩, hρreal, hcN₀, rfl, fun n => ?_⟩
  simp only [PChar.val, tw]
  rw [hψ2eq, hψ1eq]
  rfl
end

set_option autoImplicit false
open Formalism.HC UpperTheory.Top
namespace UpperTheory.Top
theorem _root_.solution :
    ∀ (χ : PChar) (S q d : ℕ), χ.IsReal → 0 < S → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → Nat.Coprime S (q * d) → χ.N ∣ S * q * d →
      ∃ (ρ : PChar) (i j : Fin 2), ρ.IsReal ∧ ρ.N ∣ 8 * ordCompl[2] S ∧ χ.N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) ∧
        ∀ a : ℕ, a.Coprime χ.N → χ.val a = tw ρ.val q d i j a := by
  intro χ0
  cases χ0 with
  | mk N χ hχp =>
    intro S q d hreal hS hq hd hq2 hd2 hqd hcop hdvd
    obtain ⟨ρ, i, j, hρ, hρN, hN, hval⟩ :=
      exists_real_pchar_twist_decomposition N χ hχp S q d hreal hS hq hd hq2 hd2 hqd hcop hdvd
    exact ⟨ρ, i, j, hρ, hρN, hN, fun a _ => hval a⟩
end UpperTheory.Top
