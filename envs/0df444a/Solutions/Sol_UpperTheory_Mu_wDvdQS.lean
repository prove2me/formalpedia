-- Prove2me | solution 1 for UpperTheory.Mu.wDvdQS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:00.79563+00:00
-- url     : https://prove2.me/submissions/26ba44d2-2682-4fb9-a530-c2e7cc7b89fa

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_WDvdQS
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_cop_QSq_d
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_HC_Der_exists_unit_crt
import Theorems.Thm_Formalism_HC_Der_tauN_root
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_exists_primitiveRoot_w
import Theorems.Thm_Formalism_HC_HostRaw_w_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_w_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField Formalism.HC KStar.Tree
private theorem wDvdQS_crt {N A B : ℕ} [NeZero N] (h : N = A * B) (hAB : A.Coprime B) (y : ℕ) (hy : y.Coprime B) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD A] ∧ (u : ZMod N).val ≡ y [MOD B] := by
  subst h
  obtain ⟨u, hu1, hu2⟩ := Formalism.HC.Der.exists_unit_crt hAB 1 y (Nat.coprime_one_left A) hy
  exact ⟨u, hu1, hu2⟩
private theorem wDvdQS_not_dvd {φ : Frame} (H : HostRaw φ) (A p : ℕ) (hp : p.Prime) (h3 : 3 < p)
    (hN : H.condN = A * p) (hA : A.Coprime p)
    (hart : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD A] → H.art u ^ 2 = 1) : ¬ p ∣ H.w := by
  intro hdvd
  haveI : NeZero H.condN := ⟨by rw [hN]; exact mul_ne_zero (fun h0 => by simp [h0] at hA; exact hp.one_lt.ne' hA) hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := H.exists_primitiveRoot_w
  have hζp : IsPrimitiveRoot (ζ ^ (H.w / p)) p := hζ.pow H.w_pos (Nat.div_mul_cancel hdvd).symm
  have hξ : IsPrimitiveRoot (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) p :=
    hζp.map_of_injective (Formalism.HC.Der.emb H).toRingHom.injective
  have hpN : p ∣ H.condN := ⟨A, by rw [hN, mul_comm]⟩
  have hcop : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  obtain ⟨u, hu1, hu2⟩ := wDvdQS_crt hN hA 2 hcop
  have ha : H.art (u ^ 2) = 1 := by rw [map_pow]; exact hart u hu1
  have he := Formalism.HC.Der.emb_art H (u ^ 2) (ζ ^ (H.w / p))
  rw [ha, map_one, AlgEquiv.one_apply, Formalism.HC.Der.tauN_root] at he
  · have hmod : ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD p] := by
      have he' : (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) ^ ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val
          = (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) ^ 1 := by
        rw [pow_one]; exact he.symm
      have := (hξ.isOfFinOrder hp.ne_zero).pow_eq_pow_iff_modEq.mp he'
      rwa [← hξ.eq_orderOf] at this
    have h4 : ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 2 * 2 [MOD p] := by
      rw [Units.val_pow_eq_pow_val, sq, ZMod.val_mul]
      exact ((Nat.mod_modEq _ _).of_dvd hpN).trans (Nat.ModEq.mul hu2 hu2)
    have h41 : 1 ≡ 4 [MOD p] := hmod.symm.trans h4
    have h3 : p ∣ 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp h41
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · exact (hξ.pow_eq_one_iff_dvd _).mpr hpN
end

set_option autoImplicit false
open NumberField Formalism.HC KStar.Tree
namespace UpperTheory.Mu
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostRaw φ), H.q ≠ 3 → H.w ∣ H.QS ∧ ¬ H.q ∣ H.w ∧ ¬ H.d ∣ H.w := by
  intro φ H hq3
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have hq8 := H.hyp.2.2.1
  have hd16 := H.hyp.2.2.2.1
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).2 (by omega)
  have h1 : ¬ H.q ∣ H.w :=
    wDvdQS_not_dvd H (H.QS * H.d) H.q hq (by omega) (by ring)
      (Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right hqd.symm) H.art_q
  have h2 : ¬ H.d ∣ H.w := by
    refine wDvdQS_not_dvd H (H.QS * H.q) H.d hd (by omega) rfl (Der.cop_QSq_d H) fun u hu => ?_
    rcases H.art_d u hu with h | h
    · rw [h, one_pow]
    · rw [h, sq]
      exact Prod.ext (show ((1, -1) : Formalism.FrobeniusOrbits.G0) * (1, -1) = 1 by decide) (mul_one _)
  refine ⟨?_, h1, h2⟩
  have h3 : H.w ∣ H.QS * H.q :=
    ((hd.coprime_iff_not_dvd.2 h2).symm).dvd_of_dvd_mul_right H.w_dvd_condN
  exact ((hq.coprime_iff_not_dvd.2 h1).symm).dvd_of_dvd_mul_right h3
end UpperTheory.Mu
