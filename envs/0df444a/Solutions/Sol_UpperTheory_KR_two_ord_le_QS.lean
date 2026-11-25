-- Prove2me | solution 1 for UpperTheory.KR.two_ord_le_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:32.229725+00:00
-- url     : https://prove2.me/submissions/6b2b25b1-3d9a-4b76-9d8f-1aa722080754

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeQS
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_art_surj
import Theorems.Thm_Formalism_HC_Der_two_dvd_QS
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_natCard_GG
import Theorems.Thm_Formalism_HC_HostRaw_QS_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QS_q
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QSd_q
import Theorems.Thm_Formalism_HC_HostRaw_d_not_dvd_QSq
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_QS
import Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_imgOne
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_inertG
import Theorems.Thm_UpperTheory_HF_inert_d
import Theorems.Thm_UpperTheory_HF_inert_q
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
open UpperTheory.HF
open Formalism.HC
open scoped Pointwise
private theorem ordCompl_eq_self_of_not_dvd {n p : ℕ} (h : ¬p ∣ n) : ordCompl[p] n = n := by
  simp [Nat.factorization_eq_zero_of_not_dvd h]
private theorem ordCompl_q' {φ : Frame} (H : HostRaw φ) : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have h1 : ¬H.q ∣ H.QS := (Nat.Prime.coprime_iff_not_dvd hq).1 H.coprime_QS_q.symm
  have h2 : ¬H.q ∣ H.d := (Nat.Prime.coprime_iff_not_dvd hq).1
    (Nat.Coprime.coprime_dvd_left (dvd_mul_left H.d H.QS) H.coprime_QSd_q).symm
  have h3 : ordCompl[H.q] H.q = 1 := by
    simpa using Nat.ordCompl_self_pow (k := 1) hq
  simp only [HostRaw.condN, Nat.ordCompl_mul, h3, ordCompl_eq_self_of_not_dvd h1, ordCompl_eq_self_of_not_dvd h2, mul_one]
private theorem ordCompl_d' {φ : Frame} (H : HostRaw φ) : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hd := H.d_prime
  have h3 : ordCompl[H.d] H.d = 1 := by
    simpa using Nat.ordCompl_self_pow (k := 1) hd
  simp only [HostRaw.condN]
  rw [Nat.ordCompl_mul, h3, mul_one, ordCompl_eq_self_of_not_dvd H.d_not_dvd_QSq]
private theorem crt_unit {φ : Frame} (H : HostRaw φ) {a b : ℕ} (hab : a.Coprime b) (hN : H.condN = a * b)
    (u : (ZMod H.condN)ˣ) : ∃ v : (ZMod H.condN)ˣ, (v : ZMod H.condN).val ≡ 1 [MOD a] ∧
      (v : ZMod H.condN).val ≡ (u : ZMod H.condN).val [MOD b] := by
  obtain ⟨x, hxa, hxb⟩ := Nat.chineseRemainder hab 1 (u : ZMod H.condN).val
  have hu : Nat.Coprime (u : ZMod H.condN).val H.condN := ZMod.val_coe_unit_coprime u
  have hxa' : Nat.Coprime x a := by
    have := Nat.ModEq.gcd_eq hxa
    rw [Nat.Coprime, this]
    simp
  have hxb' : Nat.Coprime x b := by
    have := Nat.ModEq.gcd_eq hxb
    rw [Nat.Coprime, this]
    exact Nat.Coprime.coprime_dvd_right (hN ▸ dvd_mul_left b a) hu
  have hx : Nat.Coprime x H.condN := by
    rw [hN]
    exact Nat.Coprime.mul_right hxa' hxb'
  refine ⟨ZMod.unitOfCoprime x hx, ?_, ?_⟩
  · exact ((H.val_unitOfCoprime hx).of_dvd (hN ▸ dvd_mul_right a b)).trans hxa
  · exact ((H.val_unitOfCoprime hx).of_dvd (hN ▸ dvd_mul_left b a)).trans hxb
private theorem img_sub {φ : Frame} (H : HostRaw φ) :
    (H.imgOne H.QS : Set φ.GG) ⊆ (H.inertG H.q : Set φ.GG) * (H.inertG H.d : Set φ.GG) := by
  intro g hg
  rw [SetLike.mem_coe, HostRaw.mem_imgOne H H.QS_dvd_condN] at hg
  obtain ⟨u, hu1, rfl⟩ := hg
  have hN : H.condN = H.QS * H.d * H.q := by simp only [HostRaw.condN]; ring
  obtain ⟨v, hv1, hv2⟩ := crt_unit H H.coprime_QSd_q hN u
  set w : (ZMod H.condN)ˣ := v⁻¹ * u with hw
  have hvw : ((v : ZMod H.condN) * (w : ZMod H.condN)) = (u : ZMod H.condN) := by
    rw [← Units.val_mul, hw, mul_inv_cancel_left]
  have hmod : (u : ZMod H.condN).val ≡ (v : ZMod H.condN).val * (w : ZMod H.condN).val [MOD H.condN] := by
    rw [← hvw, ZMod.val_mul]
    exact Nat.mod_modEq _ _
  have hQSN : H.QS ∣ H.condN := H.QS_dvd_condN
  have hqN : H.q ∣ H.condN := by rw [hN]; exact dvd_mul_left _ _
  have hwQS : (w : ZMod H.condN).val ≡ 1 [MOD H.QS] := by
    have e1 := hmod.of_dvd hQSN
    have e2 : (v : ZMod H.condN).val ≡ 1 [MOD H.QS] := hv1.of_dvd (dvd_mul_right _ _)
    have e3 : (v : ZMod H.condN).val * (w : ZMod H.condN).val ≡ 1 * (w : ZMod H.condN).val [MOD H.QS] :=
      e2.mul_right _
    rw [one_mul] at e3
    exact e3.symm.trans (e1.symm.trans hu1)
  have hwq : (w : ZMod H.condN).val ≡ 1 [MOD H.q] := by
    have e1 := hmod.of_dvd hqN
    have hcop : Nat.Coprime H.q (v : ZMod H.condN).val :=
      (Nat.Coprime.coprime_dvd_right hqN (ZMod.val_coe_unit_coprime v)).symm
    apply Nat.ModEq.cancel_left_of_coprime hcop
    rw [mul_one]
    exact e1.symm.trans hv2.symm
  have hw1 : (w : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QS_q).1 ⟨hwQS, hwq⟩
  refine Set.mem_mul.2 ⟨H.art v, ?_, H.art w, ?_, ?_⟩
  · rw [SetLike.mem_coe, HostRaw.mem_inertG]
    refine ⟨v, ?_, rfl⟩
    rw [ordCompl_q' H]
    exact hv1
  · rw [SetLike.mem_coe, HostRaw.mem_inertG]
    refine ⟨w, ?_, rfl⟩
    rw [ordCompl_d' H]
    exact hw1
  · rw [← map_mul, hw, mul_inv_cancel_left]
private theorem two_totient_le {n : ℕ} (h : 2 ∣ n) : 2 * Nat.totient n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl⟩ := h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    by_cases h2 : 2 ∣ m
    · rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2]
      have := ih m (by omega) h2
      omega
    · rw [Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two h2]
      have := Nat.totient_le m
      omega
end

set_option autoImplicit false
open UpperTheory.HF
open Formalism.HC
open scoped Pointwise
namespace UpperTheory.KR
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), φ.ord ≤ Nat.totient H.QS ∧ 2 * φ.ord ≤ H.QS ∧ 4 * φ.ord ^ 2 * H.q * H.d ≤ (H.QS * H.q * H.d) ^ 2 := by
  intro φ H
  set R := H.toHostRaw with hR
  have hsurj : Function.Surjective R.art := Der.art_surj R
  have hQS0 : R.QS ≠ 0 := R.QS_ne_zero
  haveI : NeZero R.QS := ⟨hQS0⟩
  have hcard : Nat.card φ.GG = 4 * φ.ord := φ.natCard_GG
  have h1 : φ.ord ≤ Nat.totient R.QS := by
    rcases Nat.eq_zero_or_pos φ.ord with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    haveI : Finite φ.GG := Nat.finite_of_card_ne_zero (by omega)
    set I := HostRaw.imgOne R R.QS with hI
    have hidx : I.index ≤ Nat.totient R.QS := by
      have hdvd : I.index ∣ (HostRaw.unitsOne R R.QS).index :=
        Subgroup.index_map_dvd (HostRaw.unitsOne R R.QS) hsurj
      have key : ∀ n : ℕ, n = R.QS → Nat.card (ZMod n)ˣ ≤ Nat.totient R.QS := by
        rintro n rfl
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      have hg : R.QS.gcd R.condN = R.QS := Nat.gcd_eq_left R.QS_dvd_condN
      have hK : (HostRaw.unitsOne R R.QS).index ≤ Nat.totient R.QS := by
        simp only [HostRaw.unitsOne]
        rw [Subgroup.index_ker]
        exact (Subgroup.card_le_card_group _).trans (key _ hg)
      have hpos' : 0 < (HostRaw.unitsOne R R.QS).index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd hpos' hdvd).trans hK
    have hI4 : Nat.card I ≤ 4 := by
      have hsub := img_sub R
      have hm : Nat.card ((I : Set φ.GG)) ≤ Nat.card ((HostRaw.inertG R R.q : Set φ.GG) * (HostRaw.inertG R R.d : Set φ.GG)) :=
        Nat.card_mono (Set.toFinite _) hsub
      have hmul := Set.natCard_mul_le (s := (HostRaw.inertG R R.q : Set φ.GG)) (t := (HostRaw.inertG R R.d : Set φ.GG))
      have hq2 : Nat.card (HostRaw.inertG R R.q) ≤ 2 := (inert_q H).1
      have hd2 : Nat.card (HostRaw.inertG R R.d) = 2 := (inert_d H).2.1
      have e1 : Nat.card I = Nat.card ((I : Set φ.GG)) := rfl
      have e2 : Nat.card (HostRaw.inertG R R.q) = Nat.card ((HostRaw.inertG R R.q : Set φ.GG)) := rfl
      have e3 : Nat.card (HostRaw.inertG R R.d) = Nat.card ((HostRaw.inertG R R.d : Set φ.GG)) := rfl
      rw [e1]
      rw [← e2, ← e3, hd2] at hmul
      nlinarith
    have hci := Subgroup.card_mul_index I
    rw [hcard] at hci
    have : 4 * φ.ord ≤ 4 * Nat.totient R.QS := by
      rw [← hci]
      exact Nat.mul_le_mul hI4 hidx
    omega
  have h2 : 2 * φ.ord ≤ R.QS :=
    (Nat.mul_le_mul_left 2 h1).trans (two_totient_le R.two_dvd_QS)
  refine ⟨h1, h2, ?_⟩
  have hqd : R.q * R.d ≤ (R.q * R.d) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : (2 * φ.ord) ^ 2 ≤ R.QS ^ 2 := Nat.pow_le_pow_left h2 2
  calc 4 * φ.ord ^ 2 * H.q * H.d = (2 * φ.ord) ^ 2 * (R.q * R.d) := by rw [hR]; ring
    _ ≤ R.QS ^ 2 * (R.q * R.d) ^ 2 := Nat.mul_le_mul hsq hqd
    _ = (H.QS * H.q * H.d) ^ 2 := by rw [hR]; ring
end UpperTheory.KR
