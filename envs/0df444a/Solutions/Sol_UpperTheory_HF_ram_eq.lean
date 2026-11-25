-- Prove2me | solution 1 for UpperTheory.HF.ram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:17.39332+00:00
-- url     : https://prove2.me/submissions/d8e66052-b691-49e5-9bf9-cb7d95e3bb8b

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_eq_one
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_Rd_hH_art
import Theorems.Thm_Formalism_HC_Der_Rd_hcl_eq_one
import Theorems.Thm_Formalism_HC_Der_Rd_q_ne_d
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_d_notMem_small
import Theorems.Thm_Formalism_HC_HostRaw_dvd_condN_iff_small
import Theorems.Thm_Formalism_HC_HostRaw_q_ne_d
import Theorems.Thm_Formalism_HC_HostRaw_q_notMem_small
import Theorems.Thm_Formalism_HC_HostRaw_tower_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_two_mem_small
import Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_imgOne_eq_bot_iff
import Theorems.Thm_UpperTheory_HF_condE_spec
import Theorems.Thm_UpperTheory_HF_inert_d
import Theorems.Thm_UpperTheory_HF_inert_q
import Theorems.Thm_UpperTheory_HF_layer_bot
import Theorems.Thm_UpperTheory_HF_log_rd_sum
import Theorems.Thm_UpperTheory_HF_mem_ram
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
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem tower_le {φ : Frame} (H : HostRaw φ) : φ.e + 2 ≤ H.condE.factorization 2 := by
  have h2 := Nat.prime_two
  have hN := H.condN_ne_zero
  have he := H.two_le_e
  have hev : φ.e + 2 ≤ H.condN.factorization 2 :=
    (h2.pow_dvd_iff_le_factorization hN).1 H.tower_dvd_condN
  have hodd : ¬ 2 ∣ H.condN / 2 ^ H.condN.factorization 2 := Nat.not_dvd_ordCompl h2 hN
  have haN : H.condN / 2 ^ H.condN.factorization 2 * 2 ^ H.condN.factorization 2 = H.condN :=
    Nat.div_mul_cancel (Nat.ordProj_dvd _ _)
  by_contra hlt
  push_neg at hlt
  have hbot := ((layer_bot H h2 (j := φ.e + 1) (by omega)).1).2 (by omega)
  generalize ha : H.condN / 2 ^ H.condN.factorization 2 = a at hbot hodd haN
  have hf : a * 2 ^ (φ.e + 1) ∣ H.condN := by
    rw [← haN]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow _ (by omega))
  have hall := (H.imgOne_eq_bot_iff hf).1 hbot
  have hk : 2 ∣ a * 2 ^ (φ.e + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) a
  have hp1 : 1 + a * 2 ^ (φ.e + 1) ≡ 1 [MOD a * 2 ^ (φ.e + 1)] := by
    simp [Nat.ModEq]
  have hcop : Nat.Coprime (1 + a * 2 ^ (φ.e + 1)) H.condN := by
    rw [← haN]
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.pow_right _ ?_)
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq (hp1.of_mul_right _), Nat.gcd_one_left]
    · rw [Nat.coprime_comm, h2.coprime_iff_not_dvd, Nat.dvd_add_left hk]
      norm_num
  set u := ZMod.unitOfCoprime _ hcop
  have hu := H.val_unitOfCoprime hcop
  have h1 := hall u (hu.of_dvd hf |>.trans hp1)
  have hh := Der.Rd.hH_art H u
  rw [h1] at hh
  simp only [Prod.snd_one, map_one] at hh
  have hM : (((u : ZMod H.condN).val : ℕ) : ZMod (2 ^ (φ.e + 2))) = ((1 + a * 2 ^ (φ.e + 1) : ℕ) : ZMod (2 ^ (φ.e + 2))) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (hu.of_dvd H.tower_dvd_condN)
  rw [ZMod.natCast_val] at hM
  rcases Der.Rd.hcl_eq_one hh.symm with hv | hv
  · have := congrArg Units.val hv
    rw [ZMod.unitsMap_val, hM, Units.val_one] at this
    have h' := (ZMod.natCast_eq_natCast_iff _ _ _).1 (this.trans Nat.cast_one.symm)
    have hd := (Nat.modEq_iff_dvd' (by omega)).1 h'.symm
    rw [Nat.add_sub_cancel_left, pow_succ 2 (φ.e + 1), mul_comm a] at hd
    exact hodd (Nat.dvd_of_mul_dvd_mul_left (by positivity) hd)
  · have := congrArg Units.val hv
    rw [ZMod.unitsMap_val, hM, Units.val_neg, Units.val_one, eq_neg_iff_add_eq_zero] at this
    have h0 : ((1 + a * 2 ^ (φ.e + 1) + 1 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast
      push_cast at this
      exact this
    have hd := (ZMod.natCast_eq_zero_iff _ _).1 h0
    have h4M : 4 ∣ 2 ^ (φ.e + 2) := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    have h4X : 4 ∣ a * 2 ^ (φ.e + 1) := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) a
    have h42 := h4M.trans hd
    rw [show 1 + a * 2 ^ (φ.e + 1) + 1 = 2 + a * 2 ^ (φ.e + 1) by ring, Nat.dvd_add_left h4X] at h42
    norm_num at h42
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (∀ l, l ∈ H.ram ↔ l ∈ H.smallR ∨ (l = H.q ∧ H.q ∈ H.ram) ∨ l = H.d) ∧ 2 ∈ H.smallR ∧ H.ram = H.condE.primeFactors ∧ H.condE = H.QSc * (if H.q ∈ H.ram then H.q else 1) * H.d ∧ H.QSc ∣ H.QS ∧ 2 ^ (φ.e + 2) ∣ H.QSc ∧ (∀ l ∈ H.smallR, H.sl l = H.condE.factorization l) ∧ (∀ l ∈ H.ramI, l ∣ H.QS * H.q) := by
  intro φ H
  have hd := H.d_prime
  have hq := H.q_prime
  have hID := inert_d H
  have hIQ := inert_q H
  have hEpos := (condE_spec H.toHostRaw).2.1
  have hEN := (condE_spec H.toHostRaw).1
  have hsub := (log_rd_sum H).2.2.1
  have hprime : ∀ l ∈ H.ram, Nat.Prime l := fun l hl => Nat.prime_of_mem_primeFactors hl
  have hS : ∀ l, l ∈ H.smallR ↔ l ∈ H.small ∧ l ∈ H.ram := fun l => Finset.mem_inter
  have hA : ∀ l, l ∈ H.ram ↔ l ∈ H.smallR ∨ (l = H.q ∧ H.q ∈ H.ram) ∨ l = H.d := by
    intro l
    constructor
    · intro hl
      have hlN := Nat.dvd_of_mem_primeFactors (hsub hl)
      rcases (H.dvd_condN_iff_small (hprime l hl)).1 hlN with h | h | h
      · exact Or.inl ((hS l).2 ⟨h, hl⟩)
      · exact Or.inr (Or.inl ⟨h, h ▸ hl⟩)
      · exact Or.inr (Or.inr h)
    · rintro (h | ⟨rfl, h⟩ | rfl)
      · exact ((hS l).1 h).2
      · exact h
      · exact hID.2.2.2.2.1
  have h2S : 2 ∈ H.smallR := (hS 2).2 ⟨H.two_mem_small, hID.2.2.2.2.2.1⟩
  have hC : H.ram = H.condE.primeFactors := by
    ext l
    rw [Nat.mem_primeFactors]
    constructor
    · intro hl
      exact ⟨hprime l hl, (mem_ram H (hprime l hl)).2.1.1 hl, hEpos.ne'⟩
    · rintro ⟨hp, hdv, -⟩
      exact (mem_ram H hp).2.1.2 hdv
  have hG : ∀ l ∈ H.smallR, H.sl l = H.condE.factorization l := by
    intro l hl
    have hr := ((hS l).1 hl).2
    have hdv := (mem_ram H (hprime l hr)).2.1.1 hr
    have h1 := ((hprime l hr).dvd_iff_one_le_factorization hEpos.ne').1 hdv
    show max 1 (H.condE.factorization l) = H.condE.factorization l
    exact max_eq_right h1
  have hprod : H.condE = ∏ l ∈ H.ram, l ^ H.condE.factorization l := by
    nth_rewrite 1 [← Nat.factorization_prod_pow_eq_self hEpos.ne']
    rw [Finsupp.prod, Nat.support_factorization, hC]
  have hQSc : H.QSc = ∏ l ∈ H.smallR, l ^ H.condE.factorization l := by
    show ∏ l ∈ H.smallR, l ^ H.sl l = _
    exact Finset.prod_congr rfl (fun l hl => by rw [hG l hl])
  have hdS : H.d ∉ H.smallR := fun h => H.d_notMem_small ((hS _).1 h).1
  have hqS : H.q ∉ H.smallR := fun h => H.q_notMem_small ((hS _).1 h).1
  have hD : H.condE = H.QSc * (if H.q ∈ H.ram then H.q else 1) * H.d := by
    by_cases hqr : H.q ∈ H.ram
    · have hset : H.ram = insert H.d (insert H.q H.smallR) := by
        ext l
        rw [hA l, Finset.mem_insert, Finset.mem_insert]
        tauto
      have hdn : H.d ∉ insert H.q H.smallR := by
        rw [Finset.mem_insert]
        exact fun h => h.elim (fun h => H.q_ne_d h.symm) hdS
      rw [if_pos hqr, hprod, hset, Finset.prod_insert hdn, Finset.prod_insert hqS, hQSc,
        hID.2.2.2.2.2.2, (hIQ.2.2.1 hqr).2.2]
      ring
    · have hset : H.ram = insert H.d H.smallR := by
        ext l
        rw [hA l, Finset.mem_insert]
        constructor
        · rintro (h | ⟨rfl, h⟩ | h)
          · exact Or.inr h
          · exact absurd h hqr
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
      rw [if_neg hqr, hprod, hset, Finset.prod_insert hdS, hQSc, hID.2.2.2.2.2.2]
      ring
  have hcopQ : Nat.Coprime H.QSc (H.q * H.d) := by
    show Nat.Coprime (∏ l ∈ H.smallR, l ^ H.sl l) (H.q * H.d)
    refine Nat.Coprime.prod_left (fun l hl => Nat.Coprime.pow_left _ ?_)
    have hr := (hS l).1 hl
    have hl' := hprime l hr.2
    refine Nat.Coprime.mul_right ((Nat.coprime_primes hl' hq).2 ?_) ((Nat.coprime_primes hl' hd).2 ?_)
    · rintro rfl
      exact H.q_notMem_small hr.1
    · rintro rfl
      exact H.d_notMem_small hr.1
  have hQN : H.QSc ∣ H.QS * (H.q * H.d) := by
    have h1 : H.QSc ∣ H.condE := ⟨(if H.q ∈ H.ram then H.q else 1) * H.d, by rw [hD]; ring⟩
    have h2 := h1.trans hEN
    rw [← mul_assoc]
    exact h2
  refine ⟨hA, h2S, hC, hD, hcopQ.dvd_of_dvd_mul_right hQN, ?_, hG, ?_⟩
  · have hle : φ.e + 2 ≤ H.sl 2 := by
      rw [hG 2 h2S]
      exact tower_le H.toHostRaw
    exact (pow_dvd_pow 2 hle).trans (Finset.dvd_prod_of_mem (fun l => l ^ H.sl l) h2S)
  · intro l hl
    have hl2 : l ≠ H.d ∧ l ∈ H.ram := Finset.mem_erase.1 hl
    have hlp := hprime l hl2.2
    have hlN : l ∣ H.QS * H.q * H.d := Nat.dvd_of_mem_primeFactors (hsub hl2.2)
    exact ((Nat.coprime_primes hlp hd).2 hl2.1).dvd_of_dvd_mul_right hlN
end UpperTheory.HF
