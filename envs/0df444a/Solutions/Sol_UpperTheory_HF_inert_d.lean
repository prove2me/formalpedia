-- Prove2me | solution 1 for UpperTheory.HF.inert_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:00.743289+00:00
-- url     : https://prove2.me/submissions/e924e87c-4a0d-4d8a-9ab1-52712f092649

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_D7_inertia_d
import Theorems.Thm_Formalism_HC_Der_discr_primes
import Theorems.Thm_Formalism_HC_Der_inertia
import Theorems.Thm_Formalism_HC_Der_inertia_d
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_d_ne_two
import Theorems.Thm_Formalism_HC_HostRaw_d_not_dvd_QSq
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_inertG
import Theorems.Thm_UpperTheory_HF_condE_spec
import Theorems.Thm_UpperTheory_HF_mem_ram
import Theorems.Thm_UpperTheory_HF_vd_tame_wild
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



set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), H.inertG H.d = Subgroup.zpowers φ.iod ∧ H.el H.d = 2 ∧ H.vdH H.d = 1 / 2 ∧ H.sl H.d = 1 ∧ H.d ∈ H.ram ∧ 2 ∈ H.ram ∧ H.condE.factorization H.d = 1 := by
  intro φ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have hd := H.d_prime
  have hQq : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
  have hfac : H.condN.factorization H.d = 1 := by
    show (H.QS * H.q * H.d).factorization H.d = 1
    rw [Nat.factorization_mul hQq hd.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd H.d_not_dvd_QSq, hd.factorization_self]
  have hquot : H.condN / H.d ^ H.condN.factorization H.d = H.QS * H.q := by
    rw [hfac, pow_one]
    exact Nat.mul_div_cancel _ hd.pos
  have hmem : φ.iod ∈ H.inertG H.d := by
    obtain ⟨P, hPm, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H.E)
      (Ideal.span {(H.d : ℤ)})
    have h1 := (H.der.inertia_d P (H.gal.symm φ.iod)).2 (Or.inr (by simp))
    obtain ⟨u, hu, h⟩ := (H.der.inertia H.d P (H.gal.symm φ.iod)).1 h1
    exact (H.mem_inertG H.d _).2 ⟨u, hu, by simpa using h⟩
  have hG : H.inertG H.d = Subgroup.zpowers φ.iod := by
    refine le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.2 hmem)
    obtain ⟨u, hu, rfl⟩ := (H.mem_inertG H.d g).1 hg
    rw [hquot] at hu
    rcases H.art_d u hu with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hord : orderOf φ.iod = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simp [Frame.iod, sq, Prod.ext_iff]) (by simp [Frame.iod, Prod.ext_iff])
  have hel : H.el H.d = 2 := by
    show Nat.card (H.inertG H.d) = 2
    rw [hG, Nat.card_zpowers, hord]
  have hndvd : ¬ H.d ∣ H.el H.d := by
    rw [hel]
    exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).not.2 H.d_ne_two
  have htw := vd_tame_wild H hd
  have hv : H.vdH H.d = 1 / 2 := by
    rw [htw.1 hndvd, hel]
    norm_num
  have hs : H.sl H.d = 1 := htw.2.2 hndvd
  have hram := mem_ram H hd
  have hdram : H.d ∈ H.ram := hram.1.2 (by rw [hel]; norm_num)
  have h2ram : 2 ∈ H.ram := by
    show 2 ∈ (NumberField.discr H.E).natAbs.primeFactors
    refine Nat.mem_primeFactors.2 ⟨Nat.prime_two, ?_, Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)⟩
    exact Int.natAbs_dvd_natAbs.2 (H.der.discr_primes).2.1
  have hpos := (condE_spec H.toHostRaw).2.1
  have hdvd : H.d ∣ H.condE := hram.2.1.1 hdram
  have hle : H.condE.factorization H.d ≤ 1 := by
    have h : max 1 (H.condE.factorization H.d) = 1 := hs
    exact max_eq_left_iff.1 h
  have hge : 1 ≤ H.condE.factorization H.d := (hd.dvd_iff_one_le_factorization hpos.ne').1 hdvd
  exact ⟨hG, hel, hv, hs, hdram, h2ram, le_antisymm hle hge⟩
end UpperTheory.HF
