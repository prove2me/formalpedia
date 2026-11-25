-- Prove2me | solution 1 for UpperTheory.HF.diff_EK_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:20:18.604026+00:00
-- url     : https://prove2.me/submissions/ab875a02-0815-459a-a108-bc6a24f01cbe

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffMult
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffEKSupp
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_diffSupport
import Theorems.Thm_Formalism_HC_Der_discr_primes
import Theorems.Thm_Formalism_HC_Der_kc_diff_smul_eq
import Theorems.Thm_Formalism_HC_Der_kc_exists_prime
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_d_ne_two
import Theorems.Thm_Formalism_HC_HostRaw_d_not_dvd_QSq
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_dvd_one
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_el_pos
import Theorems.Thm_UpperTheory_HF_diff_mult
import Theorems.Thm_UpperTheory_HF_discr_K
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
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem natMem {M : Type} [Field M] [NumberField M] (l : ℕ) (P : Ideal (𝓞 M))
    [h : P.LiesOver (span {(l : ℤ)})] (n : ℕ) : (n : 𝓞 M) ∈ P ↔ l ∣ n := by
  have h1 : (n : 𝓞 M) = algebraMap ℤ (𝓞 M) (n : ℤ) := by simp
  rw [h1, ← Ideal.mem_comap, ← Ideal.under_def, ← h.over, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
private theorem sq_lemma' {φ : Frame} (H : HostAx φ) (s : 𝓞 H.E) (hs : (s : H.E) = H.sqd) :
    s * s = -(H.d : 𝓞 H.E) := by
  apply RingOfIntegers.coe_injective
  have h2 := H.sqd_sq
  rw [← hs] at h2
  rw [← pow_two]
  push_cast
  exact h2
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (∀ σ : H.E ≃ₐ[ℚ] H.E, σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ (∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) : ℝ) = H.el l * H.vdH l) ∧ 2 ∈ H.ramI := by
  intro φ H
  have hd := H.der
  obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
  have key : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.LiesOver (span {(l : ℤ)})],
      ¬ P ∣ span {s} := by
    intro l hl hld P _ hPs
    rw [Ideal.dvd_span_singleton] at hPs
    have hsq : s * s ∈ P := P.mul_mem_left s hPs
    rw [sq_lemma' H s hs, neg_mem_iff, natMem l P] at hsq
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 hsq)
  have mult : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})],
      multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) = multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
    intro l hl hld P hPp _
    have hP0 : P ≠ ⊥ := by
      intro h0
      have hl' : (l : 𝓞 H.E) ∈ P := (natMem l P l).2 dvd_rfl
      rw [h0, Ideal.mem_bot] at hl'
      exact hl.ne_zero (by exact_mod_cast hl')
    have hpr : Prime P := Ideal.prime_of_isPrime hP0 hPp
    have hz : emultiplicity P (span {s}) = 0 := emultiplicity_eq_zero.2 (key l hl hld P)
    unfold multiplicity
    rw [hdiff, emultiplicity_mul hpr, hz, add_zero]
  refine ⟨fun σ => Formalism.HC.Der.kc_diff_smul_eq H.toHostRaw σ, ?_, ?_, ?_⟩
  · intro P hPp
    constructor
    · intro hPd
      have hmem := hd.diffSupport P hPp hPd
      have hne : H.QS * H.q ≠ 0 := mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
      obtain ⟨l, hl, hlq, hover⟩ := Formalism.HC.Der.kc_exists_prime P _ hne hmem
      refine ⟨l, ?_, hover⟩
      have hld : l ≠ H.d := by
        rintro rfl
        exact H.d_not_dvd_QSq hlq
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase]
      refine ⟨hld, ?_⟩
      rw [(mem_ram H hl).1]
      intro hel
      have h0 : multiplicity P (differentIdeal ℤ (𝓞 H.E)) = 0 := by
        rw [(diff_mult H hl P).2.2.1 (by rw [hel]; exact hl.not_dvd_one), hel]
      have hdv : P ∣ differentIdeal ℤ (𝓞 H.E) := hdiff ▸ dvd_mul_of_dvd_left hPd _
      exact multiplicity_eq_zero.1 h0 hdv
    · rintro ⟨l, hlI, hover⟩
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase] at hlI
      obtain ⟨hld, hlr⟩ := hlI
      have hl : l.Prime := by
        simp only [UpperTheory.HF.Formalism.HC.HostRaw.ram, Nat.mem_primeFactors] at hlr
        exact hlr.1
      have hv : H.vdH l ≠ 0 := ((mem_ram H hl).2.2.1).1 hlr
      have hm := (diff_mult H hl P).1
      have hne : (H.el l : ℝ) * H.vdH l ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (UpperTheory.HF.Formalism.HC.HostRaw.el_pos H.toHostRaw l).ne') hv
      rw [← hm, ← mult l hl hld P] at hne
      by_contra hnd
      exact hne (by exact_mod_cast multiplicity_eq_zero.2 hnd)
  · intro l hl hld P _ _
    rw [mult l hl hld P]
    exact (diff_mult H hl P).1
  · simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase, UpperTheory.HF.Formalism.HC.HostRaw.ram,
      Nat.mem_primeFactors]
    refine ⟨H.d_ne_two.symm, Nat.prime_two, ?_, ?_⟩
    · exact Int.ofNat_dvd_left.1 hd.discr_primes.2.1
    · exact Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)
end UpperTheory.HF
