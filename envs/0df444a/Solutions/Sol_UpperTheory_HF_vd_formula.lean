-- Prove2me | solution 1 for UpperTheory.HF.vd_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:49.613906+00:00
-- url     : https://prove2.me/submissions/0651a54b-c650-42b4-ad9c-3f342e6e3f20

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogPrimeIndep
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Theorems.Thm_Formalism_HC_Der_Rd_log_rd_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_HF_log_prime_indep
import Theorems.Thm_UpperTheory_HF_log_rd_sum
import Theorems.Thm_UpperTheory_HF_rho_art
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem regroup {N : ℕ} (hN : N ≠ 0) (f : ℕ → ℝ) :
    ∑ m ∈ N.divisors, ArithmeticFunction.vonMangoldt m * f (N / m) =
      ∑ l ∈ N.primeFactors, (∑ j ∈ Finset.range (N.factorization l), f (ordCompl[l] N * l ^ j)) * Real.log l := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', ← Finset.sum_filter_add_sum_filter_not N.divisors IsPrimePow,
    Finset.sum_eq_zero (s := N.divisors.filter fun m => ¬ IsPrimePow m) (fun m hm => by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (Finset.mem_filter.1 hm).2, zero_mul]), add_zero]
  symm
  refine Finset.sum_bij (fun x _ => x.1 ^ (N.factorization x.1 - x.2)) ?_ ?_ ?_ ?_
  · rintro ⟨l, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨?_, hN⟩, ?_⟩
    · exact (pow_dvd_pow l (Nat.sub_le _ _)).trans (Nat.ordProj_dvd N l)
    · exact hx.1.1.isPrimePow.pow (by dsimp only; omega)
  · rintro ⟨l, j⟩ hx ⟨l', j'⟩ hy h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx hy
    dsimp only at h
    have h1 : l = l' := by
      refine (Nat.prime_dvd_prime_iff_eq hx.1.1 hy.1.1).1 (hx.1.1.dvd_of_dvd_pow (n := N.factorization l' - j') ?_)
      rw [← h]; exact dvd_pow_self l (by omega)
    subst h1
    have h2 := Nat.pow_right_injective hx.1.1.two_le h
    obtain rfl : j = j' := by omega
    rfl
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 hm2
    have hd := Nat.dvd_of_mem_divisors hm1
    have hle : k ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN).1 hd
    refine ⟨⟨p, N.factorization p - k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors]
      exact ⟨⟨hp, (dvd_pow_self p hk.ne').trans hd, hN⟩, by omega⟩
    · dsimp only
      congr 1; omega
  · rintro ⟨l, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx
    dsimp only
    have hl := hx.1.1
    have h4 : N / l ^ (N.factorization l - j) = ordCompl[l] N * l ^ j := by
      refine Nat.div_eq_of_eq_mul_right (pow_pos hl.pos _) ?_
      rw [mul_comm (ordCompl[l] N), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hx.2.le]
      exact (Nat.ordProj_mul_ordCompl_eq_self N l).symm
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hl, h4, mul_comm]
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l = ∑ j ∈ Finset.range (H.condN.factorization l), (1 - 1 / (Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) : ℝ)) := by
  intro φ H l hl
  have hN : H.condN ≠ 0 := NeZero.ne _
  obtain ⟨-, h2, h3, -⟩ := UpperTheory.HF.log_rd_sum H
  by_cases hlN : l ∈ H.condN.primeFactors
  · have h4 := Formalism.HC.Der.Rd.log_rd_eq H.toHostRaw
    rw [Formalism.HC.Der.Rd.SS, regroup hN (Formalism.HC.Der.Rd.rho H.art.ker), h2] at h4
    let a : ℕ → ℚ := fun p => (padicValNat p (NumberField.discr H.E).natAbs : ℚ) / (Module.finrank ℚ H.E : ℚ)
    let b : ℕ → ℚ := fun p => ∑ j ∈ Finset.range (H.condN.factorization p),
      (1 - 1 / (Nat.card (H.imgOne (ordCompl[p] H.condN * p ^ j)) : ℚ))
    have ha : ∀ p, (a p : ℝ) = H.vdH p := fun p => by
      simp only [a, HostRaw.vdH]; push_cast; rfl
    have hb : ∀ p, (b p : ℝ) = ∑ j ∈ Finset.range (H.condN.factorization p),
        (1 - 1 / (Nat.card (H.imgOne (ordCompl[p] H.condN * p ^ j)) : ℝ)) := fun p => by
      simp only [b]; push_cast; rfl
    have h5 := UpperTheory.HF.log_prime_indep H.condN.primeFactors a b (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (by
        simp_rw [ha, hb]
        rw [h4]
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        refine UpperTheory.HF.rho_art H.toHostRaw ?_
        conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self H.condN p, mul_comm]
        exact mul_dvd_mul_left _ (pow_dvd_pow p (Finset.mem_range.1 hj).le)) l hlN
    rw [← ha, ← hb, h5]
  · have h6 : H.condN.factorization l = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hlN
    have h7 : ¬ l ∣ (NumberField.discr H.E).natAbs := fun hd =>
      hlN (h3 (Nat.mem_primeFactors.2 ⟨hl, hd, Int.natAbs_ne_zero.2 (discr_ne_zero H.E)⟩))
    rw [h6, Finset.sum_range_zero, HostRaw.vdH, padicValNat.eq_zero_of_not_dvd h7, Nat.cast_zero, zero_div]
end UpperTheory.HF
