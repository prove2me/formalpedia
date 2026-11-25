-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.LargePrimeDivisors.exists_prime_gt_dvd_eval_of_natDegree_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:39.497741+00:00
-- url     : https://prove2.me/submissions/1846cdfa-379c-4c82-b099-59944e090bed

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_LargePrimeDivisors
import Theorems.Thm_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_mul_sub_mul_add_ne_zero
import Theorems.Thm_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_exists_nat_eval_mul_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.LargePrimeDivisors
open scoped Int LT OfNat Polynomial Dvd
namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors
theorem _root_.solution (f : Polynomial ℤ) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ (p : ℤ) ∣ Polynomial.eval m f := by
  by_cases hc : f.eval 0 = 0
  · obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
    refine ⟨p, p, hp, by omega, ?_⟩
    have h1 := Polynomial.sub_dvd_eval_sub (p : ℤ) 0 f
    rw [hc, sub_zero, sub_zero] at h1
    exact h1
  · have hM0 : ((N.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
    have hcM : f.eval 0 * (N.factorial : ℤ) ≠ 0 := mul_ne_zero hc hM0
    obtain ⟨t, ht⟩ := exists_nat_eval_mul_ne_zero _ (mul_sub_mul_add_ne_zero f hf (f.eval 0)) _ hcM
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_C] at ht
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) 0 f
    have hw : f.eval (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) =
        f.eval 0 * (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) := by
      linear_combination hk
    rw [hw] at ht
    have hv0 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 0 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv1 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ -1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hna : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs ≠ 1 := by
      intro h0
      rcases Int.natAbs_eq_iff.mp h0 with h | h
      · exact hv1 (by exact_mod_cast h)
      · exact hv2 (by rw [h]; norm_num)
    have hp : Nat.Prime ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) :=
      Nat.minFac_prime hna
    have hpv : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
        (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) :=
      Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
    refine ⟨_, f.eval 0 * (N.factorial : ℤ) * (t : ℤ), hp, ?_, ?_⟩
    · by_contra hle
      push_neg at hle
      have hpN : ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) ∣ N.factorial :=
        Nat.dvd_factorial hp.pos hle
      have hpN' : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
          (N.factorial : ℤ) * ((t : ℤ) * k) :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpN) _
      have h1 : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣ 1 :=
        (dvd_add_left hpN').mp hpv
      have h2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac ∣ 1 := by
        exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · rw [hw]
      exact Dvd.dvd.mul_left hpv _
end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
