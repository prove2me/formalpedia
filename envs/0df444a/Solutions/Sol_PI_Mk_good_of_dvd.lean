-- Prove2me | solution 1 for PI.Mk.good_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:38.859175+00:00
-- url     : https://prove2.me/submissions/33cd7d0e-d4de-4418-9511-1e362ccbd230

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
import Theorems.Thm_PI_Mk_good_one
import Theorems.Thm_PI_Mk_good_mul
import Theorems.Thm_PI_Mk_good_cyclotomic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution (ℓ : ℕ) (hℓ : ℓ.Prime) (a M : ℕ) (p : ℚ[X]) (hp : p.Monic)
    (hd : p ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) ^ M) : Good ℓ p := by
  suffices H : ∀ n : ℕ, ∀ q : ℚ[X], q.natDegree = n → q.Monic →
      q ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) ^ M → Good ℓ q from H _ p rfl hp hd
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih q hqn hq hqd
  by_cases h1 : q = 1
  · rw [h1]; exact good_one ℓ
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqu : ¬ IsUnit q := fun hu => h1 (hq.eq_one_of_isUnit hu)
  obtain ⟨r, hr, hrq⟩ := WfDvdMonoid.exists_irreducible_factor hqu hq0
  have hrd : r ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) := hr.prime.dvd_of_dvd_pow (hrq.trans hqd)
  rw [← prod_cyclotomic_eq_X_pow_sub_one (pow_pos hℓ.pos a) (R := ℚ)] at hrd
  obtain ⟨d, hdm, hdr⟩ := hr.prime.exists_mem_finset_dvd hrd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 (Nat.dvd_of_mem_divisors hdm)
  have hirr := cyclotomic.irreducible_rat (pow_pos hℓ.pos i)
  obtain ⟨s, rfl⟩ := (hr.dvd_symm hirr hdr).trans hrq
  have hcm : (cyclotomic (ℓ ^ i) ℚ).Monic := cyclotomic.monic _ ℚ
  have hs : s.Monic := hcm.of_mul_monic_left hq
  have hdeg : (cyclotomic (ℓ ^ i) ℚ * s).natDegree =
      (cyclotomic (ℓ ^ i) ℚ).natDegree + s.natDegree := hcm.natDegree_mul hs
  have hpos : 0 < (cyclotomic (ℓ ^ i) ℚ).natDegree := by
    rw [natDegree_cyclotomic]
    exact Nat.totient_pos.2 (pow_pos hℓ.pos i)
  apply good_mul
  · exact good_cyclotomic ℓ hℓ i
  · exact ih s.natDegree (by omega) s rfl hs ((Dvd.intro_left _ rfl).trans hqd)
end PI.Mk
