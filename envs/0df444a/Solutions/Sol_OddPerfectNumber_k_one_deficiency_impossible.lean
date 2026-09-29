-- Prove2me | solution 1 for OddPerfectNumber.k_one_deficiency_impossible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:08:10.726851+00:00
-- url     : https://prove2.me/submissions/505a92db-8d15-4fc1-bafd-1bc0b082e0a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_exact_valuation_one
import Theorems.Thm_OddPerfectNumber_k_one_unique_p_source
import Theorems.Thm_OddPerfectNumber_k_one_source_absurd

open OddPerfectNumber

-- STAGED, NOT YET SUBMITTED (awaits publish job 46e74ad8 for the residual).
-- Second-level reduction: the packaged obstruction is discharged through two
-- PROVED lemmas plus the open research residual.
theorem solution (p m d : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hm2 : 2 ≤ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) : False := by
  have hval : padicValNat p (∑ x ∈ (m ^ 2).divisors, x) = 1 :=
    k_one_exact_valuation_one p m d hp hpm hdvd hsig
  obtain ⟨q, ⟨hqmem, hqdvd⟩, huniq⟩ :=
    k_one_unique_p_source p m d hp hsig hval
  have huniq' : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q :=
    fun y hym hyd => huniq y ⟨hym, hyd⟩
  exact k_one_source_absurd p m d q hp hp4 hpm hm_odd hm2 hdvd hsig
    hqmem hqdvd huniq'
