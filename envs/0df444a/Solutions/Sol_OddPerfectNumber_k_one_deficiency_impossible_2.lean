-- Prove2me | solution 2 for OddPerfectNumber.k_one_deficiency_impossible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:35:46.145651+00:00
-- url     : https://prove2.me/submissions/65f22ad9-8883-4068-b600-d61782c2e89b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_exact_valuation_one
import Theorems.Thm_OddPerfectNumber_k_one_unique_p_source
import Theorems.Thm_OddPerfectNumber_k_one_source_absurd

theorem _root_.solution (p m d : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hm2 : 2 ≤ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) : False := by
  have hval := OddPerfectNumber.k_one_exact_valuation_one p m d hp hpm hdvd hsig
  obtain ⟨q, ⟨hqmem, hqdvd⟩, huniq⟩ :=
    OddPerfectNumber.k_one_unique_p_source p m d hp hsig hval
  exact OddPerfectNumber.k_one_source_absurd p m d q hp hp4 hpm hm_odd hm2 hdvd hsig
    hqmem hqdvd (fun y hy hP => huniq y ⟨hy, hP⟩)

#print axioms solution
