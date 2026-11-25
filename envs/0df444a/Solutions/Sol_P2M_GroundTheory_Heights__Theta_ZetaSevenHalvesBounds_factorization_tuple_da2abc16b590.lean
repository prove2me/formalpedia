-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_factorization_tuple_da2abc16b590
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:07.4268+00:00
-- url     : https://prove2.me/submissions/901e4c4d-516d-40bf-9ccc-83a16950dd82

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_label_inj_299e2bc1f903
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
open GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
theorem _root_.solution (I : Ideal (𝓞 K)) {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (tuple K I (label K P)).factorization (ratPrime K P) =
      (normalizedFactors I).count P * (absNorm P).factorization (ratPrime K P) := by
  classical
  unfold tuple
  rw [Nat.factorization_prod]
  swap
  · intro Q hQ
    split_ifs
    · refine pow_ne_zero _ ?_
      rw [Ne, absNorm_eq_zero_iff]
      exact (prime_ne_bot_of_mem (Multiset.mem_toFinset.mp hQ)).2
    · exact one_ne_zero
  rw [Finsupp.finset_sum_apply]
  have key : ∀ Q ∈ (normalizedFactors I).toFinset, Q ≠ P →
      (if label K Q = label K P then absNorm Q ^ (normalizedFactors I).count Q else 1).factorization
        (ratPrime K P) = 0 := by
    intro Q hQ hQP
    obtain ⟨hQp, hQ0⟩ := prime_ne_bot_of_mem (Multiset.mem_toFinset.mp hQ)
    split_ifs with hl
    · have hne : ratPrime K Q ≠ ratPrime K P := fun e => hQP (label_inj hQp hQ0 hP hP0 e hl)
      rw [Nat.factorization_pow, (absNorm_eq_ratPrime_pow hQp hQ0).1,
        (ratPrime_prime hQp hQ0).factorization_pow]
      simp [Finsupp.single_apply, hne]
    · simp
  rw [Finset.sum_eq_single P key]
  · rw [if_pos rfl, Nat.factorization_pow]
    simp
  · intro hPn
    rw [Multiset.mem_toFinset] at hPn
    rw [Multiset.count_eq_zero.mpr hPn]
    simp
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
