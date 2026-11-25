-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_tuple_injOn_e0a8cda4a4ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:52.414093+00:00
-- url     : https://prove2.me/submissions/09cbb93d-89f4-4942-8a67-66a1644ee0ac

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_factorization_tuple_da2abc16b590

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
theorem _root_.solution : Set.InjOn (tuple K) {I | I ≠ ⊥} := by
  intro I hI J hJ h
  have hc : ∀ P, (normalizedFactors I).count P = (normalizedFactors J).count P := by
    intro P
    by_cases hP : P.IsPrime ∧ P ≠ ⊥
    · have hI' := factorization_tuple I hP.1 hP.2
      have hJ' := factorization_tuple J hP.1 hP.2
      rw [h] at hI'
      have hpos := (absNorm_eq_ratPrime_pow hP.1 hP.2).2
      exact Nat.eq_of_mul_eq_mul_right hpos (hI'.symm.trans hJ')
    · rw [Multiset.count_eq_zero.mpr fun hm => hP (prime_ne_bot_of_mem hm),
        Multiset.count_eq_zero.mpr fun hm => hP (prime_ne_bot_of_mem hm)]
  have hm : normalizedFactors I = normalizedFactors J := Multiset.ext.mpr hc
  rw [← associated_iff_eq.mp (prod_normalizedFactors hI),
    ← associated_iff_eq.mp (prod_normalizedFactors hJ), hm]
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
