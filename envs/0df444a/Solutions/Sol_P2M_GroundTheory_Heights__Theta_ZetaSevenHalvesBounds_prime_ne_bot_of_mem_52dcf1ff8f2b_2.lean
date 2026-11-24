-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:59.923325+00:00
-- url     : https://prove2.me/submissions/89e884c6-7202-4c7a-98cf-6bb785e4a0f7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm

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
theorem _root_.solution {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ := by
  have hp := prime_of_normalized_factor P h
  exact ⟨(Ideal.prime_iff_isPrime hp.ne_zero).mp hp, hp.ne_zero⟩
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
