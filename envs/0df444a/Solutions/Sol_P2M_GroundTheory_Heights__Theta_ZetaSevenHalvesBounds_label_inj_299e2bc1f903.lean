-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_label_inj_299e2bc1f903
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:59.77083+00:00
-- url     : https://prove2.me/submissions/9f72306e-f18f-4ef1-b082-619dbe348bf8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_label_injective_897833744e40

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
theorem _root_.solution {P Q : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) (e : ratPrime K P = ratPrime K Q) (h : label K P = label K Q) : P = Q := by
  unfold label at h
  rw [dif_pos ⟨hP, hP0⟩, dif_pos ⟨hQ, hQ0⟩] at h
  exact prime_label_injective _ _ e _ _ h
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
