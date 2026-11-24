-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:03.952344+00:00
-- url     : https://prove2.me/submissions/ddeae918-a37c-400c-8068-9750875dc810

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    absNorm P = ratPrime K P ^ (absNorm P).factorization (ratPrime K P) ∧
      0 < (absNorm P).factorization (ratPrime K P) := by
  have hp := ratPrime_prime hP hP0
  have : P.LiesOver (Ideal.span {((ratPrime K P : ℕ) : ℤ)}) := Int.liesOver_span_absNorm P
  have h := absNorm_eq_pow_inertiaDeg' P hp
  have hf : (absNorm P).factorization (ratPrime K P) =
      (Ideal.span {((ratPrime K P : ℕ) : ℤ)}).inertiaDeg' P := by
    rw [h, hp.factorization_pow, Finsupp.single_eq_same]
  refine ⟨hf ▸ h, ?_⟩
  rw [hf]
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, pow_zero, absNorm_eq_one_iff] at h
  exact hP.ne_top h
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
