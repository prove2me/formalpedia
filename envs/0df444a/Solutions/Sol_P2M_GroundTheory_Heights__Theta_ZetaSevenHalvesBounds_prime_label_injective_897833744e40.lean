-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_label_injective_897833744e40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:06.104524+00:00
-- url     : https://prove2.me/submissions/32e2f9e4-fb74-4762-a5d6-22377ced66db

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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : p = q) {P Q : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))
    (hQ : Q ∈ primesOver (Ideal.span {(q : ℤ)}) (𝓞 K))
    (h : primeLabel K p hp P hP = primeLabel K q hq Q hQ) : P = Q := by
  subst e
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite _ _).to_subtype
  unfold primeLabel at h
  have h1 := Fin.castLE_injective _ h
  have h2 := (Finite.equivFin _).injective h1
  exact congrArg Subtype.val h2
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
