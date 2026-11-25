-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:29.178993+00:00
-- url     : https://prove2.me/submissions/971a57f7-e571-42f7-9a84-9f2166abca8f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {r₁ : Ω → K'} {Q₂ : SubSystem S x Ω} {Q₂' : SubSystem S y K'} {r₂ : Ω → K'}
    (h₂ : RestrictData Q₂ hxy Q₂' r₂) (I : Chart y) {l : List (Ω × Ω)} {z z' : Ω}
    (hz : ∀ p ∈ l, p.2 * z ∈ Q₂.sub (liftChart hxy I))
    (hz' : ∀ p ∈ l, p.2 * z' ∈ Q₂.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l (z + z') = prodRes r₁ r₂ l z + prodRes r₁ r₂ l z' := by
  rw [prodRes, prodRes, prodRes, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [mul_add, h₂.add I _ (hz p hp) _ (hz' p hp), mul_add]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
