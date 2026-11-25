-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ideal_eq_of_isHomogeneous_48fc59908dff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:44.756415+00:00
-- url     : https://prove2.me/submissions/1423c4d5-0c2c-48c1-bdc2-ec70b63cf36a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint

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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I J : Ideal (Poly S N)}
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f.IsHomogeneous e → (f ∈ I ↔ f ∈ J)) : I = J := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact J.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mp (hI f hf d)
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact I.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mpr (hJ f hf d)
end GroundTheory.Heights₂.Heights.Kleiman
