-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_eq_of_subset_43355d35aad8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:09.538823+00:00
-- url     : https://prove2.me/submissions/270debad-9fe7-49b1-9c83-f87b2be949fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d

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
theorem _root_.solution {Q₁ Q₂ : SubSystem S x Ω} {Q₁' Q₂' : SubSystem S y K'} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁ hxy Q₁' r₁) (h₂ : RestrictData Q₂ hxy Q₂' r₂) {I K : Chart y}
    (hIK : I.1 ⊆ K.1) {l l' : List (Ω × Ω)}
    (hl : ∀ p ∈ l, p.1 ∈ Q₁.sub (liftChart hxy I) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy I), p.2 * a ∈ chartRing S x (liftChart hxy I))
    (hl1 : (l.map fun p => p.1 * p.2).sum = 1)
    (hl' : ∀ p ∈ l', p.1 ∈ Q₁.sub (liftChart hxy K) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy K), p.2 * a ∈ chartRing S x (liftChart hxy K))
    (hl1' : (l'.map fun p => p.1 * p.2).sum = 1) {z : Ω}
    (hz : z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l z = prodRes r₁ r₂ l' z := by
  have H : prodRes r₁ r₂ l z = prodRes r₁ r₂ l' z ∧
      z ∈ Q₂.sub (liftChart hxy K) * Q₁.sub (liftChart hxy K) := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem b hb a ha =>
      have ha' := Q₁.mono (liftChart hxy I) (liftChart hxy K) hIK a ha
      have hb' := Q₂.mono (liftChart hxy I) (liftChart hxy K) hIK b hb
      exact ⟨by rw [prodRes_mul h₁ h₂ I hl hl1 ha hb, prodRes_mul h₁ h₂ K hl' hl1' ha' hb'],
        Submodule.mul_mem_mul hb' ha'⟩
    | add z hz z' hz' h h' =>
      refine ⟨?_, add_mem h.2 h'.2⟩
      rw [prodRes_add h₂ I (fun p hp => mul_mem_of_mem_mul (hl p hp).2 hz)
          (fun p hp => mul_mem_of_mem_mul (hl p hp).2 hz'),
        prodRes_add h₂ K (fun p hp => mul_mem_of_mem_mul (hl' p hp).2 h.2)
          (fun p hp => mul_mem_of_mem_mul (hl' p hp).2 h'.2), h.1, h'.1]
  exact H.1
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
