-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:02.228046+00:00
-- url     : https://prove2.me/submissions/f41daf95-b3e4-45c5-8b39-f6caffebaee8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AOpRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf37
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] {I : Subgroup G} {t : G} {R : Finset G},
      (∀ r ∈ R, r ∈ I) →
        (∀ i ∈ I, ∃! r : G, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) →
          ∀ {φ : G → ℂ},
            (∀ (g i : G), i ∈ I → φ (g * i) = φ g) →
              ∀ (g i : G), i ∈ I → UpperTheory.Reformulated.B.Qf37.aOp R t φ (g * i) = UpperTheory.Reformulated.B.Qf37.aOp R t φ g := by
  intro G inst I t R hR hU φ hφ g i hi
  have hex : ∀ r ∈ R, ∃ s, s ∈ R ∧ t⁻¹ * (s⁻¹ * (i * r)) * t ∈ I := fun r hr =>
    (hU (i * r) (I.mul_mem hi (hR r hr))).exists
  choose σ hσR hσ using hex
  have hinj : ∀ a (ha : a ∈ R) b (hb : b ∈ R), σ a ha = σ b hb → a = b := by
    intro a ha b hb hab
    have h1 := hσ a ha
    have h2 := hσ b hb
    rw [← hab] at h2
    have h3 := I.mul_mem (I.inv_mem h1) h2
    have h4 : t⁻¹ * (a⁻¹ * b) * t ∈ I := by
      convert h3 using 1
      group
    have h5 : t⁻¹ * (b⁻¹ * b) * t ∈ I := by
      simp
    exact (hU b (hR b hb)).unique ⟨ha, h4⟩ ⟨hb, h5⟩
  unfold UpperTheory.Reformulated.B.Qf37.aOp
  refine Finset.sum_bij σ hσR hinj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσR
      (fun a b ha hb h => hinj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, hab.symm⟩
  · intro a ha
    rw [← hφ (g * σ a ha * t) _ (hσ a ha)]
    congr 1
    group
end UpperTheory.Reformulated.B.Qf37
