-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCF.classGroup_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:05:16.509268+00:00
-- url     : https://prove2.me/submissions/ae491c16-6c9c-4f57-b30b-33fecb903a49

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCF
variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
theorem _root_.solution {G : Type*} [Monoid G] (f₁ f₂ : ClassGroup R →* G)
    (h : ∀ v : HeightOneSpectrum R, f₁ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      f₂ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) : f₁ = f₂ := by
  have key : ∀ I : Ideal R, ∀ hI : I ∈ nonZeroDivisors (Ideal R), f₁ (ClassGroup.mk0 ⟨I, hI⟩) = f₂ (ClassGroup.mk0 ⟨I, hI⟩) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro hI; exact absurd rfl (nonZeroDivisors.ne_zero hI)
    | h₂ u hu =>
      intro hI
      have : (⟨u, hI⟩ : nonZeroDivisors (Ideal R)) = 1 := by
        apply Subtype.ext
        show u = 1
        rw [Ideal.isUnit_iff] at hu
        rw [Ideal.one_eq_top]; exact hu
      rw [this, map_one, map_one, map_one]
    | h₃ a p ha hp ih =>
      intro hI
      have hp0 : p ≠ 0 := hp.ne_zero
      have hpm : p ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero hp0
      have ham : a ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero ha
      have e : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal R)) = ⟨p, hpm⟩ * ⟨a, ham⟩ := rfl
      have hP := h ⟨p, Ideal.isPrime_of_prime hp, by simpa using hp0⟩
      rw [e, map_mul, map_mul, map_mul, ih ham]
      exact congrArg (· * _) hP
  refine MonoidHom.ext fun c => ?_
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
  exact key I hI

