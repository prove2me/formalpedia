-- Prove2me | solution 2 for ReciprocityTheory.Neutral.Bridge.HCF.classGroup_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:19.171804+00:00
-- url     : https://prove2.me/submissions/66e7bf8a-d78c-4c33-a89f-180193fdb9b0

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
namespace ReciprocityTheory.Neutral.Bridge.HCF
theorem _root_.solution {G : Type*} [Monoid G] (f₁ f₂ : ClassGroup R →* G)
    (h : ∀ v : HeightOneSpectrum R, f₁ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      f₂ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) : f₁ = f₂ := by
  suffices key : ∀ I : Ideal R, ∀ hI : I ∈ (Ideal R)⁰, f₁ (ClassGroup.mk0 ⟨I, hI⟩) = f₂ (ClassGroup.mk0 ⟨I, hI⟩) by
    ext c
    obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
    exact key I hI
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact absurd hI (zero_notMem_nonZeroDivisors)
  | h₂ u hu =>
    intro hI
    have : (⟨u, hI⟩ : (Ideal R)⁰) = 1 := Subtype.ext (by simpa using hu)
    rw [this, map_one, map_one, map_one]
  | h₃ I p hI' hp ih =>
    intro hI
    have hp0 : p ∈ (Ideal R)⁰ := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
    have hI0 : I ∈ (Ideal R)⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
      rintro rfl; exact hI (mul_zero p)
    have : (⟨p * I, hI⟩ : (Ideal R)⁰) = ⟨p, hp0⟩ * ⟨I, hI0⟩ := rfl
    rw [this, map_mul, map_mul, map_mul, ih hI0]
    congr 1
    have hpp : p.IsPrime := Ideal.isPrime_of_prime hp
    have hpb : p ≠ ⊥ := hp.ne_zero
    exact h ⟨p, hpp, hpb⟩
end ReciprocityTheory.Neutral.Bridge.HCF
