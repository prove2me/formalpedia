-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isLocalizedModule_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:05:10.175411+00:00
-- url     : https://prove2.me/submissions/6eea6bc2-9b34-44b1-8c68-11bcd41e16e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]
variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
variable {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [Module B A] [Module B A'] (hsm : ∀ (b : B) (a : A), b • a = e b * a)
    (hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a) (f : A →ₗ[B] A') (hf : ∀ a, f a = algebraMap A A' a) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B M) f := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨_, ⟨m, hm, rfl⟩⟩ := x
    have hu : IsUnit (algebraMap A A' (e (algebraMap S B m))) := by
      rw [AlgHom.commutes]
      exact IsLocalization.map_units A' (⟨algebraMap S A m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩ :
        Algebra.algebraMapSubmonoid A M)
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hu
    constructor
    · intro a₁ a₂ h
      simp only [Module.algebraMap_end_apply, hsm'] at h
      rw [← hu] at h
      exact u.isUnit.mul_left_cancel h
    · intro a
      refine ⟨((u⁻¹ : A'ˣ) : A') * a, ?_⟩
      simp only [Module.algebraMap_end_apply, hsm', ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨⟨a, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A M) y
    refine ⟨⟨a, ⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩⟩, ?_⟩
    show algebraMap S B m • y = f a
    rw [hsm', hf, AlgHom.commutes, ← h, mul_comm]
  · rw [hf, hf] at hx
    obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, h⟩ := IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hx
    refine ⟨⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩, ?_⟩
    show algebraMap S B m • x₁ = algebraMap S B m • x₂
    rw [hsm, hsm, AlgHom.commutes]
    exact h
end ReciprocityTheory.ChartRestriction.G.Chart
