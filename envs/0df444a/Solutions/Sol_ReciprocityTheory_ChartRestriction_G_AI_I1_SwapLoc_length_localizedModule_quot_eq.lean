-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_localizedModule_quot_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:14.899805+00:00
-- url     : https://prove2.me/submissions/039c19d0-5886-4818-88dc-469db1932248

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
theorem _root_.solution {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (S : Submonoid R) (V : Ideal R) (x : R)
    (hS : ∀ s ∈ S, IsUnit (algebraMap R T s))
    (hsurj : ∀ y : T, ∃ r : R, ∃ s ∈ S, algebraMap R T r = y * algebraMap R T s)
    (hker : ∀ r : R, algebraMap R T r = 0 → ∃ s ∈ S, s * r ∈ V)
    (hV : ∀ v ∈ V, algebraMap R T v = 0) :
    Module.length (Localization S) (LocalizedModule S (R ⧸ (V ⊔ Ideal.span {x}))) =
      Module.length T (T ⧸ Ideal.span {algebraMap R T x}) := by
  classical
  let φ : Localization S →+* T := IsLocalization.lift (M := S) (S := Localization S)
    (fun s : S => hS s.1 s.2)
  have hφ : ∀ r : R, φ (algebraMap R (Localization S) r) = algebraMap R T r :=
    fun r => IsLocalization.lift_eq _ r
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨r, s, hs, h⟩ := hsurj y
    refine ⟨IsLocalization.mk' (Localization S) r ⟨s, hs⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    rw [h, mul_comm]
  letI : Algebra (Localization S) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization S) T := IsScalarTower.of_algebraMap_eq (fun r => (hφ r).symm)
  set I := V ⊔ Ideal.span {x}
  set J : Ideal T := Ideal.span {algebraMap R T x}
  have hI : ∀ a ∈ I, (Algebra.ofId R (T ⧸ J)) a = 0 := by
    intro a ha
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply R T (T ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Submodule.mem_sup.mp ha |>.elim fun v ⟨hv, y, hy, e⟩ => ?_
    rw [← e, map_add, hV v hv, zero_add]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let g : (R ⧸ I) →ₗ[R] T ⧸ J := (Ideal.Quotient.liftₐ I (Algebra.ofId R (T ⧸ J)) hI).toLinearMap
  have hg : ∀ r : R, g (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J (algebraMap R T r) := by
    intro r
    simp [g, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  haveI : IsLocalizedModule S g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · obtain ⟨u, hu⟩ := hS s.1 s.2
      refine (Module.End.isUnit_iff _).2 ⟨fun a b h => ?_, fun m => ⟨(↑u⁻¹ : T) • m, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        have h2 : (↑u⁻¹ : T) • ((s : R) • a) = (↑u⁻¹ : T) • ((s : R) • b) := by rw [h]
        rwa [← algebraMap_smul T (s : R) a, ← algebraMap_smul T (s : R) b, ← hu, smul_smul,
          smul_smul, Units.inv_mul, one_smul, one_smul] at h2
      · simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul T (s : R), ← hu, smul_smul, Units.mul_inv, one_smul]
    · obtain ⟨τ, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨r, s, hs, h⟩ := hsurj τ
      refine ⟨(Ideal.Quotient.mk I r, ⟨s, hs⟩), ?_⟩
      rw [hg, h, Submonoid.smul_def, ← algebraMap_smul T (s : R), Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm]
    · obtain ⟨r₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
      obtain ⟨r₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
      rw [hg, hg, Ideal.Quotient.eq, ← map_sub] at h
      obtain ⟨τ, hτ⟩ := Ideal.mem_span_singleton'.mp h
      obtain ⟨r', s', hs', h'⟩ := hsurj τ
      have h0 : algebraMap R T (s' * (r₁ - r₂) - r' * x) = 0 := by
        rw [map_sub, map_mul, map_mul, ← hτ, h']; ring
      obtain ⟨s'', hs'', hv⟩ := hker _ h0
      refine ⟨⟨s'' * s', mul_mem hs'' hs'⟩, ?_⟩
      rw [Submonoid.smul_def, Submonoid.smul_def]
      show (s'' * s') • Ideal.Quotient.mk I r₁ = (s'' * s') • Ideal.Quotient.mk I r₂
      rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq]
      have : s'' * s' * r₁ - s'' * s' * r₂ = s'' * (s' * (r₁ - r₂) - r' * x) + s'' * r' * x := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hv)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  let e : LocalizedModule S (R ⧸ I) ≃ₗ[Localization S] T ⧸ J :=
    (IsLocalizedModule.iso S g).extendScalarsOfIsLocalization S (Localization S)
  rw [e.length_eq]
  exact Module.length_eq_of_surjective hφs
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
