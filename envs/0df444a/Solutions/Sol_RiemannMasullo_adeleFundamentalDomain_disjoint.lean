-- Prove2me | solution 1 for RiemannMasullo.adeleFundamentalDomain_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:34:20.729186+00:00
-- url     : https://prove2.me/submissions/a3d0a33f-2554-491e-8bc6-d583f18aa0b2

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L75-L77
import Mathlib
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution (x : F) (hx : x ≠ 0) :
    Disjoint (algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) (adeleFundamentalDomain F b) := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  haveI : Finite ι := Module.Finite.finite_basis b
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, ha, rfl⟩ hw
  change algebraMap F 𝔸[F] x + a ∈ adeleFundamentalDomain F b at hw
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hw₁, hw₂⟩ := hw
  have hxint : algebraMap F 𝔸[F] x ∈ integralAdelesOutside F ∅ := by
    simpa using (integralAdelesOutside F ∅).sub_mem hw₂ ha₂
  have hr := (diagonal_mem_integralAdelesOutside F ∅ x).mp hxint
  simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hr
  obtain ⟨r, rfl⟩ := hr
  let φ := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let u := mixedEmbedding F (algebraMap (𝓞 F) F r)
  have hu : u ∈ Submodule.span ℤ (Set.range B) := by
    rw [show Submodule.span ℤ (Set.range B) = mixedEmbedding.integerLattice F from
      Module.Basis.ofZLatticeBasis_span ..]
    exact ⟨r, rfl⟩
  change φ a.1 ∈ ZSpan.fundamentalDomain B at ha₁
  change φ (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r) + a.1) ∈
    ZSpan.fundamentalDomain B at hw₁
  rw [map_add, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at hw₁
  let v : Submodule.span ℤ (Set.range B) := ⟨u, hu⟩
  have h₁ : v +ᵥ φ a.1 ∈ ZSpan.fundamentalDomain B := hw₁
  have h₀ : (0 : Submodule.span ℤ (Set.range B)) +ᵥ φ a.1 ∈ ZSpan.fundamentalDomain B := by
    simpa using ha₁
  have hv : v = 0 := (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (φ a.1)).unique h₁ h₀
  apply hx
  apply mixedEmbedding_injective F
  exact (congrArg Subtype.val hv).trans (map_zero (mixedEmbedding F)).symm
