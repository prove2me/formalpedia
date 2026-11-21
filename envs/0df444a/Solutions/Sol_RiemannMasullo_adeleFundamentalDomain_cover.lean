-- Prove2me | solution 1 for RiemannMasullo.adeleFundamentalDomain_cover
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:39:48.711034+00:00
-- url     : https://prove2.me/submissions/a1a342cd-061e-47e2-adb0-4c95da5d7913

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L81-L83
import Mathlib
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
import Theorems.Thm_RiemannMasullo_exists_sub_diagonal_mem_integralAdeles
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution :
    (⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) = Set.univ := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  haveI : Finite ι := Module.Finite.finite_basis b
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨x, hx⟩ := exists_sub_diagonal_mem_integralAdeles F a
  let y := a - algebraMap F 𝔸[F] x
  let φ := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (φ y.1)
  have hspan : Submodule.span ℤ (Set.range B) = mixedEmbedding.integerLattice F :=
    Module.Basis.ofZLatticeBasis_span ..
  have hvL : (v : mixedEmbedding.mixedSpace F) ∈ mixedEmbedding.integerLattice F := by
    rw [← hspan]
    exact v.property
  obtain ⟨r, hr⟩ := hvL
  let z := algebraMap (𝓞 F) F r
  have hz : algebraMap F 𝔸[F] z ∈ integralAdelesOutside F ∅ := by
    apply (diagonal_mem_integralAdelesOutside F ∅ z).mpr
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
    exact ⟨r, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨x - z, y + algebraMap F 𝔸[F] z, ⟨?_, (integralAdelesOutside F ∅).add_mem hx hz⟩, ?_⟩
  · change φ (y.1 + algebraMap F (InfiniteAdeleRing F) z) ∈ ZSpan.fundamentalDomain B
    rw [map_add, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, add_comm]
    change (v : mixedEmbedding.mixedSpace F) + φ y.1 ∈ ZSpan.fundamentalDomain B at hv
    rw [← hr] at hv
    exact hv
  · change algebraMap F 𝔸[F] (x - z) + (a - algebraMap F 𝔸[F] x + algebraMap F 𝔸[F] z) = a
    rw [map_sub]; abel
