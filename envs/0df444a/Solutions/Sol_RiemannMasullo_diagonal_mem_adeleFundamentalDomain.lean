-- Prove2me | solution 1 for RiemannMasullo.diagonal_mem_adeleFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:31:59.184177+00:00
-- url     : https://prove2.me/submissions/2cbdf215-f8ec-4535-a335-726d7136eafc

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L61-L63
import Mathlib
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution (x : F) :
    algebraMap F 𝔸[F] x ∈ adeleFundamentalDomain F b ↔ x = 0 := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  constructor
  · rintro ⟨hinf, hfin⟩
    have hx := (diagonal_mem_integralAdelesOutside F ∅ x).mp hfin
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)) ∈ ZSpan.fundamentalDomain B at hinf
    rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at hinf
    have hzero : r = 0 := by
      apply b.repr.injective
      ext i
      have h := (ZSpan.mem_fundamentalDomain B).mp hinf i
      change B.repr ((e r : mixedEmbedding.integerLattice F) : mixedEmbedding.mixedSpace F) i ∈ Set.Ico 0 1 at h
      rw [Module.Basis.ofZLatticeBasis_repr_apply, Module.Basis.map_repr] at h
      change (((b.repr (e.symm (e r))) i : ℤ) : ℝ) ∈ Set.Ico 0 1 at h
      rw [LinearEquiv.symm_apply_apply] at h
      obtain ⟨h0,h1⟩ := h
      have h0' : 0 ≤ b.repr r i := by exact_mod_cast h0
      have h1' : b.repr r i < 1 := by exact_mod_cast h1
      simp only [map_zero, Finsupp.zero_apply]
      omega
    simp [hzero]
  · rintro rfl
    rw [map_zero]
    refine ⟨?_, Subring.zero_mem _⟩
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 ∈ ZSpan.fundamentalDomain B
    rw [map_zero, ZSpan.mem_fundamentalDomain]
    intro i
    simp
