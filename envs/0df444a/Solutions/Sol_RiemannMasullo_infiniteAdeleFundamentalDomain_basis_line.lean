-- Prove2me | solution 1 for RiemannMasullo.infiniteAdeleFundamentalDomain_basis_line
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:30:51.98203+00:00
-- url     : https://prove2.me/submissions/67bbb0ee-8258-4044-8e94-70dd96d326c6

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L48-L51
import Mathlib
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution (i : ι) (t : ℝ) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • mixedEmbedding F (b i : F)) ∈
      infiniteAdeleFundamentalDomain F b ↔ t ∈ Set.Ico 0 1 := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _) ∈ ZSpan.fundamentalDomain B ↔ _
  rw [RingEquiv.apply_symm_apply]
  have hi : B i = mixedEmbedding F (b i : F) := by
    rw [show B i = ((b.map e) i : mixedEmbedding.mixedSpace F) from
      Module.Basis.ofZLatticeBasis_apply ..]
    rfl
  rw [← hi, ZSpan.mem_fundamentalDomain]
  constructor
  · intro h
    simpa using h i
  · intro ht k
    by_cases h : i = k
    · subst k; simpa using ht
    · simp [Module.Basis.repr_self, Finsupp.single_apply, h, Ne.symm h]
