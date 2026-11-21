-- Prove2me | solution 1 for RiemannMasullo.isDiscrete_principalAdeles
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:39:35.69718+00:00
-- url     : https://prove2.me/submissions/ba0919a3-e628-4158-95a8-2141462bb44f

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L298-L340
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
import Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem
import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

local notation "Integral(" F ")" => integralAdelesOutside F ∅

local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
private theorem mem_integralAdeles_iff (a : 𝔸[F]) :
    a ∈ Integral(F) ↔ ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F := by
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true, true_implies]
  rfl

/-- The integral adele model is open in the full ring of adeles. -/
private theorem isOpen_integralAdeles : IsOpen (Integral(F) : Set 𝔸[F]) := by
  have h : (Integral(F) : Set 𝔸[F]) =
      Prod.snd ⁻¹' {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    Set.ext (mem_integralAdeles_iff F)
  rw [h]
  apply IsOpen.preimage continuous_snd
  have hopen := isOpen_restrictedProduct_forall_mem
    (A := fun v : Primes(F) ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Set.univ
    (fun v _ ↦ Valued.isOpen_integer (v.adicCompletion F))
  simp only [Set.mem_univ, forall_const] at hopen
  exact hopen

/-- The archimedean adele ring and the mixed space have the same product topology. -/
private noncomputable def infiniteAdeleMixedHomeomorph : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F := by
  classical
  refine ((Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F ↦ v.IsReal)
    (fun v ↦ v.Completion))).trans ?_
  exact (Homeomorph.piCongrRight fun v ↦
    (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
      ((Homeomorph.piCongrRight fun v ↦ (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) <|
          Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))

/-- Paper: Lemma A.1.2.1, p. 540. The principal adeles are discrete, since the integral
ones project to the integer lattice in the archimedean factor. -/
theorem solution : IsDiscrete (Principal(F) : Set 𝔸[F]) := by
  let e := infiniteAdeleMixedHomeomorph F
  have hL : IsOpen ({0} : Set (mixedEmbedding.integerLattice F)) := isOpen_discrete _
  obtain ⟨U, hU, hzero⟩ := isOpen_induced_iff.mp hL
  have hzero_mem : (0 : mixedEmbedding.mixedSpace F) ∈ U := by
    have hz : (0 : mixedEmbedding.integerLattice F) ∈ ({0} : Set (mixedEmbedding.integerLattice F)) :=
      Set.mem_singleton _
    rw [← hzero] at hz
    exact hz
  apply isDiscrete_iff_discreteTopology.mpr
  change DiscreteTopology (Principal(F))
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  refine isOpen_induced_iff.mpr ⟨(Integral(F) : Set 𝔸[F]) ∩
    (e ∘ Prod.fst) ⁻¹' U, (isOpen_integralAdeles F).inter
      (hU.preimage (e.continuous.comp continuous_fst)), ?_⟩
  ext a
  constructor
  · rintro ⟨ha, hU'⟩
    obtain ⟨x, hx⟩ := a.property
    have hxInt := (diagonal_mem_integralAdelesOutside F ∅ x).mp (hx ▸ ha)
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hxInt
    obtain ⟨r, rfl⟩ := hxInt
    have hr : mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ mixedEmbedding.integerLattice F :=
      ⟨r, rfl⟩
    have he : e (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)) =
        mixedEmbedding F (algebraMap (𝓞 F) F r) :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
    have hm : (⟨_, hr⟩ : mixedEmbedding.integerLattice F) ∈ ({0} : Set _) := by
      rw [← hzero]
      change mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ U
      rw [← he]
      change e (algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)).1 ∈ U
      rw [hx]
      exact hU'
    have hr0 : algebraMap (𝓞 F) F r = 0 :=
      (mixedEmbedding F).injective (by simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp hm))
    exact Set.mem_singleton_iff.mpr (Subtype.ext (by simpa [hr0] using hx.symm))
  · rintro ha
    have ha' := Set.mem_singleton_iff.mp ha
    subst a
    refine ⟨(Integral(F)).zero_mem, ?_⟩
    change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ U
    rwa [map_zero]

