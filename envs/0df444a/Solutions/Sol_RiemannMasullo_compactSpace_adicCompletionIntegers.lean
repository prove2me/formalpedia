-- Prove2me | solution 1 for RiemannMasullo.compactSpace_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:45:47.806278+00:00
-- url     : https://prove2.me/submissions/3ebae9e1-e8e5-4d1a-b5fa-12103e31e162

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L77-L84
import Mathlib
import Definitions.Def_RiemannMasullo_AdicCompletionNorm

open scoped RiemannMasullo.AdicCompletionNorm
open Valued.integer

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private theorem finite_residueField_adicCompletion (v : HeightOneSpectrum R) :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  let O := v.adicCompletionIntegers K
  let f := (residue O).comp (algebraMap R O)
  let q : R ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).2
    change Valued.v (algebraMap R (v.adicCompletion K) r) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    exact (v.valuation_lt_one_iff_mem r).2 hr)
  have := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  apply Finite.of_surjective q
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  -- Approximate the representative first by an element of `K`, then by one of `R`.
  let ν : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion K)) < 1} ∈ 𝓝 (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap K).mem_nhds hn
  change ν (algebraMap K (v.adicCompletion K) a - x) < 1 at ha
  have ha' : v.valuation K a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap K (v.adicCompletion K) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap R (v.adicCompletion K) r - algebraMap K (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub]
    change Valued.v (((algebraMap R K) r - a : K) : v.adicCompletion K) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap R O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap R (v.adicCompletion K) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

theorem solution (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers K) := by
  have : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers K) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
      finite_residueField_adicCompletion v⟩

