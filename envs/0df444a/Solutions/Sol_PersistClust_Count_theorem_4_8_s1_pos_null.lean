-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_s1_pos_null
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T13:33:23.106462+00:00
-- url     : https://prove2.me/submissions/6f61ec8c-b07d-44ca-b6a0-598647a032c4

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold

open PersistClust.Count

/-! ## S1 — the sample-positivity null set of the 4.8 probabilistic shell

The accepted core (`PersistClust.Count.theorem_4_8_core`, id 027bdb99) takes the
deterministic positivity hypothesis `hpos : ∀ i : Fin n, 0 < f (pts i)`.  The shell
must show that its failure set `{pts | ∃ i, f (pts i) ≤ 0}` (note: `¬(0 < f (pts i))`
unfolds to `f (pts i) ≤ 0`) is `sampleMeasure`-null.

Only three facts are used: the density normalization `IsDensity μ f` (non-negativity AND
`∫ f dμ = 1` — the latter only to make `sampleLaw μ f` a probability measure, hence
sigma-finite, which `Measure.pi_eval_preimage_null` needs) and measurability of `f`
(in the root it follows from `hLip` via Lipschitz → continuous → measurable, using
`[BorelSpace X]`).  On the level set `{x | f x ≤ 0}` non-negativity forces `f = 0`, so
the density integrand `ENNReal.ofReal ∘ f` vanishes there and each one-coordinate slice
has `sampleLaw μ f {x | f x ≤ 0} = 0`.
`Measure.pi_eval_preimage_null` transports the null slice to the product, and
`measure_iUnion_null_iff` finishes the finite union. -/

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (n : ℕ)
    (hdens : IsDensity μ f) (hf : Measurable f) :
    sampleMeasure μ n f {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} = 0 := by
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens
  have hA : MeasurableSet {x : X | f x ≤ 0} := measurableSet_Iic.preimage hf
  -- each one-coordinate slice is null for the single-sample law
  have h0 : sampleLaw μ f {x : X | f x ≤ 0} = 0 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x ≤ 0} = 0
    have h1 : μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x ≤ 0}
        = ∫⁻ a in {x : X | f x ≤ 0}, ENNReal.ofReal (f a) ∂μ :=
      withDensity_apply _ hA
    have h2 : ∫⁻ a in {x : X | f x ≤ 0}, ENNReal.ofReal (f a) ∂μ = 0 := by
      rw [← lintegral_indicator hA]
      have hpt : ∀ a : X,
          {x : X | f x ≤ 0}.indicator (fun x => ENNReal.ofReal (f x)) a = 0 := by
        intro a
        by_cases ha : a ∈ {x : X | f x ≤ 0}
        · have hfa : f a = 0 := le_antisymm ha (hnonneg a)
          rw [Set.indicator_of_mem ha, hfa, ENNReal.ofReal_zero]
        · exact Set.indicator_of_notMem ha (fun x => ENNReal.ofReal (f x))
      rw [lintegral_congr hpt]
      exact lintegral_zero
    rw [h1, h2]
  -- the single-sample law is a probability measure (density normalization), hence
  -- sigma-finite — this is what `Measure.pi_eval_preimage_null` synthesizes
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  have key : ∀ i : Fin n,
      sampleMeasure μ n f {pts : Fin n → X | f (pts i) ≤ 0} = 0 := fun i =>
    Measure.pi_eval_preimage_null (μ := fun _ : Fin n => sampleLaw μ f) h0
  have hU : {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0}
      = ⋃ i : Fin n, {pts : Fin n → X | f (pts i) ≤ 0} := by
    ext pts
    simp
  rw [hU]
  exact measure_iUnion_null_iff (μ := sampleMeasure μ n f) |>.2 key
