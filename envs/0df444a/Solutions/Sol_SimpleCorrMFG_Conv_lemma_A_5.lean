-- Prove2me | solution 1 for SimpleCorrMFG.Conv.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:47:35.747753+00:00
-- url     : https://prove2.me/submissions/d3f45273-86f4-43bc-8e2d-e73f4bff208e

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_RegCondDistrib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

lemma empMeas_apply {Ω' 𝒴 : Type*} [MeasurableSpace 𝒴] {N : ℕ} (Z : Fin N → Ω' → 𝒴)
    (ω : Ω') {A : Set 𝒴} (hA : MeasurableSet A) :
    empiricalMeasure Z ω A = (N : ENNReal)⁻¹ * ∑ j, A.indicator (1 : 𝒴 → ENNReal) (Z j ω) := by
  unfold empiricalMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp [Measure.dirac_apply' _ hA]

lemma empMeas_meas {Ω' 𝒴 : Type*} [MeasurableSpace Ω'] [MeasurableSpace 𝒴] {N : ℕ}
    (Z : Fin N → Ω' → 𝒴) (hZ : ∀ j, Measurable (Z j)) :
    Measurable (empiricalMeasure Z) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  have : (fun ω => empiricalMeasure Z ω A) =
      fun ω => (N : ENNReal)⁻¹ * ∑ j, A.indicator (1 : 𝒴 → ENNReal) (Z j ω) := by
    funext ω; exact empMeas_apply Z ω hA
  rw [this]
  refine Measurable.const_mul (Finset.measurable_sum _ (fun j _ => ?_)) _
  exact (measurable_const.indicator hA).comp (hZ j)

theorem solution {Ω 𝒴 : Type*} [MeasurableSpace Ω] [TopologicalSpace 𝒴] [PolishSpace 𝒴]
    [MeasurableSpace 𝒴] [BorelSpace 𝒴] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}
    (Y : Fin N → Ω → 𝒴) (hY : ∀ i, Measurable (Y i))
    (hexch : ∀ π : Equiv.Perm (Fin N),
      P.map (fun ω i => Y (π i) ω) = P.map (fun ω i => Y i ω))
    (i : Fin N) :
    IsRegCondDistrib P (Y i) (empiricalMeasure Y)
      (MeasurableSpace.comap (empiricalMeasure Y) inferInstance) := by
  have hN0 : (N : ENNReal) ≠ 0 := by
    have : N ≠ 0 := by have := i.pos; omega
    exact_mod_cast this
  have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hμ : Measurable (empiricalMeasure Y) := empMeas_meas Y hY
  refine ⟨fun ω => ⟨?_⟩, fun A hA => ⟨?_, ?_⟩⟩
  · have h := empMeas_apply Y ω (MeasurableSet.univ : MeasurableSet (Set.univ : Set 𝒴))
    rw [h]
    simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hN0 hNt
  · exact (Measure.measurable_coe hA).comp (comap_measurable (empiricalMeasure Y))
  · intro s hs
    obtain ⟨B, hB, rfl⟩ := hs
    have hsm : MeasurableSet (empiricalMeasure Y ⁻¹' B) := hμ hB
    -- exchangeability: all coordinates have the same joint law with the empirical measure
    have hj : ∀ j, P (Y j ⁻¹' A ∩ empiricalMeasure Y ⁻¹' B) =
        P (Y i ⁻¹' A ∩ empiricalMeasure Y ⁻¹' B) := by
      intro j
      let E : (Fin N → 𝒴) → Measure 𝒴 := empiricalMeasure (fun k (x : Fin N → 𝒴) => x k)
      have hE : Measurable E := empMeas_meas _ (fun k => measurable_pi_apply k)
      let S : Set (Fin N → 𝒴) := {x | x i ∈ A} ∩ E ⁻¹' B
      have hS : MeasurableSet S :=
        ((measurable_pi_apply i) hA).inter (hE hB)
      have key := hexch (Equiv.swap i j)
      have h1 := congrArg (fun m => m S) key
      rw [Measure.map_apply (measurable_pi_lambda _ (fun k => hY _)) hS,
        Measure.map_apply (measurable_pi_lambda _ (fun k => hY _)) hS] at h1
      have e1 : (fun ω (k : Fin N) => Y (Equiv.swap i j k) ω) ⁻¹' S =
          Y j ⁻¹' A ∩ empiricalMeasure Y ⁻¹' B := by
        ext ω
        have : E (fun k => Y (Equiv.swap i j k) ω) = empiricalMeasure Y ω := by
          show (N : ENNReal)⁻¹ • ∑ k, Measure.dirac (Y (Equiv.swap i j k) ω) = _
          unfold empiricalMeasure
          rw [Equiv.sum_comp (Equiv.swap i j) (fun k => Measure.dirac (Y k ω))]
        simp [S, this]
      have e2 : (fun ω (k : Fin N) => Y k ω) ⁻¹' S =
          Y i ⁻¹' A ∩ empiricalMeasure Y ⁻¹' B := by
        ext ω
        simp [S, E, empiricalMeasure]
      rw [e1, e2] at h1
      exact h1
    have hcalc : ∫⁻ ω in empiricalMeasure Y ⁻¹' B, empiricalMeasure Y ω A ∂P =
        (N : ENNReal)⁻¹ * ∑ j : Fin N, P (Y j ⁻¹' A ∩ empiricalMeasure Y ⁻¹' B) := by
      have : ∀ ω, empiricalMeasure Y ω A =
          (N : ENNReal)⁻¹ * ∑ j, (Y j ⁻¹' A).indicator (1 : Ω → ENNReal) ω := by
        intro ω
        rw [empMeas_apply Y ω hA]
        rfl
      refine (lintegral_congr this).trans ?_
      have hm : ∀ j : Fin N, Measurable ((Y j ⁻¹' A).indicator (1 : Ω → ENNReal)) :=
        fun j => measurable_one.indicator (hY j hA)
      rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun j _ => hm j)),
        lintegral_finset_sum _ (fun j _ => hm j)]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [lintegral_indicator_one ((hY j) hA), Measure.restrict_apply ((hY j) hA)]
    rw [hcalc, Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNt, one_mul]
