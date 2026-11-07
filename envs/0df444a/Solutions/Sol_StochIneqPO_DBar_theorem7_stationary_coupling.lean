-- Prove2me | solution 1 for StochIneqPO.DBar.theorem7_stationary_coupling
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:46:49.948196+00:00
-- url     : https://prove2.me/submissions/e0d2eb03-976e-415a-8a5e-e895ca29519e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant
import Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae

open MeasureTheory StochIneqPO.DBar Topology Filter BoundedContinuousFunction

theorem solution
    {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P Q : Measure (ℤ → E))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPQ : StochIneqPO.Comparison.StochLE P Q) :
    ∃ ν : Measure ((ℤ → E) × (ℤ → E)),
      IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
      (∀ᵐ z ∂ν, z.1 ≤ z.2) := by
  have := hP.1; have := hQ.1
  -- Step 0: a monotone coupling (Theorem 1, (i) ⇒ (ii))
  obtain ⟨lam, hlam, hlamH, hl1, hl2⟩ :=
    ((StochIneqPO.Comparison.theorem1_tfae P Q).out 0 1).mp hPQ
  have hθc : Continuous (shift (E := E)) := continuous_pi (fun n => continuous_apply _)
  have hθ := hθc.measurable
  have hTc : Continuous (Prod.map (shift (E := E)) (shift (E := E))) := hθc.prodMap hθc
  have hT := hTc.measurable
  set H : Set ((ℤ → E) × (ℤ → E)) := {z | z.1 ≤ z.2} with hHdef
  have hHc : IsClosed H := isClosed_le continuous_fst continuous_snd
  have hHm : MeasurableSet H := hHc.measurableSet
  have hHinv : Prod.map (shift (E := E)) (shift (E := E)) ⁻¹' Hᶜ ⊆ Hᶜ := by
    intro z hz hzH
    apply hz
    show shift z.1 ≤ shift z.2
    intro n; exact hzH (n + 1)
  -- iterates
  let L : ℕ → Measure ((ℤ → E) × (ℤ → E)) := fun k =>
    (fun μ => μ.map (Prod.map (shift (E := E)) (shift (E := E))))^[k] lam
  have hLsucc : ∀ k, L (k + 1) = (L k).map (Prod.map shift shift) := by
    intro k; exact Function.iterate_succ_apply' _ k lam
  have hLprop : ∀ k, IsProbabilityMeasure (L k) ∧ (L k).map Prod.fst = P ∧
      (L k).map Prod.snd = Q ∧ L k Hᶜ = 0 := by
    intro k
    induction k with
    | zero => exact ⟨hlam, hl1, hl2, hlamH⟩
    | succ k ih =>
      obtain ⟨h0, h1, h2, h3⟩ := ih
      rw [hLsucc]
      refine ⟨Measure.isProbabilityMeasure_map hT.aemeasurable, ?_, ?_, ?_⟩
      · rw [Measure.map_map measurable_fst hT]
        have : (Prod.fst ∘ Prod.map (shift (E := E)) (shift (E := E))) = shift ∘ Prod.fst := rfl
        rw [this, ← Measure.map_map hθ measurable_fst, h1, hP.2]
      · rw [Measure.map_map measurable_snd hT]
        have : (Prod.snd ∘ Prod.map (shift (E := E)) (shift (E := E))) = shift ∘ Prod.snd := rfl
        rw [this, ← Measure.map_map hθ measurable_snd, h2, hQ.2]
      · rw [Measure.map_apply hT hHm.compl]
        exact measure_mono_null hHinv h3
  -- Cesàro averages
  let M : ℕ → Measure ((ℤ → E) × (ℤ → E)) := fun n =>
    ((n : ENNReal) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), L k
  have hMapply : ∀ n (s : Set ((ℤ → E) × (ℤ → E))),
      M n s = ((n : ENNReal) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), L k s := by
    intro n s
    simp only [M, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  have hconst : ∀ n (c : ENNReal) (s : Set ((ℤ → E) × (ℤ → E))), (∀ k, L k s = c) →
      M n s = c := by
    intro n c s hc
    rw [hMapply]
    simp only [hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← mul_assoc, Nat.cast_add, Nat.cast_one, ENNReal.inv_mul_cancel (by simp) (by simp),
      one_mul]
  have hMprob : ∀ n, IsProbabilityMeasure (M n) := by
    intro n
    constructor
    exact hconst n 1 Set.univ (fun k => (hLprop k).1.measure_univ)
  have hMfst : ∀ n, (M n).map Prod.fst = P := by
    intro n; ext s hs
    rw [Measure.map_apply measurable_fst hs]
    refine hconst n _ _ (fun k => ?_)
    rw [← Measure.map_apply measurable_fst hs, (hLprop k).2.1]
  have hMsnd : ∀ n, (M n).map Prod.snd = Q := by
    intro n; ext s hs
    rw [Measure.map_apply measurable_snd hs]
    refine hconst n _ _ (fun k => ?_)
    rw [← Measure.map_apply measurable_snd hs, (hLprop k).2.2.1]
  have hMH : ∀ n, M n Hᶜ = 0 := fun n => hconst n 0 _ (fun k => (hLprop k).2.2.2)
  -- integrals against bounded continuous functions
  have hint : ∀ (f : ((ℤ → E) × (ℤ → E)) →ᵇ ℝ) n,
      ∫ x, f x ∂(M n) = ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), ∫ x, f x ∂(L k) := by
    intro f n
    have := fun k => (hLprop k).1
    simp only [M]
    rw [integral_smul_measure, integral_finset_sum_measure]
    · simp only [ENNReal.toReal_inv, smul_eq_mul]
      congr 2
    · intro k _; exact f.integrable _
  have hintT : ∀ (f : ((ℤ → E) × (ℤ → E)) →ᵇ ℝ) (μ : Measure ((ℤ → E) × (ℤ → E))),
      ∫ x, f x ∂(μ.map (Prod.map shift shift)) = ∫ x, f (Prod.map shift shift x) ∂μ := by
    intro f μ
    exact integral_map hT.aemeasurable f.continuous.aestronglyMeasurable
  have hintTM : ∀ (f : ((ℤ → E) × (ℤ → E)) →ᵇ ℝ) n,
      ∫ x, f x ∂((M n).map (Prod.map shift shift)) =
        ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), ∫ x, f x ∂(L (k + 1)) := by
    intro f n
    rw [hintT]
    have := hint (f.compContinuous ⟨_, hTc⟩) n
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at this
    rw [this]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hLsucc, hintT]
  have hdiff : ∀ (f : ((ℤ → E) × (ℤ → E)) →ᵇ ℝ),
      Tendsto (fun n => ∫ x, f x ∂((M n).map (Prod.map shift shift)) - ∫ x, f x ∂(M n))
        atTop (𝓝 0) := by
    intro f
    have heq : ∀ n, ∫ x, f x ∂((M n).map (Prod.map shift shift)) - ∫ x, f x ∂(M n) =
        ((n : ℝ) + 1)⁻¹ * (∫ x, f x ∂(L (n + 1)) - ∫ x, f x ∂(L 0)) := by
      intro n
      rw [hintTM, hint, ← mul_sub, ← Finset.sum_sub_distrib,
        Finset.sum_range_sub (fun k => ∫ x, f x ∂(L k))]
    simp_rw [heq]
    have hb : ∀ n, |∫ x, f x ∂(L (n + 1)) - ∫ x, f x ∂(L 0)| ≤ 2 * ‖f‖ := by
      intro n
      have := (hLprop (n+1)).1; have := (hLprop 0).1
      have a1 : ‖∫ x, f x ∂(L (n + 1))‖ ≤ ‖f‖ := by
        simpa using norm_integral_le_of_norm_le_const (μ := L (n+1))
          (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
      have a2 : ‖∫ x, f x ∂(L 0)‖ ≤ ‖f‖ := by
        simpa using norm_integral_le_of_norm_le_const (μ := L 0)
          (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
      rw [Real.norm_eq_abs] at a1 a2
      have := abs_sub (∫ x, f x ∂(L (n + 1))) (∫ x, f x ∂(L 0))
      linarith
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.congr (fun n => by simp)
    refine squeeze_zero_norm (fun n => ?_) (hinv.mul_const (2 * ‖f‖) |>.trans (by simp))
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb n) (by positivity)
  -- compactness
  let ν : ℕ → ProbabilityMeasure ((ℤ → E) × (ℤ → E)) := fun n => ⟨M n, hMprob n⟩
  let T : ProbabilityMeasure ((ℤ → E) × (ℤ → E)) → ProbabilityMeasure ((ℤ → E) × (ℤ → E)) :=
    fun μ => μ.map hTc.measurable.aemeasurable
  have hTcont : Continuous T := ProbabilityMeasure.continuous_map hTc
  have htight : IsTightMeasureSet
      {x | ∃ μ ∈ Set.range ν, (μ : Measure ((ℤ → E) × (ℤ → E))) = x} := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := P)).subset
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact hMfst n
    · apply (isTightMeasureSet_singleton (μ := Q)).subset
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact hMsnd n
  have hK := isCompact_closure_of_isTightMeasureSet htight
  let U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨νs, -, hνs⟩ := hK.ultrafilter_le_nhds (U.map ν) (by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff]
    show ∀ᶠ n in (U : Filter ℕ), ν n ∈ closure (Set.range ν)
    exact Filter.Eventually.of_forall (fun n => subset_closure ⟨n, rfl⟩))
  have hlim : Tendsto ν U (𝓝 νs) := by rwa [Ultrafilter.coe_map] at hνs
  have hfst : (νs : Measure ((ℤ → E) × (ℤ → E))).map Prod.fst = P := by
    have h1 := ((ProbabilityMeasure.continuous_map continuous_fst).tendsto νs).comp hlim
    have h2 : (fun μ : ProbabilityMeasure ((ℤ → E) × (ℤ → E)) =>
        μ.map continuous_fst.measurable.aemeasurable) ∘ ν =
        fun _ => (⟨P, inferInstance⟩ : ProbabilityMeasure (ℤ → E)) := by
      funext n; apply ProbabilityMeasure.toMeasure_injective; exact hMfst n
    rw [h2] at h1
    have := tendsto_nhds_unique tendsto_const_nhds h1
    exact (congrArg (fun m : ProbabilityMeasure (ℤ → E) => (m : Measure (ℤ → E))) this).symm
  have hsnd : (νs : Measure ((ℤ → E) × (ℤ → E))).map Prod.snd = Q := by
    have h1 := ((ProbabilityMeasure.continuous_map continuous_snd).tendsto νs).comp hlim
    have h2 : (fun μ : ProbabilityMeasure ((ℤ → E) × (ℤ → E)) =>
        μ.map continuous_snd.measurable.aemeasurable) ∘ ν =
        fun _ => (⟨Q, inferInstance⟩ : ProbabilityMeasure (ℤ → E)) := by
      funext n; apply ProbabilityMeasure.toMeasure_injective; exact hMsnd n
    rw [h2] at h1
    have := tendsto_nhds_unique tendsto_const_nhds h1
    exact (congrArg (fun m : ProbabilityMeasure (ℤ → E) => (m : Measure (ℤ → E))) this).symm
  have hH1 : (νs : Measure ((ℤ → E) × (ℤ → E))) H = 1 := by
    have := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hHc
    have hc : (fun n => ((ν n : Measure ((ℤ → E) × (ℤ → E))) H)) = fun _ => 1 := by
      funext n
      exact (prob_compl_eq_zero_iff hHm).mp (hMH n)
    rw [hc, Filter.limsup_const] at this
    exact le_antisymm prob_le_one this
  have hHae : ∀ᵐ z ∂(νs : Measure ((ℤ → E) × (ℤ → E))), z.1 ≤ z.2 := by
    rw [ae_iff]; exact (prob_compl_eq_zero_iff hHm).mpr hH1
  have hTlim1 : Tendsto (fun n => T (ν n)) U (𝓝 (T νs)) := (hTcont.tendsto νs).comp hlim
  have hTlim2 : Tendsto (fun n => T (ν n)) U (𝓝 νs) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim ⊢
    intro f
    have h := (hlim f).add ((hdiff f).mono_left hU)
    rw [add_zero] at h
    refine h.congr (fun n => ?_)
    show ∫ x, f x ∂(M n) + (∫ x, f x ∂((M n).map _) - ∫ x, f x ∂(M n)) = _
    rw [ProbabilityMeasure.toMeasure_map]
    show _ = ∫ ω, f ω ∂((M n).map (Prod.map shift shift))
    ring
  have hfix : T νs = νs := tendsto_nhds_unique hTlim1 hTlim2
  refine ⟨νs, ⟨inferInstance, ?_⟩, hfst, hsnd, hHae⟩
  exact congrArg (fun m : ProbabilityMeasure ((ℤ → E) × (ℤ → E)) =>
    (m : Measure ((ℤ → E) × (ℤ → E)))) hfix
