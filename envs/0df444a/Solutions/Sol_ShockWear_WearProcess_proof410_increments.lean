-- Prove2me | solution 1 for ShockWear.WearProcess.proof410_increments
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:13:21.01699+00:00
-- url     : https://prove2.me/submissions/b9464b24-fdb6-46a9-9b1d-b425e1d0eb40

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace ShockWear.WearProcess

lemma incr_natFilt_le {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ) (hZ : IsWearProcess pr Z κ) (t : ℝ≥0) :
    natFilt Z t ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun r _ => (hZ.meas r).comap_le

lemma incr_meas_natFilt {Ω : Type*} [MeasurableSpace Ω] (Z : ℝ≥0 → Ω → ℝ) (r t : ℝ≥0)
    (hr : r ≤ t) : Measurable[natFilt Z t] (Z r) := by
  intro s hs
  exact le_iSup₂ (f := fun r (_ : r ≤ t) => MeasurableSpace.comap (Z r) inferInstance) r hr _
    ⟨s, hs, rfl⟩

lemma incr_core {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ) (hZ : IsWearProcess pr Z κ) (t Δ : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[natFilt Z t] A) (C : Set ℝ) (hC : MeasurableSet C) :
    pr (A ∩ Z (t + Δ) ⁻¹' C) = ∫⁻ ω in A, κ t Δ (Z t ω) {w | Z t ω + w ∈ C} ∂pr := by
  have hm := incr_natFilt_le pr Z κ hZ t
  have hAm : MeasurableSet A := hm _ hA
  haveI := hZ.kernel_markov t Δ
  set g : Ω → ℝ := (Z (t + Δ) ⁻¹' C).indicator (fun _ => (1 : ℝ)) with hg
  have hCm : MeasurableSet (Z (t+Δ) ⁻¹' C) := hZ.meas _ hC
  have hgi : Integrable g pr := (integrable_const (1:ℝ)).indicator hCm
  set S : Set (ℝ × ℝ) := {p | p.1 + p.2 ∈ C} with hS
  have hSm : MeasurableSet S := (measurable_fst.add measurable_snd) hC
  set f : ℝ × ℝ → ℝ := S.indicator (fun _ => (1:ℝ)) with hf
  have hW : Measurable (fun ω => Z (t + Δ) ω - Z t ω) := (hZ.meas _).sub (hZ.meas _)
  have hfg : (fun ω => f (Z t ω, Z (t + Δ) ω - Z t ω)) = g := by
    funext ω
    classical
    have : Z t ω + (Z (t + Δ) ω - Z t ω) = Z (t + Δ) ω := by ring
    simp only [hf, hg, S, Set.indicator]
    show (if Z t ω + (Z (t + Δ) ω - Z t ω) ∈ C then (1:ℝ) else 0) = if Z (t + Δ) ω ∈ C then 1 else 0
    rw [this]
  have h1 := condExp_prod_ae_eq_integral_condDistrib (μ := pr) (hZ.meas t) hW.aemeasurable
      ((stronglyMeasurable_const.indicator hSm)) (by rw [hfg]; exact hgi)
  rw [hfg] at h1
  have h2 := hZ.incr_law t Δ
  have h2' : ∀ᵐ ω ∂pr, condDistrib (fun ω => Z (t + Δ) ω - Z t ω) (Z t) pr (Z t ω)
      = κ t Δ (Z t ω) :=
    ae_of_ae_map (hZ.meas t).aemeasurable h2
  have h3 : pr[g | MeasurableSpace.comap (Z t) inferInstance] =ᵐ[pr]
      fun ω => (κ t Δ (Z t ω)).real {w | Z t ω + w ∈ C} := by
    filter_upwards [h1, h2'] with ω hω1 hω2
    rw [hω1, hω2]
    have : (fun w => f (Z t ω, w)) = ({w | Z t ω + w ∈ C}).indicator 1 := by
      funext w; simp [hf, S, Set.indicator]
    rw [this]; exact integral_indicator_one ((measurable_const_add (Z t ω)) hC)
  have h4 := hZ.markov t (t + Δ) le_self_add C hC
  have hmeasF : Measurable fun ω => κ t Δ (Z t ω) {w | Z t ω + w ∈ C} :=
    (Kernel.measurable_kernel_prodMk_left (κ := κ t Δ) hSm).comp (hZ.meas t)
  have hfin : ∫⁻ ω in A, κ t Δ (Z t ω) {w | Z t ω + w ∈ C} ∂pr ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top (pr.restrict A) Set.univ) ?_
    rw [← lintegral_one]
    exact lintegral_mono fun ω => prob_le_one
  have E1 : ∫ ω in A, g ω ∂pr = ∫ ω in A, (pr[g | natFilt Z t]) ω ∂pr :=
    (setIntegral_condExp hm hgi hA).symm
  have E2 : ∫ ω in A, (pr[g | natFilt Z t]) ω ∂pr
      = ∫ ω in A, (pr[g | MeasurableSpace.comap (Z t) inferInstance]) ω ∂pr :=
    integral_congr_ae (ae_restrict_of_ae h4)
  have E3 : ∫ ω in A, (pr[g | MeasurableSpace.comap (Z t) inferInstance]) ω ∂pr
      = ∫ ω in A, (κ t Δ (Z t ω)).real {w | Z t ω + w ∈ C} ∂pr :=
    integral_congr_ae (ae_restrict_of_ae h3)
  have E4 : ∫ ω in A, (κ t Δ (Z t ω)).real {w | Z t ω + w ∈ C} ∂pr
      = (∫⁻ ω in A, κ t Δ (Z t ω) {w | Z t ω + w ∈ C} ∂pr).toReal := by
    simp only [measureReal_def]
    exact integral_toReal hmeasF.aemeasurable (ae_of_all _ fun ω => measure_lt_top _ _)
  have E0 : ∫ ω in A, g ω ∂pr = (pr (A ∩ Z (t + Δ) ⁻¹' C)).toReal := by
    have : g = (Z (t + Δ) ⁻¹' C).indicator 1 := rfl
    rw [this, integral_indicator_one hCm, measureReal_restrict_apply hCm, Set.inter_comm,
      measureReal_def]
  rw [E1, E2, E3, E4] at E0
  exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin).1 E0.symm)

lemma incr_step2 {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ) (hZ : IsWearProcess pr Z κ) (t Δ : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[natFilt Z t] A) (B : Set ℝ) (hB : MeasurableSet B) :
    pr (A ∩ (fun ω => Z (t + Δ) ω - Z t ω) ⁻¹' B) = ∫⁻ ω in A, κ t Δ (Z t ω) B ∂pr := by
  have hm := incr_natFilt_le pr Z κ hZ t
  have hAm : MeasurableSet A := hm _ hA
  haveI := hZ.kernel_markov t Δ
  have hY := hZ.meas t
  have hY' := hZ.meas (t + Δ)
  let g : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.1 + p.2)
  have hg : Measurable g := measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hM : (pr.restrict A).map (fun ω => (Z t ω, Z (t + Δ) ω))
      = (((pr.restrict A).map (Z t)) ⊗ₘ (κ t Δ)).map g := by
    refine Measure.ext_prod fun {C1} {C2} hC1 hC2 => ?_
    rw [Measure.map_apply (hY.prodMk hY') (hC1.prod hC2), Measure.map_apply hg (hC1.prod hC2),
      Measure.compProd_apply (hg (hC1.prod hC2)),
      lintegral_map (Kernel.measurable_kernel_prodMk_left (hg (hC1.prod hC2))) hY,
      Measure.restrict_apply ((hY.prodMk hY') (hC1.prod hC2))]
    have hfun : (fun ω => κ t Δ (Z t ω) (Prod.mk (Z t ω) ⁻¹' (g ⁻¹' C1 ×ˢ C2))) =
        (Z t ⁻¹' C1).indicator (fun ω => κ t Δ (Z t ω) {w | Z t ω + w ∈ C2}) := by
      funext ω
      classical
      by_cases h : Z t ω ∈ C1
      · rw [Set.indicator_of_mem (by exact h)]
        congr 1
        ext w; simp [g, h]
      · rw [Set.indicator_of_notMem (by exact h)]
        convert measure_empty (μ := κ t Δ (Z t ω))
        ext w; simp [g, h]
    rw [hfun, lintegral_indicator (hY hC1), Measure.restrict_restrict (hY hC1)]
    have hA' : MeasurableSet[natFilt Z t] (Z t ⁻¹' C1 ∩ A) :=
      ((incr_meas_natFilt Z t t le_rfl) hC1).inter hA
    rw [← incr_core pr Z κ hZ t Δ _ hA' C2 hC2]
    congr 1
    ext ω; simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]; tauto
  have hD : MeasurableSet {p : ℝ × ℝ | p.2 - p.1 ∈ B} := (measurable_snd.sub measurable_fst) hB
  have := congrArg (fun μ => μ {p : ℝ × ℝ | p.2 - p.1 ∈ B}) hM
  rw [Measure.map_apply (hY.prodMk hY') hD, Measure.map_apply hg hD,
    Measure.restrict_apply ((hY.prodMk hY') hD)] at this
  have hpre : g ⁻¹' {p : ℝ × ℝ | p.2 - p.1 ∈ B} = Set.univ ×ˢ B := by
    ext p; simp [g]
  rw [hpre, Measure.compProd_apply_prod MeasurableSet.univ hB, Measure.restrict_univ,
    lintegral_map (Kernel.measurable_coe _ hB) hY] at this
  rw [← this, Set.inter_comm]
  rfl

theorem incr_main {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (Δ : ℝ≥0) :
    ∃ κ' : ℕ → Kernel ℝ ℝ, IsDamageSeq pr (wearIncr Z Δ) κ' := by
  refine ⟨fun k => κ (k • Δ) Δ, ?_⟩
  have hX : ∀ k : ℕ, wearIncr Z Δ k = fun ω => Z (k • Δ + Δ) ω - Z (k • Δ) ω := by
    intro k; funext ω; simp only [wearIncr, succ_nsmul]
  have hXm : ∀ k, Measurable (wearIncr Z Δ k) := by
    intro k; rw [hX]; exact (hZ.meas _).sub (hZ.meas _)
  refine ⟨hXm, ?_, fun k => hZ.kernel_markov _ _, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hZ.start_mono] with ω hω
    rw [hX]
    exact sub_nonneg.2 (hω.2 le_self_add)
  · intro k
    set t : ℝ≥0 := k • Δ with ht
    haveI := hZ.kernel_markov t Δ
    let V : Ω → (Fin k → ℝ) := fun ω i => wearIncr Z Δ i ω
    have hVn : Measurable[natFilt Z t] V := by
      refine @measurable_pi_lambda Ω (Fin k) (fun _ => ℝ) (natFilt Z t) _ V fun i => ?_
      have h1 : (i : ℕ) • Δ + Δ ≤ t := by
        rw [← succ_nsmul, ht]; exact nsmul_le_nsmul_left (zero_le : (0:ℝ≥0) ≤ Δ) (by omega)
      have h2 : (i : ℕ) • Δ ≤ t := le_trans le_self_add h1
      show Measurable[natFilt Z t] (wearIncr Z Δ i)
      rw [hX]
      exact (incr_meas_natFilt Z _ t h1).sub (incr_meas_natFilt Z _ t h2)
    have hm := incr_natFilt_le pr Z κ hZ t
    have hV : Measurable V := hVn.mono hm le_rfl
    have hsum : Measurable (fun v : Fin k → ℝ => ∑ i, v i) := by fun_prop
    let L : Kernel (Fin k → ℝ) ℝ := (κ t Δ).comap (fun v => ∑ i, v i) hsum
    haveI : IsMarkovKernel L := by
      simp only [L]; infer_instance
    have htel : ∀ᵐ ω ∂pr, ∑ i, V ω i = Z t ω := by
      filter_upwards [hZ.start_mono] with ω hω
      simp only [V]
      rw [Fin.sum_univ_eq_sum_range (fun i => wearIncr Z Δ i ω) k]
      unfold wearIncr
      rw [Finset.sum_range_sub (fun i => Z (i • Δ) ω) k]
      simp [hω.1, ht]
    have key : condDistrib (wearIncr Z Δ k) V pr =ᵐ[pr.map V] L := by
      refine condDistrib_ae_eq_of_measure_eq_compProd V (hXm k).aemeasurable ?_
      refine Measure.ext_prod fun {A0} {B} hA0 hB => ?_
      rw [Measure.map_apply (hV.prodMk (hXm k)) (hA0.prod hB),
        Measure.compProd_apply_prod hA0 hB,
        setLIntegral_map hA0 (Kernel.measurable_coe _ hB) hV]
      have e1 : (fun ω => (V ω, wearIncr Z Δ k ω)) ⁻¹' A0 ×ˢ B
          = V ⁻¹' A0 ∩ (fun ω => Z (t + Δ) ω - Z t ω) ⁻¹' B := by
        ext ω; simp [hX k, ht]
      rw [e1, incr_step2 pr Z κ hZ t Δ _ (hVn hA0) B hB]
      refine setLIntegral_congr_fun_ae (hV hA0) ?_
      filter_upwards [htel] with ω hω _
      simp only [L, Kernel.comap_apply, hω]
    refine key.trans (Eventually.of_forall fun v => ?_)
    rfl
  · intro k u z hz z' hz' hzz'
    exact hZ.dec Δ u (k • Δ) (k • Δ) z z' le_rfl hz hzz'
  · intro k u z hz
    exact hZ.dec Δ u (k • Δ) ((k + 1) • Δ) z z
      (nsmul_le_nsmul_left (zero_le : (0:ℝ≥0) ≤ Δ) (by omega)) hz le_rfl

end ShockWear.WearProcess

open ShockWear.WearProcess


theorem solution {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    ∃ κ' : ℕ → Kernel ℝ ℝ, IsDamageSeq pr (wearIncr Z Δ) κ' := by
  exact incr_main pr Z κ hZ Δ
