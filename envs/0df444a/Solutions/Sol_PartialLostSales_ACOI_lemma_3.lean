-- Prove2me | solution 1 for PartialLostSales.ACOI.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:00:38.479687+00:00
-- url     : https://prove2.me/submissions/dd9237e2-b4fd-48fa-bc8e-4c33c35e6838

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model
import Theorems.Thm_ProbabilityMeasureSpace_standardBorelSpace

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE Set
open scoped ENNReal NNReal

open PartialLostSales.ACOI in
theorem solution (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P)) (hM : IsCOMDP P M) :
    (⨅ z, wOpt M z) ≠ ⊤ := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  haveI := hprob
  haveI : StandardBorelSpace (ProbabilityMeasure ℝ≥0) :=
    ProbabilityMeasureSpace.standardBorelSpace
  have hmeas : MeasurableSet
      {z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤} := by
    have h1 : Measurable (fun z : ProbabilityMeasure ℝ≥0 => secondMoment (z : Measure ℝ≥0)) := by
      unfold secondMoment
      exact (Measure.measurable_lintegral (by fun_prop)).comp measurable_subtype_coe
    exact h1 measurableSet_Iio
  haveI : StandardBorelSpace (Bel P) := hmeas.standardBorel
  let a0 : Act P := ⟨0, le_refl 0, hK.le⟩
  let p0 : Bel P × Act P := (δ0 P, a0)
  have hD0 : P.demand (Iio 0) = 0 := hneg
  have hnext : nextLaw P (δ0 P).1 (a0 : ℝ) =
      (P.demand).map (fun s => Real.toNNReal (-s)) := by
    unfold nextLaw
    show ((Measure.dirac (0:ℝ≥0)).prod P.demand).map _ = _
    rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext s
    simp [a0]
  have hR1 : R1 P (δ0 P).1 a0 = 0 := by
    unfold R1
    rw [hnext, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    convert hD0 using 2
    ext s
    simp [Real.toNNReal_pos]
  have hR0 : R0 P (δ0 P).1 a0 = 1 := by
    unfold R0
    rw [hnext, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    have : (fun s : ℝ => Real.toNNReal (-s)) ⁻¹' {0} = (Iio (0:ℝ))ᶜ := by
      ext s
      simp [Real.toNNReal_eq_zero]
    rw [this, prob_compl_eq_one_sub measurableSet_Iio, hD0, tsub_zero]
  have hq : M.q p0 = Measure.dirac (δ0 P) := by
    rw [hM.2.2]
    unfold qBel
    rw [hR0, hR1]
    simp
  let φ : Bel P → Act P := fun _ => a0
  have hφ : Measurable φ := measurable_const
  let π := Policy.ofStationary φ hφ
  have hstep : ∀ t (h : Π _ : Finset.Iic t, Bel P × Act P), lastPair t h = p0 →
      stepKernel M π t h = Measure.dirac p0 := by
    intro t h hh
    ext s hs
    have hm1 : Measurable (lastPair (X := Bel P) (A := Act P) t) := measurable_pi_apply _
    have hm2 : Measurable (fun p : (Π _ : Finset.Iic t, Bel P × Act P) × Bel P =>
        (histFin t p.1, p.2)) :=
      ((measurable_histFin t).comp measurable_fst).prodMk measurable_snd
    haveI : IsMarkovKernel (M.q.comap (lastPair t) hm1) := Kernel.IsMarkovKernel.comap _ _
    haveI : IsMarkovKernel ((π.rule (t + 1)).comap _ hm2) := Kernel.IsMarkovKernel.comap _ _
    have e : stepKernel M π t h s =
        ((M.q.comap (lastPair t) hm1) ⊗ₖ ((π.rule (t + 1)).comap _ hm2)) h s := rfl
    rw [e, Kernel.compProd_apply hs, Kernel.comap_apply, hh, hq,
      lintegral_dirac, Kernel.comap_apply]
    simp only [π, Policy.ofStationary, Kernel.deterministic_apply, φ]
    rw [Measure.dirac_apply' _ (measurable_prodMk_left hs), Measure.dirac_apply' _ hs]
    rfl
  have hinit : initMeasure π (δ0 P) = Measure.dirac p0 := by
    simp only [initMeasure, π, Policy.ofStationary, Kernel.deterministic_apply, φ]
    rw [Measure.map_dirac' (by fun_prop)]
  haveI : IsProbabilityMeasure (initMeasure π (δ0 P)) := by rw [hinit]; infer_instance
  haveI : IsProbabilityMeasure (pathMeasure M π (δ0 P)) := by
    unfold pathMeasure; infer_instance
  have hae : ∀ t, ∀ᵐ ω ∂(pathMeasure M π (δ0 P)), ω t = p0 := by
    intro t
    induction t with
    | zero =>
      have h0 : (pathMeasure M π (δ0 P)).map (fun ω => ω 0) = Measure.dirac p0 := by
        have : (fun ω : ℕ → Bel P × Act P => ω 0) =
            (fun h : (Π _ : Finset.Iic 0, Bel P × Act P) => h ⟨0, by simp⟩) ∘
              Preorder.frestrictLe 0 := rfl
        rw [this, ← Measure.map_map
          (g := fun h : (Π _ : Finset.Iic 0, Bel P × Act P) => h ⟨0, by simp⟩)
          (measurable_pi_apply _) (Preorder.measurable_frestrictLe 0)]
        rw [pathMeasure, Kernel.trajMeasure, Measure.map_comp _ _
          (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
          Kernel.partialTraj_self, Measure.id_comp, hinit, Measure.map_dirac' (by fun_prop),
          Measure.map_dirac' (by fun_prop)]
        rfl
      have : ∀ᵐ x ∂((pathMeasure M π (δ0 P)).map (fun ω => ω 0)), x = p0 := by
        rw [h0]
        exact (ae_dirac_iff (measurableSet_singleton p0)).2 rfl
      exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable this
    | succ t ih =>
      have key := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ => Bel P × Act P)
        (μ₀ := initMeasure π (δ0 P)) (κ := stepKernel M π) (a := t)
      have hset : MeasurableSet
          {q : (Π _ : Finset.Iic t, Bel P × Act P) × (Bel P × Act P) | q.2 ≠ p0} :=
        ((measurableSet_singleton p0).compl).preimage measurable_snd
      rw [ae_iff]
      have e1 : (pathMeasure M π (δ0 P)) {ω | ¬ ω (t + 1) = p0} =
          ((pathMeasure M π (δ0 P)).map
            (fun ω => (Preorder.frestrictLe t ω, ω (t + 1))))
            {q : (Π _ : Finset.Iic t, Bel P × Act P) × (Bel P × Act P) | q.2 ≠ p0} := by
        rw [Measure.map_apply (by fun_prop) hset]
        rfl
      rw [e1, pathMeasure, ← key, Measure.compProd_apply hset]
      have hlast : ∀ᵐ h ∂((pathMeasure M π (δ0 P)).map
          (Preorder.frestrictLe t)), lastPair t h = p0 := by
        refine (ae_map_iff (Preorder.measurable_frestrictLe
          (X := fun _ : ℕ => Bel P × Act P) t).aemeasurable
          (p := fun h : (Π _ : Finset.Iic t, Bel P × Act P) => lastPair t h = p0)
          ((measurableSet_singleton p0).preimage (measurable_pi_apply _))).2 ?_
        exact ih
      calc _ = ∫⁻ _h, (0 : ℝ≥0∞) ∂((pathMeasure M π (δ0 P)).map
            (Preorder.frestrictLe t)) := by
              refine lintegral_congr_ae (hlast.mono fun h hh => ?_)
              simp only
              rw [hstep t h hh, Measure.dirac_apply' _ (measurable_prodMk_left hset)]
              simp
        _ = 0 := lintegral_zero
  have hall : ∀ᵐ ω ∂(pathMeasure M π (δ0 P)), ∀ t, ω t = p0 := ae_all_iff.2 hae
  set c0 := M.cost (δ0 P) a0 with hc0def
  have hv : ∀ N, vN M π N 1 (δ0 P) = N * c0 := by
    intro N
    unfold vN
    rw [lintegral_congr_ae (hall.mono fun ω hω => by
      show (∑ t ∈ Finset.range N, ENNReal.ofReal (1 ^ t) * M.cost (ω t).1 (ω t).2) =
        ∑ t ∈ Finset.range N, c0
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hω t]
      simp [p0, c0])]
    simp [measure_univ]
  have havg : avgCost M π (δ0 P) = c0 := by
    unfold avgCost
    rw [Filter.limsup_congr (f := atTop) (v := fun _ => c0)]
    · exact limsup_const c0
    · filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hv N, ENNReal.inv_mul_cancel_left (by exact_mod_cast (show N ≠ 0 by omega))
        (ENNReal.natCast_ne_top N)]
  have hc0 : c0 ≠ ⊤ := by
    rw [hc0def, hM.2.1]
    unfold cbar
    show ∫⁻ x, c P x a0 ∂(Measure.dirac (0:ℝ≥0)) ≠ ⊤
    rw [lintegral_dirac]
    unfold c
    apply ne_of_lt
    calc _ ≤ ∫⁻ s, ENNReal.ofReal ((P.hplus + P.hminus) * |s|) ∂P.demand := by
          apply lintegral_mono
          intro s
          apply ENNReal.ofReal_le_ofReal
          simp only [a0, NNReal.coe_zero, zero_add, sub_zero, zero_sub]
          have h1 : max (-s) 0 ≤ |s| := max_le (neg_le_abs s) (abs_nonneg s)
          have h2 : max s 0 ≤ |s| := max_le (le_abs_self s) (abs_nonneg s)
          nlinarith [mul_le_mul_of_nonneg_left h1 hhp.le, mul_le_mul_of_nonneg_left h2 hhm.le]
      _ < ⊤ := ((hint.abs).const_mul _).lintegral_lt_top
  refine ne_top_of_le_ne_top hc0 ?_
  calc (⨅ z, wOpt M z) ≤ wOpt M (δ0 P) := iInf_le _ _
    _ ≤ avgCost M π (δ0 P) := iInf_le _ π
    _ = c0 := havg

