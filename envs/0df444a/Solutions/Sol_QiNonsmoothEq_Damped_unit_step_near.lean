-- Prove2me | solution 1 for QiNonsmoothEq.Damped.unit_step_near
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:24:26.199879+00:00
-- url     : https://prove2.me/submissions/c8e02ca9-59f0-4b20-bf03-91e41b668ae5

import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

open Filter Topology

namespace QiNonsmoothEq.Damped
open MeasureTheory Metric

section avg
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma g51_ae_diff_ball (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → E) (a : E) (ρ : ℝ) (K : NNReal)
    (hK : LipschitzOnWith K F (ball a ρ)) :
    ∀ᵐ w ∂μ, w ∈ ball a ρ → DifferentiableAt ℝ F w := by
  filter_upwards [hK.ae_differentiableWithinAt_of_mem (μ := μ)] with w hw hwm
  exact (hw hwm).differentiableAt (isOpen_ball.mem_nhds hwm)

lemma g51_exists_diff (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → E) (a : E) (ρ : ℝ) (K : NNReal)
    (hK : LipschitzOnWith K F (ball a ρ)) (S : Set E) (hS : IsOpen S) (hne : S.Nonempty)
    (hSB : S ⊆ ball a ρ) : ∃ w ∈ S, DifferentiableAt ℝ F w := by
  by_contra hcon
  push_neg at hcon
  have h1 := g51_ae_diff_ball μ F a ρ K hK
  have h2 : μ S = 0 := by
    rw [ae_iff] at h1
    refine measure_mono_null (fun w hw => ?_) h1
    simp only [Set.mem_setOf_eq, _root_.not_imp]
    exact ⟨hSB hw, hcon w hw⟩
  exact (hS.measure_pos μ hne).ne' h2

lemma g51_avg_step (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → E) (hFc : Continuous F) (x h L : E) (K : NNReal) (ρ : ℝ)
    (hK : LipschitzOnWith K F (ball x ρ)) (ε δ : ℝ) (hδ : 0 < δ)
    (hdiff : ∀ w, DifferentiableAt ℝ F w → ∀ t : ℝ, ∀ h' : E, 0 < t → t < δ → ‖h' - h‖ < δ →
       w = x + t • h' → ‖fderiv ℝ F w h' - L‖ ≤ ε)
    (t0 t1 : ℝ) (ht0 : 0 < t0) (ht01 : t0 < t1) (ht1δ : t1 < δ)
    (ht1ρ : 2 * t1 * (‖h‖ + δ) < ρ) :
    ‖F (x + t1 • h) - F (x + t0 • h) - (t1 - t0) • L‖ ≤
      (ε + K * (δ / 2)) * (t1 - t0) + K * (t0 * δ) := by
  set r : ℝ := t0 * δ / 2 with hr
  have hrpos : 0 < r := by positivity
  set B : Set E := ball (0 : E) r with hB
  set ν : Measure E := μ.restrict B with hν
  haveI : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hmpos : 0 < ν.real Set.univ := by
    rw [hν, measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos (measure_ball_pos μ _ hrpos).ne' measure_ball_lt_top.ne
  set m : ℝ := ν.real Set.univ with hm
  -- points stay inside the ball
  have hpts : ∀ z ∈ B, ∀ s : ℝ, 0 ≤ s → s ≤ 3 * t1 / 2 → x + z + s • h ∈ ball x ρ := by
    intro z hz s hs0 hs1
    have hz' : ‖z‖ < r := by simpa [hB] using hz
    rw [mem_ball_iff_norm]
    have : x + z + s • h - x = z + s • h := by abel
    rw [this]
    calc ‖z + s • h‖ ≤ ‖z‖ + ‖s • h‖ := norm_add_le _ _
      _ ≤ r + s * ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg hs0]; linarith
      _ < ρ := by
        have h1 : r ≤ t1 * δ / 2 := by rw [hr]; nlinarith
        have h2 : s * ‖h‖ ≤ 3 * t1 / 2 * ‖h‖ := by gcongr
        nlinarith [norm_nonneg h]
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hcont : ∀ s : ℝ, Continuous (fun z : E => F (x + z + s • h)) := fun s =>
    hFc.comp (by fun_prop)
  have hint : ∀ s : ℝ, Integrable (fun z : E => F (x + z + s • h)) ν := fun s =>
    ((hcont s).continuousOn.integrableOn_compact (isCompact_closedBall (0:E) r)).mono_set
      ball_subset_closedBall
  have hae : ∀ s0 : ℝ, 0 ≤ s0 → s0 ≤ 3 * t1 / 2 →
      ∀ᵐ z ∂ν, DifferentiableAt ℝ F (x + z + s0 • h) := by
    intro s0 hs0pos hs0le
    have h1 := g51_ae_diff_ball μ F x ρ K hK
    have h2 : ∀ᵐ z ∂μ, x + z + s0 • h ∈ ball x ρ → DifferentiableAt ℝ F (x + z + s0 • h) := by
      have := (quasiMeasurePreserving_add_right μ (x + s0 • h)).ae h1
      filter_upwards [this] with z hz
      simpa [add_assoc, add_comm, add_left_comm] using hz
    have h3 := ae_restrict_of_ae (s := B) h2
    filter_upwards [h3, ae_restrict_mem (μ := μ) (measurableSet_ball (x := (0:E)) (ε := r))]
      with z hz hzB
    exact hz (hpts z hzB s0 hs0pos hs0le)
  set Φ : ℝ → E := fun s => ∫ z, F (x + z + s • h) ∂ν with hΦ
  have hderiv : ∀ s0 ∈ Set.Icc t0 t1, HasDerivAt Φ (∫ z, fderiv ℝ F (x + z + s0 • h) h ∂ν) s0 ∧
      Integrable (fun z => fderiv ℝ F (x + z + s0 • h) h) ν := by
    intro s0 hs0
    have hs0pos : 0 < s0 := lt_of_lt_of_le ht0 hs0.1
    have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := ν) (s := ball s0 (t0 / 2))
      (F := fun (s : ℝ) (z : E) => F (x + z + s • h))
      (F' := fun z => fderiv ℝ F (x + z + s0 • h) h) (x₀ := s0)
      (bound := fun _ => (K : ℝ) * ‖h‖) (E := E) (α := E) (𝕜 := ℝ)
      (ball_mem_nhds _ (by linarith))
      (Eventually.of_forall (fun s => (hcont s).aestronglyMeasurable))
      (hint s0)
      (by
        have : Measurable fun z : E => fderiv ℝ F (x + z + s0 • h) h :=
          (measurable_fderiv_apply_const ℝ F h).comp (by fun_prop)
        exact this.aestronglyMeasurable)
      (by
        filter_upwards [ae_restrict_mem (μ := μ) (measurableSet_ball (x := (0:E)) (ε := r))] with z hz
        refine LipschitzOnWith.of_dist_le_mul (fun a ha b hb => ?_)
        have hpa := hpts z hz a (by have := ha; rw [mem_ball, Real.dist_eq, abs_lt] at this; linarith [hs0.1]) (by have := ha; rw [mem_ball, Real.dist_eq, abs_lt] at this; linarith [hs0.2])
        have hpb := hpts z hz b (by have := hb; rw [mem_ball, Real.dist_eq, abs_lt] at this; linarith [hs0.1]) (by have := hb; rw [mem_ball, Real.dist_eq, abs_lt] at this; linarith [hs0.2])
        have := hK.dist_le_mul _ hpa _ hpb
        calc dist (F (x + z + a • h)) (F (x + z + b • h)) ≤ K * dist (x + z + a • h) (x + z + b • h) := this
          _ = ((Real.nnabs ((K:ℝ) * ‖h‖) : NNReal) : ℝ) * dist a b := by
              simp only [dist_eq_norm]
              have : x + z + a • h - (x + z + b • h) = (a - b) • h := by rw [sub_smul]; abel
              rw [this, norm_smul, Real.coe_nnabs, abs_of_nonneg (by positivity)]
              ring)
      (integrable_const _)
      (by
        filter_upwards [hae s0 hs0pos.le (by linarith [hs0.2])] with z hz
        have h1 : HasDerivAt (fun s : ℝ => x + z + s • h) h s0 := by
          simpa using ((hasDerivAt_id s0).smul_const h).const_add (x + z)
        have h2 := (hz.hasFDerivAt).comp_hasDerivAt s0 h1
        exact h2)
    exact ⟨key.2, key.1⟩
  -- bound on the derivative
  have hbound : ∀ s0 ∈ Set.Icc t0 t1,
      ‖(∫ z, fderiv ℝ F (x + z + s0 • h) h ∂ν) - m • L‖ ≤ (ε + K * (δ / 2)) * m := by
    intro s0 hs0
    have hs0pos : 0 < s0 := lt_of_lt_of_le ht0 hs0.1
    obtain ⟨_, hi⟩ := hderiv s0 hs0
    have e1 : ∫ z, (fderiv ℝ F (x + z + s0 • h) h - L) ∂ν
        = (∫ z, fderiv ℝ F (x + z + s0 • h) h ∂ν) - m • L := by
      rw [integral_sub hi (integrable_const L), integral_const]
    rw [← e1]
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hae s0 hs0pos.le (by linarith [hs0.2]),
      ae_restrict_mem (μ := μ) (measurableSet_ball (x := (0:E)) (ε := r))] with z hz hzB
    have hzr : ‖z‖ < r := by simpa [hB] using hzB
    have hw := hpts z hzB s0 hs0pos.le (by linarith [hs0.2])
    have hD : ‖fderiv ℝ F (x + z + s0 • h)‖ ≤ K :=
      norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hw) hK
    set h' : E := h + s0⁻¹ • z with hh'
    have hh'h : ‖h' - h‖ < δ / 2 := by
      have : h' - h = s0⁻¹ • z := by rw [hh']; abel
      rw [this, norm_smul, norm_inv, Real.norm_of_nonneg hs0pos.le]
      rw [inv_mul_lt_iff₀ hs0pos]
      have : r ≤ s0 * (δ / 2) := by rw [hr]; nlinarith [hs0.1]
      linarith
    have h1 := hdiff _ hz s0 h' hs0pos (lt_of_le_of_lt hs0.2 ht1δ) (by linarith)
      (by rw [hh', smul_add, smul_smul, mul_inv_cancel₀ hs0pos.ne', one_smul]; abel)
    have h2 : ‖fderiv ℝ F (x + z + s0 • h) (h - h')‖ ≤ K * (δ / 2) := by
      calc _ ≤ ‖fderiv ℝ F (x + z + s0 • h)‖ * ‖h - h'‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * (δ / 2) := by
          rw [norm_sub_rev]
          exact mul_le_mul hD hh'h.le (norm_nonneg _) (by positivity)
    have h3 : fderiv ℝ F (x + z + s0 • h) h - L =
        fderiv ℝ F (x + z + s0 • h) (h - h') + (fderiv ℝ F (x + z + s0 • h) h' - L) := by
      rw [map_sub]; abel
    rw [h3]
    exact (norm_add_le _ _).trans (by linarith)
  -- mean value inequality
  have hMVT : ‖(Φ t1 - t1 • (m • L)) - (Φ t0 - t0 • (m • L))‖ ≤
      (ε + K * (δ / 2)) * m * ‖t1 - t0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => Φ s - s • (m • L))
      (f' := fun s => (∫ z, fderiv ℝ F (x + z + s • h) h ∂ν) - m • L)
      (fun s hs => ?_) (fun s hs => hbound s hs) (convex_Icc t0 t1)
      (Set.left_mem_Icc.2 ht01.le) (Set.right_mem_Icc.2 ht01.le)
    have h2 := ((hderiv s hs).1.sub ((hasDerivAt_id' s).smul_const (m • L)))
    rw [one_smul] at h2
    exact h2.hasDerivWithinAt
  -- comparison of Φ with F
  have hcmp : ∀ s : ℝ, 0 ≤ s → s ≤ 3 * t1 / 2 → ‖Φ s - m • F (x + s • h)‖ ≤ K * r * m := by
    intro s hs0 hs1
    have e1 : Φ s - m • F (x + s • h) = ∫ z, (F (x + z + s • h) - F (x + s • h)) ∂ν := by
      rw [integral_sub (hint s) (integrable_const _), integral_const]
    rw [e1]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun z => F (x + z + s • h) - F (x + s • h))
      (C := K * r) ?_
    · exact this
    filter_upwards [ae_restrict_mem (μ := μ) (measurableSet_ball (x := (0:E)) (ε := r))] with z hzB
    have hzr : ‖z‖ < r := by simpa [hB] using hzB
    have hp1 := hpts z hzB s hs0 hs1
    have hp0 := hpts 0 (by simp [hB, hrpos]) s hs0 hs1
    have := hK.dist_le_mul _ hp1 _ hp0
    rw [dist_eq_norm, dist_eq_norm] at this
    have e : x + z + s • h - (x + 0 + s • h) = z := by abel
    rw [e] at this
    have : ‖F (x + z + s • h) - F (x + s • h)‖ ≤ K * ‖z‖ := by simpa using this
    exact this.trans (by gcongr)
  have hmain : m • (F (x + t1 • h) - F (x + t0 • h) - (t1 - t0) • L) =
      ((Φ t1 - t1 • (m • L)) - (Φ t0 - t0 • (m • L))) - (Φ t1 - m • F (x + t1 • h))
        + (Φ t0 - m • F (x + t0 • h)) := by
    module
  have hfin : m * ‖F (x + t1 • h) - F (x + t0 • h) - (t1 - t0) • L‖ ≤
      m * ((ε + K * (δ / 2)) * (t1 - t0) + K * (t0 * δ)) := by
    have h1 := hcmp t1 (by linarith) (by linarith)
    have h2 := hcmp t0 (by linarith) (by linarith)
    have h3 : ‖m • (F (x + t1 • h) - F (x + t0 • h) - (t1 - t0) • L)‖ ≤
        (ε + K * (δ / 2)) * m * ‖t1 - t0‖ + K * r * m + K * r * m := by
      rw [hmain]
      calc _ ≤ ‖((Φ t1 - t1 • (m • L)) - (Φ t0 - t0 • (m • L))) - (Φ t1 - m • F (x + t1 • h))‖
              + ‖Φ t0 - m • F (x + t0 • h)‖ := norm_add_le _ _
        _ ≤ ‖(Φ t1 - t1 • (m • L)) - (Φ t0 - t0 • (m • L))‖ + ‖Φ t1 - m • F (x + t1 • h)‖
              + ‖Φ t0 - m • F (x + t0 • h)‖ := by
          gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [norm_smul, Real.norm_of_nonneg hmpos.le, Real.norm_of_nonneg (by linarith : 0 ≤ t1 - t0)] at h3
    have : K * r * m + K * r * m = m * (K * (t0 * δ)) := by rw [hr]; ring
    nlinarith
  exact le_of_mul_le_mul_left hfin hmpos

lemma g51_avg_core (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → E) (hFc : Continuous F)
    (x h L : E) (K : NNReal) (ρ : ℝ)
    (hK : LipschitzOnWith K F (ball x ρ)) (ε δ : ℝ) (hδ : 0 < δ)
    (hdiff : ∀ w, DifferentiableAt ℝ F w → ∀ t : ℝ, ∀ h' : E, 0 < t → t < δ → ‖h' - h‖ < δ →
       w = x + t • h' → ‖fderiv ℝ F w h' - L‖ ≤ ε)
    (t1 : ℝ) (ht1 : 0 < t1) (ht1δ : t1 < δ) (ht1ρ : 2 * t1 * (‖h‖ + δ) < ρ) :
    ‖F (x + t1 • h) - F x - t1 • L‖ ≤ (ε + K * (δ / 2)) * t1 := by
  have hc1 : Continuous fun t0 : ℝ => ‖F (x + t1 • h) - F (x + t0 • h) - (t1 - t0) • L‖ := by
    have : Continuous fun t0 : ℝ => F (x + t0 • h) := hFc.comp (by fun_prop)
    fun_prop
  have hc2 : Continuous fun t0 : ℝ => (ε + K * (δ / 2)) * (t1 - t0) + K * (t0 * δ) := by fun_prop
  have h1 := hc1.tendsto 0
  have h2 := hc2.tendsto 0
  have hev : ∀ᶠ t0 in 𝓝[>] (0:ℝ), ‖F (x + t1 • h) - F (x + t0 • h) - (t1 - t0) • L‖ ≤
      (ε + K * (δ / 2)) * (t1 - t0) + K * (t0 * δ) := by
    filter_upwards [Ioo_mem_nhdsGT ht1] with t0 ht0
    exact g51_avg_step μ F hFc x h L K ρ hK ε δ hδ hdiff t0 t1 ht0.1 ht0.2 ht1δ ht1ρ
  have := le_of_tendsto_of_tendsto (h1.mono_left nhdsWithin_le_nhds) (h2.mono_left nhdsWithin_le_nhds) hev
  simpa using this

lemma g51_hasDirDeriv (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → E) (hFc : Continuous F)
    (x h L : E) (K : NNReal) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : LipschitzOnWith K F (ball x ρ))
    (hss : ∀ ε > 0, ∃ δ > 0, ∀ w, DifferentiableAt ℝ F w → ∀ t : ℝ, ∀ h' : E, 0 < t → t < δ →
       ‖h' - h‖ < δ → w = x + t • h' → ‖fderiv ℝ F w h' - L‖ ≤ ε) :
    Tendsto (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x)) (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ0, hδ0, hd0⟩ := hss (ε / 4) (by positivity)
  set δ : ℝ := min δ0 (ε / (2 * (K + 1))) with hδdef
  have hKpos : (0:ℝ) < K + 1 := by positivity
  have hδpos : 0 < δ := lt_min hδ0 (by positivity)
  have hδK : (K:ℝ) * (δ / 2) ≤ ε / 4 := by
    have : δ ≤ ε / (2 * (K + 1)) := min_le_right _ _
    have h2 : (K:ℝ) * δ ≤ (K + 1) * (ε / (2 * (K + 1))) := by
      apply mul_le_mul (by linarith) this hδpos.le (by positivity)
    have h3 : ((K:ℝ) + 1) * (ε / (2 * (K + 1))) = ε / 2 := by field_simp
    nlinarith
  have hT : 0 < min δ (ρ / (2 * (‖h‖ + δ) + 1)) := by
    apply lt_min hδpos; positivity
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  have ht0 : 0 < t := ht.1
  have htδ : t < δ := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htρ : 2 * t * (‖h‖ + δ) < ρ := by
    have h1 : t < ρ / (2 * (‖h‖ + δ) + 1) := lt_of_lt_of_le ht.2 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg h]
  have hcore := g51_avg_core μ F hFc x h L K ρ hK (ε / 4) δ hδpos
    (fun w hw t' h' ht'0 ht'δ hh' hwe => hd0 w hw t' h' ht'0 (lt_of_lt_of_le ht'δ (min_le_left _ _))
      (lt_of_lt_of_le hh' (min_le_left _ _)) hwe) t ht0 htδ htρ
  rw [dist_eq_norm]
  have e : t⁻¹ • (F (x + t • h) - F x) - L = t⁻¹ • (F (x + t • h) - F x - t • L) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
  rw [e, norm_smul, norm_inv, Real.norm_of_nonneg ht0.le, inv_mul_lt_iff₀ ht0]
  have : (ε / 4 + K * (δ / 2)) * t ≤ (ε / 2) * t := by nlinarith
  nlinarith

end avg

section main

abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma g51_fderiv_mem_bJac {n : ℕ} {F : Eu n → Eu n} {w : Eu n} (hw : DifferentiableAt ℝ F w) :
    fderiv ℝ F w ∈ NonsmoothNewton.Shared.bJac F w :=
  ⟨fun _ => w, tendsto_const_nhds, fun _ => hw, tendsto_const_nhds⟩

lemma g51_semi_dir {n : ℕ} (F : Eu n → Eu n) (hFc : Continuous F) (y : Eu n)
    (hss : NonsmoothNewton.Local.SemismoothAt F y) (h : Eu n) :
    ∃ L, NonsmoothNewton.Local.HasDirDerivAt F y h L ∧
      ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : Eu n), 0 < t → t < δ → ‖h' - h‖ < δ →
        ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (y + t • h'), ‖V h' - L‖ < ε := by
  obtain ⟨⟨K, U, hU, hKU⟩, hs⟩ := hss
  obtain ⟨L, hL⟩ := hs h
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨L, ?_, hL⟩
  refine g51_hasDirDeriv MeasureTheory.volume F hFc y h L K ρ hρ (hKU.mono hball) ?_
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hL ε hε
  refine ⟨δ, hδ, fun w hw t h' ht htδ hh' hwe => ?_⟩
  subst hwe
  have := hd t h' ht htδ hh' (fderiv ℝ F (y + t • h'))
    (subset_convexHull ℝ _ (g51_fderiv_mem_bJac hw))
  exact this.le

lemma g51_bJac_norm_le {n : ℕ} (F : Eu n → Eu n) (y : Eu n) (K : NNReal) (U : Set (Eu n))
    (hU : U ∈ 𝓝 y) (hK : LipschitzOnWith K F U) {V : Eu n →L[ℝ] Eu n}
    (hV : V ∈ NonsmoothNewton.Shared.bJac F y) : ‖V‖ ≤ K := by
  obtain ⟨u, hu, hd, hV⟩ := hV
  have h1 : ∀ᶠ k in atTop, u k ∈ interior U := hu.eventually (interior_mem_nhds.2 hU)
  refine le_of_tendsto hV.norm ?_
  filter_upwards [h1] with k hk
  exact norm_fderiv_le_of_lipschitzOn ℝ (mem_interior_iff_mem_nhds.1 hk) hK

lemma g51_bJac_closed {n : ℕ} (F : Eu n → Eu n) (x : Eu n) (y : ℕ → Eu n)
    (V : ℕ → Eu n →L[ℝ] Eu n) (W : Eu n →L[ℝ] Eu n) (hy : Tendsto y atTop (𝓝 x))
    (hV : ∀ k, V k ∈ NonsmoothNewton.Shared.bJac F (y k)) (hW : Tendsto V atTop (𝓝 W)) :
    W ∈ NonsmoothNewton.Shared.bJac F x := by
  have key : ∀ k : ℕ, ∃ w : Eu n, DifferentiableAt ℝ F w ∧ dist w (y k) < 1 / ((k:ℝ) + 1) ∧
      dist (fderiv ℝ F w) (V k) < 1 / ((k:ℝ) + 1) := by
    intro k
    obtain ⟨u, hu, hd, hVk⟩ := hV k
    have hpos : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
    have e1 := (Metric.tendsto_nhds.1 hu) _ hpos
    have e2 := (Metric.tendsto_nhds.1 hVk) _ hpos
    obtain ⟨j, hj⟩ := (e1.and e2).exists
    exact ⟨u j, hd j, hj.1, hj.2⟩
  choose w hwd hw1 hw2 using key
  refine ⟨w, ?_, hwd, ?_⟩
  · refine Filter.Tendsto.congr_dist hy ?_
    refine squeeze_zero (fun k => dist_nonneg) (fun k => by rw [dist_comm]; exact (hw1 k).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · refine Filter.Tendsto.congr_dist hW ?_
    refine squeeze_zero (fun k => dist_nonneg) (fun k => by rw [dist_comm]; exact (hw2 k).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma g51_isUnit_of_inverse {n : ℕ} {V W : Eu n →L[ℝ] Eu n} (h : IsInverse V W) : IsUnit V := by
  refine ⟨⟨V, W, ?_, ?_⟩, rfl⟩
  · exact h.2
  · exact h.1

lemma g51_inv_bound {n : ℕ} (F : Eu n → Eu n) (hF : LocallyLipschitz F) (x : Eu n)
    (hreg : StronglyBDRegularAt F x) :
    ∃ ρ > 0, ∃ c : ℝ, 1 ≤ c ∧ ∀ y ∈ Metric.ball x ρ, ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
      ∃ W, IsInverse V W ∧ ‖W‖ ≤ c := by
  obtain ⟨K, U, hU, hKU⟩ := hF x
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.mem_nhds_iff.1 hU
  by_contra H
  push_neg at H
  have key : ∀ k : ℕ, ∃ y ∈ Metric.ball x (min ρ0 (1 / ((k:ℝ) + 1))),
      ∃ V ∈ NonsmoothNewton.Shared.bJac F y, ∀ W, IsInverse V W → ((k:ℝ) + 1) < ‖W‖ := by
    intro k
    obtain ⟨y, hy, V, hV, hW⟩ := H (min ρ0 (1 / ((k:ℝ) + 1))) (lt_min hρ0 (by positivity))
      ((k:ℝ) + 1) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    exact ⟨y, hy, V, hV, fun W hW' => hW W hW'⟩
  choose y hy V hV hW using key
  have hyx : Tendsto y atTop (𝓝 x) := by
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have := hy k
    rw [Metric.mem_ball] at this
    exact (this.trans_le (min_le_right _ _)).le
  have hbd : ∀ k, V k ∈ Metric.closedBall (0 : Eu n →L[ℝ] Eu n) K := by
    intro k
    have hk := hy k
    rw [Metric.mem_ball] at hk
    have hk' : dist (y k) x < ρ0 := hk.trans_le (min_le_left _ _)
    have hmem : y k ∈ Metric.ball x ρ0 := hk'
    have hUk : U ∈ 𝓝 (y k) := Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem) hball
    have := g51_bJac_norm_le F (y k) K U hUk hKU (hV k)
    simpa using this
  haveI : ProperSpace (Eu n →L[ℝ] Eu n) := by
    haveI : FiniteDimensional ℝ (Eu n →L[ℝ] Eu n) := inferInstance
    exact FiniteDimensional.proper_real _
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Eu n →L[ℝ] Eu n) (K:ℝ)).tendsto_subseq hbd
  have ha : a ∈ NonsmoothNewton.Shared.bJac F x :=
    g51_bJac_closed F x (y ∘ φ) (V ∘ φ) a (hyx.comp hφ.tendsto_atTop) (fun k => hV (φ k)) hlim
  obtain ⟨Wa, hWa⟩ := hreg a ha
  have hua : IsUnit a := g51_isUnit_of_inverse hWa
  obtain ⟨ua, rfl⟩ := hua
  have hcont := NormedRing.inverse_continuousAt ua
  have h1 : Tendsto (fun k => Ring.inverse (V (φ k))) atTop (𝓝 (Ring.inverse (ua : Eu n →L[ℝ] Eu n))) :=
    hcont.tendsto.comp hlim
  have h2 : ∀ᶠ k in atTop, ‖Ring.inverse (V (φ k))‖ < ‖Ring.inverse (ua : Eu n →L[ℝ] Eu n)‖ + 1 := by
    have := h1.norm
    exact this.eventually (gt_mem_nhds (lt_add_one _))
  have h3 : ∀ᶠ k in atTop, IsUnit (V (φ k)) :=
    hlim.eventually (Units.isOpen.mem_nhds ua.isUnit)
  obtain ⟨k, hk1, hk2, hk3⟩ := (h2.and (h3.and (eventually_ge_atTop (Nat.ceil (‖Ring.inverse (ua : Eu n →L[ℝ] Eu n)‖) + 1)))).exists
  have hinv : IsInverse (V (φ k)) (Ring.inverse (V (φ k))) := by
    refine ⟨?_, ?_⟩
    · have := Ring.inverse_mul_cancel _ hk2
      exact this
    · have := Ring.mul_inverse_cancel _ hk2
      exact this
  have := hW (φ k) _ hinv
  have hφk : k ≤ φ k := hφ.id_le k
  have h4 : (Nat.ceil (‖Ring.inverse (ua : Eu n →L[ℝ] Eu n)‖) : ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hk3
  have h5 : (k:ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφk
  have h6 := Nat.le_ceil ‖Ring.inverse (ua : Eu n →L[ℝ] Eu n)‖
  linarith

lemma g51_inv_apply {n : ℕ} {V W : Eu n →L[ℝ] Eu n} (h : IsInverse V W) (v : Eu n) :
    W (V v) = v := by
  have := congrArg (fun T : Eu n →L[ℝ] Eu n => T v) h.1
  simpa using this

lemma g51_inv_unique {n : ℕ} {V W W' : Eu n →L[ℝ] Eu n} (h : IsInverse V W)
    (h' : IsInverse V W') : W = W' := by
  have : W = W.comp (V.comp W') := by rw [h'.2]; rfl
  rw [this, ← ContinuousLinearMap.comp_assoc, h.1]; rfl

lemma g51_lemma_2_6 {n : ℕ} (F : Eu n → Eu n) (hF : LocallyLipschitz F) (x : Eu n)
    (hreg : StronglyBDRegularAt F x) :
    ∃ N ∈ 𝓝 x, ∃ c : ℝ,
      (∀ y ∈ N, ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
        ∃ W : Eu n →L[ℝ] Eu n, IsInverse V W ∧ ‖W‖ ≤ c) ∧
      (∀ y ∈ N, NonsmoothNewton.Local.SemismoothAt F y →
        ∀ h : Eu n, ‖h‖ ≤ c * ‖NonsmoothNewton.Local.dirDeriv F y h‖) := by
  obtain ⟨ρ, hρ, c, hc1, hinv⟩ := g51_inv_bound F hF x hreg
  refine ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρ, c, hinv, ?_⟩
  intro y hy hss h
  have hFc := hF.continuous
  obtain ⟨L, hdir, hsem⟩ := g51_semi_dir F hFc y hss h
  have hdd : NonsmoothNewton.Local.dirDeriv F y h = L := hdir.limUnder_eq
  rw [hdd]
  obtain ⟨⟨K, U, hU, hKU⟩, -⟩ := hss
  obtain ⟨ρ1, hρ1, hball1⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ρ2, hρ2, hball2⟩ := Metric.mem_nhds_iff.1 (Metric.isOpen_ball.mem_nhds hy)
  refine le_of_forall_pos_le_add (fun ε' hε' => ?_)
  set ε : ℝ := ε' / (c + 1) with hε
  have hcpos : 0 < c + 1 := by linarith
  have hεpos : 0 < ε := by positivity
  obtain ⟨δ0, hδ0, hd0⟩ := hsem ε hεpos
  set δ : ℝ := min δ0 ε with hδdef
  have hδpos : 0 < δ := lt_min hδ0 hεpos
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  set ρ3 : ℝ := min ρ1 ρ2 with hρ3
  have hρ3pos : 0 < ρ3 := lt_min hρ1 hρ2
  set τ : ℝ := min (δ / 2) (ρ3 / (2 * (‖h‖ + δ))) with hτ
  have hτpos : 0 < τ := lt_min (by positivity) (by positivity)
  have hτδ : τ ≤ δ / 2 := min_le_left _ _
  have hτρ : τ * (‖h‖ + δ) ≤ ρ3 / 2 := by
    have : τ ≤ ρ3 / (2 * (‖h‖ + δ)) := min_le_right _ _
    calc τ * (‖h‖ + δ) ≤ ρ3 / (2 * (‖h‖ + δ)) * (‖h‖ + δ) := by gcongr
      _ = ρ3 / 2 := by field_simp
  set p : Eu n := y + τ • h with hp
  set S : Set (Eu n) := Metric.ball p (τ * δ / 2) with hS
  have hSsub : S ⊆ Metric.ball y ρ3 := by
    intro w hw
    rw [hS, Metric.mem_ball] at hw
    rw [Metric.mem_ball]
    calc dist w y ≤ dist w p + dist p y := dist_triangle _ _ _
      _ < τ * δ / 2 + τ * ‖h‖ := by
          have : dist p y = τ * ‖h‖ := by
            rw [dist_eq_norm, hp]; simp [norm_smul, abs_of_pos hτpos]
          rw [this]; linarith
      _ ≤ ρ3 := by nlinarith [norm_nonneg h]
  have hKball : LipschitzOnWith K F (Metric.ball y ρ1) := hKU.mono hball1
  obtain ⟨w, hwS, hwd⟩ := g51_exists_diff MeasureTheory.volume F y ρ1 K hKball S Metric.isOpen_ball
    ⟨p, Metric.mem_ball_self (by positivity)⟩
    (fun w hw => Metric.ball_subset_ball (min_le_left _ _) (hSsub hw))
  have hwN : w ∈ Metric.ball x ρ := hball2 (Metric.ball_subset_ball (min_le_right _ _) (hSsub hwS))
  set h' : Eu n := τ⁻¹ • (w - y) with hh'
  have hwe : y + τ • h' = w := by
    rw [hh', smul_smul, mul_inv_cancel₀ hτpos.ne', one_smul]; abel
  have hh'h : ‖h' - h‖ < δ / 2 := by
    have : h' - h = τ⁻¹ • (w - p) := by
      rw [hh', hp, smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hτpos.ne']
      simp only [one_smul]; abel
    rw [this, norm_smul, norm_inv, Real.norm_of_nonneg hτpos.le, inv_mul_lt_iff₀ hτpos]
    have hwS' := hwS
    rw [hS, Metric.mem_ball, dist_eq_norm] at hwS'
    nlinarith
  have hV := hd0 τ h' hτpos (lt_of_le_of_lt hτδ (by linarith)) (lt_of_lt_of_le hh'h (by linarith))
    (fderiv ℝ F w) (by rw [hwe]; exact subset_convexHull ℝ _ (g51_fderiv_mem_bJac hwd))
  obtain ⟨W, hW, hWc⟩ := hinv w hwN _ (g51_fderiv_mem_bJac hwd)
  have e1 : ‖h'‖ ≤ c * ‖fderiv ℝ F w h'‖ := by
    calc ‖h'‖ = ‖W (fderiv ℝ F w h')‖ := by rw [g51_inv_apply hW]
      _ ≤ ‖W‖ * ‖fderiv ℝ F w h'‖ := W.le_opNorm _
      _ ≤ c * ‖fderiv ℝ F w h'‖ := by gcongr
  have e2 : ‖fderiv ℝ F w h'‖ ≤ ‖L‖ + ε := by
    have := norm_le_insert' (fderiv ℝ F w h') L
    linarith
  have e3 : ‖h‖ ≤ ‖h'‖ + δ / 2 := by
    have := norm_sub_norm_le h h'
    rw [norm_sub_rev] at this
    linarith
  have hc0 : 0 ≤ c := by linarith
  have e4 : c * ‖fderiv ℝ F w h'‖ ≤ c * (‖L‖ + ε) := mul_le_mul_of_nonneg_left e2 hc0
  have e5 : (c + 1) * ε = ε' := by rw [hε]; field_simp
  nlinarith

lemma g51_key_diff {n : ℕ} (F : Eu n → Eu n) (hFc : Continuous F) (x : Eu n)
    (hss : NonsmoothNewton.Local.SemismoothAt F x) :
    ∀ ε > 0, ∃ δ > 0, ∀ u : Eu n, DifferentiableAt ℝ F u → ‖u - x‖ < δ →
      ‖F u - F x - fderiv ℝ F u (u - x)‖ ≤ ε * ‖u - x‖ := by
  intro ε hε
  have hss' := hss
  obtain ⟨⟨K, U, hU, hKU⟩, -⟩ := hss'
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hK : LipschitzOnWith K F (Metric.ball x ρ) := hKU.mono hball
  set ε1 : ℝ := ε / (K + 2) with hε1
  have hε1pos : 0 < ε1 := by positivity
  have hloc : ∀ h0 ∈ Metric.sphere (0 : Eu n) 1, ∃ r : ℝ, 0 < r ∧ r ≤ ε1 ∧ r ≤ 1 ∧ r ≤ ρ / 4 ∧
      ∃ L : Eu n, (∀ t : ℝ, 0 < t → t < r → ‖F (x + t • h0) - F x - t • L‖ ≤ ε1 * t) ∧
        (∀ (t : ℝ) (h' : Eu n), 0 < t → t < r → ‖h' - h0‖ < r →
          ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h'), ‖V h' - L‖ < ε1) := by
    intro h0 _
    obtain ⟨L, hdir, hsem⟩ := g51_semi_dir F hFc x hss h0
    obtain ⟨δ1, hδ1, hd1⟩ := hsem ε1 hε1pos
    have hev := (Metric.tendsto_nhds.1 hdir) ε1 hε1pos
    obtain ⟨T, hT, hTsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨min (min δ1 (min T ε1)) (min 1 (ρ / 4)), by
      refine lt_min (lt_min hδ1 (lt_min hT hε1pos)) (lt_min one_pos (by positivity)), ?_, ?_, ?_, L, ?_, ?_⟩
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · intro t ht htr
      have htT : t < T := lt_of_lt_of_le htr ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      have := hTsub ⟨ht, htT⟩
      simp only [Set.mem_setOf_eq, dist_eq_norm] at this
      have e : t⁻¹ • (F (x + t • h0) - F x) - L = t⁻¹ • (F (x + t • h0) - F x - t • L) := by
        simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      rw [e, norm_smul, norm_inv, Real.norm_of_nonneg ht.le, inv_mul_lt_iff₀ ht] at this
      nlinarith
    · intro t h' ht htr hh' V hV
      exact hd1 t h' ht (lt_of_lt_of_le htr ((min_le_left _ _).trans (min_le_left _ _)))
        (lt_of_lt_of_le hh' ((min_le_left _ _).trans (min_le_left _ _))) V hV
  choose! r hr0 hrε hr1 hrρ L hL1 hL2 using hloc
  obtain ⟨tf, htf, hcov⟩ := (isCompact_sphere (0 : Eu n) 1).elim_nhds_subcover
    (fun h0 => Metric.ball h0 (r h0)) (fun h0 hh0 => Metric.ball_mem_nhds h0 (hr0 h0 hh0))
  have hex : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ tf, δ < r i := by
    have : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ∈ Set.Ioi 0 ∧ ∀ i ∈ tf, δ < r i := by
      refine (eventually_mem_nhdsWithin).and ?_
      refine (Filter.eventually_all_finset tf).2 (fun i hi => ?_)
      have := Ioo_mem_nhdsGT (hr0 i (htf i hi))
      filter_upwards [this] with δ hδ using hδ.2
    obtain ⟨δ, hδ1, hδ2⟩ := this.exists
    exact ⟨δ, hδ1, hδ2⟩
  obtain ⟨δ, hδ, hδr⟩ := hex
  refine ⟨δ, hδ, fun u hu hux => ?_⟩
  by_cases hux0 : u = x
  · subst hux0; simp
  set t : ℝ := ‖u - x‖ with ht
  have htpos : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 hux0)
  set h' : Eu n := t⁻¹ • (u - x) with hh'
  have hh'norm : ‖h'‖ = 1 := by
    rw [hh', norm_smul, norm_inv, Real.norm_of_nonneg htpos.le, ht]
    exact inv_mul_cancel₀ htpos.ne'
  have hh'S : h' ∈ Metric.sphere (0 : Eu n) 1 := by simpa using hh'norm
  have hue : u = x + t • h' := by
    rw [hh', smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]; abel
  obtain ⟨i, hi, hhi⟩ := Set.mem_iUnion₂.1 (hcov hh'S)
  have hi' : ‖h' - i‖ < r i := by simpa [dist_eq_norm] using hhi
  have hti : t < r i := lt_trans hux (hδr i hi)
  have hiS := htf i hi
  have hinorm : ‖i‖ = 1 := by simpa using hiS
  have hr1i := hr1 i hiS
  have hrρi := hrρ i hiS
  -- membership in the ball
  have hp1 : x + t • h' ∈ Metric.ball x ρ := by
    rw [mem_ball_iff_norm]
    have : x + t • h' - x = t • h' := by abel
    rw [this, norm_smul, hh'norm, Real.norm_of_nonneg htpos.le]; linarith
  have hp2 : x + t • i ∈ Metric.ball x ρ := by
    rw [mem_ball_iff_norm]
    have : x + t • i - x = t • i := by abel
    rw [this, norm_smul, hinorm, Real.norm_of_nonneg htpos.le]; linarith
  have hDu : DifferentiableAt ℝ F u := by assumption
  have hmem : fderiv ℝ F u ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h') := by
    rw [← hue]; exact subset_convexHull ℝ _ (g51_fderiv_mem_bJac hDu)
  have hA := hL2 i hiS t h' htpos hti hi' _ hmem
  have hB := hL1 i hiS t htpos hti
  have hC := hK.dist_le_mul _ hp1 _ hp2
  rw [dist_eq_norm, dist_eq_norm] at hC
  have hC2 : ‖(x + t • h') - (x + t • i)‖ = t * ‖h' - i‖ := by
    have : (x + t • h') - (x + t • i) = t • (h' - i) := by rw [smul_sub]; abel
    rw [this, norm_smul, Real.norm_of_nonneg htpos.le]
  have hdecomp : F u - F x - fderiv ℝ F u (u - x) =
      (F (x + t • h') - F (x + t • i)) + (F (x + t • i) - F x - t • L i) +
        t • (L i - fderiv ℝ F u h') := by
    have hux' : u - x = t • h' := by rw [hue]; abel
    rw [hux', ← hue, map_smul]; module
  have hnorm_t : ‖u - x‖ = t := rfl
  rw [hdecomp]
  have hfirst : ‖F (x + t • h') - F (x + t • i)‖ ≤ K * (t * ε1) := by
    refine hC.trans ?_
    rw [hC2]
    have : ‖h' - i‖ ≤ ε1 := hi'.le.trans (hrε i hiS)
    gcongr
  have hthird : ‖t • (L i - fderiv ℝ F u h')‖ ≤ t * ε1 := by
    rw [norm_smul, Real.norm_of_nonneg htpos.le, norm_sub_rev]
    gcongr
  calc _ ≤ ‖F (x + t • h') - F (x + t • i)‖ + ‖F (x + t • i) - F x - t • L i‖ +
        ‖t • (L i - fderiv ℝ F u h')‖ := norm_add₃_le
    _ ≤ K * (t * ε1) + ε1 * t + t * ε1 := by linarith
    _ = ε * t := by rw [hε1]; field_simp; ring

lemma g51_key {n : ℕ} (F : Eu n → Eu n) (hFc : Continuous F) (x : Eu n)
    (hss : NonsmoothNewton.Local.SemismoothAt F x) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : Eu n, ‖y - x‖ < δ → ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
      ‖F y - F x - V (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := g51_key_diff F hFc x hss ε hε
  refine ⟨δ, hδ, fun y hy V hV => ?_⟩
  obtain ⟨u, hu, hdiff, hVu⟩ := hV
  have hev : ∀ᶠ k in atTop, ‖u k - x‖ < δ := by
    have : Tendsto (fun k => ‖u k - x‖) atTop (𝓝 ‖y - x‖) := (hu.sub_const x).norm
    exact this.eventually (gt_mem_nhds hy)
  have h1 : Tendsto (fun k => ‖F (u k) - F x - fderiv ℝ F (u k) (u k - x)‖) atTop
      (𝓝 ‖F y - F x - V (y - x)‖) := by
    refine Tendsto.norm ?_
    refine ((((hFc.tendsto y).comp hu).sub tendsto_const_nhds)).sub ?_
    have hc : Continuous (fun p : (Eu n →L[ℝ] Eu n) × Eu n => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    exact (hc.tendsto (V, y - x)).comp (hVu.prodMk_nhds (hu.sub_const x))
  have h2 : Tendsto (fun k => ε * ‖u k - x‖) atTop (𝓝 (ε * ‖y - x‖)) :=
    ((hu.sub_const x).norm).const_mul ε
  exact le_of_tendsto_of_tendsto h1 h2 (hev.mono fun k hk => hd (u k) (hdiff k) hk)


section new
open NonsmoothNewton.Local NonsmoothNewton.Shared

lemma g53_normFn_hasDir {n : ℕ} (F : Eu n → Eu n) (y dy : Eu n)
    (hd : HasDirDerivAt F y dy (-F y)) :
    HasDirDerivAt (normFn F) y dy (-2 * normFn F y) := by
  unfold HasDirDerivAt at hd ⊢
  have h1 : Tendsto (fun t : ℝ => inner ℝ (F y) (t⁻¹ • (F (y + t • dy) - F y))) (𝓝[>] 0)
      (𝓝 (inner ℝ (F y) (-F y))) := tendsto_const_nhds.inner hd
  have h2 : Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t / 2) (𝓝 (0:ℝ)) (𝓝 (0 / 2)) :=
      (continuous_id.div_const 2).tendsto 0
    rw [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun t : ℝ => ‖t⁻¹ • (F (y + t • dy) - F y)‖ ^ 2) (𝓝[>] 0)
      (𝓝 (‖-F y‖ ^ 2)) := hd.norm.pow 2
  have key := h1.add (h2.mul h3)
  have hlim : inner ℝ (F y) (-F y) + 0 * ‖-F y‖ ^ 2 = -2 * normFn F y := by
    rw [inner_neg_right, real_inner_self_eq_norm_sq]
    unfold normFn; ring
  rw [hlim] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  have hb : F (y + t • dy) = F y + t • (t⁻¹ • (F (y + t • dy) - F y)) := by
    rw [smul_smul, mul_inv_cancel₀ ht'.ne', one_smul]; abel
  generalize t⁻¹ • (F (y + t • dy) - F y) = G at hb ⊢
  simp only [normFn]
  rw [hb, norm_add_sq_real, norm_smul, Real.norm_of_nonneg ht'.le, real_inner_smul_right]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma g53_dirDeriv_normFn {n : ℕ} (F : Eu n → Eu n) (y dy : Eu n)
    (hd : HasDirDerivAt F y dy (-F y)) :
    dirDeriv (normFn F) y dy = -2 * normFn F y :=
  (g53_normFn_hasDir F y dy hd).limUnder_eq

lemma g53_armijo_le {n : ℕ} (F : Eu n → Eu n) (y d : Eu n) (hd : HasDirDerivAt F y d (-F y))
    (s β σ : ℝ) (hσ : 0 < σ) (m : ℕ) (hα : 0 ≤ β ^ m * s)
    (ht : armijoTest F s β σ y d m) :
    normFn F (y + (β ^ m * s) • d) ≤ normFn F y := by
  unfold armijoTest at ht
  rw [g53_dirDeriv_normFn F y d hd] at ht
  have h0 : 0 ≤ normFn F y := by unfold normFn; positivity
  have : 0 ≤ σ * (β ^ m * s) * normFn F y := by positivity
  nlinarith

end new

section step
open NonsmoothNewton.Local NonsmoothNewton.Shared

lemma g53_step {n : ℕ} (F : Eu n → Eu n) (hF : LocallyLipschitz F) (xs : Eu n)
    (hzero : F xs = 0) (hss : SemismoothAt F xs) (hreg : StronglyBDRegularAt F xs)
    (hssN : ∀ᶠ y in 𝓝 xs, SemismoothAt F y) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : Eu n, ‖y - xs‖ < δ → ∀ d : Eu n,
      HasDirDerivAt F y d (-F y) → ‖y + d - xs‖ ≤ ε * ‖y - xs‖ := by
  intro ε hε
  have hFc := hF.continuous
  obtain ⟨ρ, hρ, c, hc1, hinv⟩ := g51_inv_bound F hF xs hreg
  have hcpos : 0 < c := by linarith
  have hss' := hss
  obtain ⟨⟨K, U, hU, hKU⟩, -⟩ := hss'
  obtain ⟨ρL, hρL, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hK : LipschitzOnWith K F (Metric.ball xs ρL) := hKU.mono hball
  set ε1 : ℝ := ε / c with hε1
  have hε1pos : 0 < ε1 := by positivity
  obtain ⟨δ1, hδ1, hkey⟩ := g51_key_diff F hFc xs hss ε1 hε1pos
  obtain ⟨r, hr, hrss⟩ := Metric.eventually_nhds_iff.1 hssN
  set R : ℝ := min (min δ1 ρ) ρL with hR
  have hRpos : 0 < R := lt_min (lt_min hδ1 hρ) hρL
  have hR1 : R ≤ δ1 := (min_le_left _ _).trans (min_le_left _ _)
  have hR2 : R ≤ ρ := (min_le_left _ _).trans (min_le_right _ _)
  have hR3 : R ≤ ρL := min_le_right _ _
  have hKnn : (0:ℝ) ≤ K := NNReal.coe_nonneg K
  refine ⟨min (R / 2) r, lt_min (by positivity) hr, fun y hy d hd => ?_⟩
  have hyR : ‖y - xs‖ < R / 2 := lt_of_lt_of_le hy (min_le_left _ _)
  have hyr : ‖y - xs‖ < r := lt_of_lt_of_le hy (min_le_right _ _)
  have hssy : SemismoothAt F y := hrss (by rwa [dist_eq_norm])
  obtain ⟨L, hdir, hsem⟩ := g51_semi_dir F hFc y hssy d
  have hL : L = -F y := tendsto_nhds_unique hdir hd
  subst hL
  have hyball : y ∈ Metric.ball xs ρL := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have claim : ∀ τ > 0, ‖y + d - xs‖ ≤ c * (ε1 * ‖y - xs‖ + (2 + K) * τ) := by
    intro τ hτ
    obtain ⟨δ', hδ', hδ'1⟩ := hsem τ hτ
    set δ'' : ℝ := min (min δ' τ) 1 with hδ''
    have hδ''pos : 0 < δ'' := lt_min (lt_min hδ' hτ) one_pos
    have hδ''1 : δ'' ≤ δ' := (min_le_left _ _).trans (min_le_left _ _)
    have hδ''2 : δ'' ≤ τ := (min_le_left _ _).trans (min_le_right _ _)
    have hδ''3 : δ'' ≤ 1 := min_le_right _ _
    set D : ℝ := ‖d‖ + 1 with hD
    have hDpos : 0 < D := by positivity
    have hq : 0 < (ε1 + 2 * K + 1) * D := by positivity
    set t : ℝ := min (δ' / 2) (min (τ / ((ε1 + 2 * K + 1) * D)) (R / (4 * D))) with ht
    have htpos : 0 < t := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    have ht1 : t < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht2' : t ≤ τ / ((ε1 + 2 * K + 1) * D) := (min_le_right _ _).trans (min_le_left _ _)
    have ht3' : t ≤ R / (4 * D) := (min_le_right _ _).trans (min_le_right _ _)
    have ht2 : (ε1 + 2 * K) * (t * D) ≤ τ := by
      have h1 : t * ((ε1 + 2 * K + 1) * D) ≤ τ := by
        rwa [le_div_iff₀ hq] at ht2'
      have h2 : 0 ≤ t * D := by positivity
      nlinarith
    have ht3 : t * D ≤ R / 4 := by
      have h1 : t * (4 * D) ≤ R := by rwa [le_div_iff₀ (by positivity)] at ht3'
      nlinarith
    have hSR : ∀ w ∈ Metric.ball (y + t • d) (t * δ''), ‖w - xs‖ < R := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have e : w - xs = (w - (y + t • d)) + (y - xs) + t • d := by abel
      have : ‖w - xs‖ ≤ ‖w - (y + t • d)‖ + ‖y - xs‖ + ‖t • d‖ := by
        rw [e]; exact (norm_add₃_le)
      rw [norm_smul, Real.norm_of_nonneg htpos.le] at this
      have h4 : t * δ'' ≤ t * 1 := by gcongr
      have h5 : t * ‖d‖ + t * 1 = t * D := by rw [hD]; ring
      nlinarith
    obtain ⟨u, huS, hudiff⟩ := g51_exists_diff MeasureTheory.volume F xs ρL K hK
      (Metric.ball (y + t • d) (t * δ'')) Metric.isOpen_ball
      ⟨y + t • d, Metric.mem_ball_self (by positivity)⟩
      (fun w hw => by
        rw [Metric.mem_ball, dist_eq_norm]; exact (hSR w hw).trans_le hR3)
    have hex : ∃ h' : Eu n, u = y + t • h' ∧ ‖h' - d‖ < δ'' := by
      refine ⟨t⁻¹ • (u - y), ?_, ?_⟩
      · rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]; abel
      · rw [Metric.mem_ball, dist_eq_norm] at huS
        have e : t⁻¹ • (u - y) - d = t⁻¹ • (u - (y + t • d)) := by
          have : u - (y + t • d) = (u - y) - t • d := by abel
          rw [this, smul_sub t⁻¹ (u - y) (t • d), smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
        rw [e, norm_smul, norm_inv, Real.norm_of_nonneg htpos.le]
        calc t⁻¹ * ‖u - (y + t • d)‖ < t⁻¹ * (t * δ'') := by gcongr
          _ = δ'' := by field_simp
    obtain ⟨h', hu_eq, hh'd⟩ := hex
    have huR : ‖u - xs‖ < R := hSR u huS
    have hu_ball : u ∈ Metric.ball xs ρL := by
      rw [Metric.mem_ball, dist_eq_norm]; exact huR.trans_le hR3
    have hu_ball2 : u ∈ Metric.ball xs ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact huR.trans_le hR2
    set V : Eu n →L[ℝ] Eu n := fderiv ℝ F u with hV
    have hVmem : V ∈ clarkeJac F (y + t • h') := by
      rw [← hu_eq]; exact subset_convexHull ℝ _ (g51_fderiv_mem_bJac hudiff)
    have hVb : V ∈ bJac F u := g51_fderiv_mem_bJac hudiff
    have E1 := hδ'1 t h' htpos ht1 (lt_of_lt_of_le hh'd hδ''1) V hVmem
    have E1' : ‖F y + V h'‖ < τ := by
      rwa [sub_neg_eq_add, add_comm] at E1
    obtain ⟨W, hW, hWc⟩ := hinv u hu_ball2 V hVb
    have E3 := hkey u hudiff (huR.trans_le hR1)
    rw [hzero, sub_zero] at E3
    have hVK : ‖V‖ ≤ K := g51_bJac_norm_le F u K (Metric.ball xs ρL)
      (Metric.isOpen_ball.mem_nhds hu_ball) hK hVb
    have hh'D : ‖h'‖ ≤ D := by
      have : ‖h'‖ ≤ ‖h' - d‖ + ‖d‖ := by
        have := norm_add_le (h' - d) d; simpa using this
      rw [hD]; linarith
    have huy : ‖u - y‖ ≤ t * D := by
      have : u - y = t • h' := by rw [hu_eq]; abel
      rw [this, norm_smul, Real.norm_of_nonneg htpos.le]
      gcongr
    have huxs : ‖u - xs‖ ≤ ‖y - xs‖ + t * D := by
      have : ‖u - xs‖ ≤ ‖u - y‖ + ‖y - xs‖ := by
        have := norm_add_le (u - y) (y - xs); simpa using this
      linarith
    have A1 : ‖F u - V (u - xs)‖ ≤ ε1 * (‖y - xs‖ + t * D) := by
      calc ‖F u - V (u - xs)‖ ≤ ε1 * ‖u - xs‖ := E3
        _ ≤ ε1 * (‖y - xs‖ + t * D) := by gcongr
    have A2 : ‖F u - F y‖ ≤ K * (t * D) := by
      have := hK.dist_le_mul u hu_ball y hyball
      rw [dist_eq_norm, dist_eq_norm] at this
      calc ‖F u - F y‖ ≤ K * ‖u - y‖ := this
        _ ≤ K * (t * D) := by gcongr
    have A4 : ‖t • V h'‖ ≤ K * (t * D) := by
      rw [norm_smul, Real.norm_of_nonneg htpos.le]
      have : ‖V h'‖ ≤ K * D := (V.le_opNorm h').trans (mul_le_mul hVK hh'D (norm_nonneg _) hKnn)
      calc t * ‖V h'‖ ≤ t * (K * D) := by gcongr
        _ = K * (t * D) := by ring
    have A5 : ‖V (d - h')‖ ≤ K * τ := by
      have h1 : ‖d - h'‖ ≤ τ := by rw [norm_sub_rev]; exact hh'd.le.trans hδ''2
      calc ‖V (d - h')‖ ≤ ‖V‖ * ‖d - h'‖ := V.le_opNorm _
        _ ≤ K * τ := mul_le_mul hVK h1 (norm_nonneg _) hKnn
    have hid : V (y + d - xs) = (V (u - xs) - F u) + (F u - F y) + (F y + V h') - t • V h' + V (d - h') := by
      have e : y + d - xs = (u - xs) - t • h' + (d - h') + h' := by rw [hu_eq]; abel
      rw [e, map_add, map_add, map_sub, map_smul]
      abel
    have hnorm : ‖V (y + d - xs)‖ ≤ ε1 * ‖y - xs‖ + (2 + K) * τ := by
      rw [hid]
      have := norm_add_le ((V (u - xs) - F u) + (F u - F y) + (F y + V h') - t • V h') (V (d - h'))
      have h2 := norm_sub_le ((V (u - xs) - F u) + (F u - F y) + (F y + V h')) (t • V h')
      have h3 := norm_add_le ((V (u - xs) - F u) + (F u - F y)) (F y + V h')
      have h4 := norm_add_le (V (u - xs) - F u) (F u - F y)
      have h5 : ‖V (u - xs) - F u‖ = ‖F u - V (u - xs)‖ := norm_sub_rev _ _
      linarith
    calc ‖y + d - xs‖ = ‖W (V (y + d - xs))‖ := by rw [g51_inv_apply hW]
      _ ≤ ‖W‖ * ‖V (y + d - xs)‖ := W.le_opNorm _
      _ ≤ c * (ε1 * ‖y - xs‖ + (2 + K) * τ) := mul_le_mul hWc hnorm (norm_nonneg _) hcpos.le
  apply le_of_forall_pos_le_add
  intro e he
  have h2K : (0:ℝ) < 2 + K := by linarith
  have := claim (e / (c * (2 + K))) (by positivity)
  calc ‖y + d - xs‖ ≤ c * (ε1 * ‖y - xs‖ + (2 + K) * (e / (c * (2 + K)))) := this
    _ = ε * ‖y - xs‖ + e := by rw [hε1]; field_simp

end step

section cor
open NonsmoothNewton.Local NonsmoothNewton.Shared

lemma g53_cor34 {n : ℕ} (F : Eu n → Eu n) (hF : LocallyLipschitz F) (xs : Eu n)
    (hzero : F xs = 0) (hss : SemismoothAt F xs) (hreg : StronglyBDRegularAt F xs)
    (hssN : ∀ᶠ y in 𝓝 xs, SemismoothAt F y) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : Eu n, ‖y - xs‖ ≤ δ → ∀ dy : Eu n,
      HasDirDerivAt F y dy (-F y) →
        ‖y + dy - xs‖ ≤ ε * ‖y - xs‖ ∧ ‖F (y + dy)‖ ≤ ε * ‖F y‖ := by
  intro ε hε
  obtain ⟨N, hN, c0, -, hdd⟩ := g51_lemma_2_6 F hF xs hreg
  set c : ℝ := max c0 1 with hcdef
  have hcpos : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hdd' : ∀ y ∈ N, SemismoothAt F y → ∀ h : Eu n, ‖h‖ ≤ c * ‖dirDeriv F y h‖ :=
    fun y hy hs h => (hdd y hy hs h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨ρN, hρN, hNb⟩ := Metric.mem_nhds_iff.1 hN
  have hss' := hss
  obtain ⟨⟨K, U, hU, hKU⟩, -⟩ := hss'
  obtain ⟨ρL, hρL, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hK : LipschitzOnWith K F (Metric.ball xs ρL) := hKU.mono hball
  obtain ⟨r, hr, hrss⟩ := Metric.eventually_nhds_iff.1 hssN
  have hKnn : (0:ℝ) ≤ K := NNReal.coe_nonneg K
  set ε' : ℝ := min (min (1 / 2) ε) (ε / ((K + 1) * (2 * c))) with hε'
  have hε'pos : 0 < ε' := lt_min (lt_min (by norm_num) hε) (by positivity)
  have hε'1 : ε' ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε'2 : ε' ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hε'3 : ε' ≤ ε / ((K + 1) * (2 * c)) := min_le_right _ _
  obtain ⟨δ0, hδ0, hstep⟩ := g53_step F hF xs hzero hss hreg hssN ε' hε'pos
  set δ : ℝ := min (min (δ0 / 2) (min ρN ρL / 2)) (r / 2) with hδ
  have hδpos : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hδ1 : δ ≤ δ0 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ min ρN ρL / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ r / 2 := min_le_right _ _
  have hρN' : min ρN ρL ≤ ρN := min_le_left _ _
  have hρL' : min ρN ρL ≤ ρL := min_le_right _ _
  refine ⟨δ, hδpos, fun y hy d hd => ?_⟩
  have hA : ‖y + d - xs‖ ≤ ε' * ‖y - xs‖ := hstep y (by linarith) d hd
  have hyN : y ∈ N := hNb (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  have hssy : SemismoothAt F y := hrss (by rw [dist_eq_norm]; linarith)
  have hdn : ‖d‖ ≤ c * ‖F y‖ := by
    have := hdd' y hyN hssy d
    have e : dirDeriv F y d = -F y := hd.limUnder_eq
    rwa [e, norm_neg] at this
  have hyc : ‖y - xs‖ ≤ 2 * c * ‖F y‖ := by
    have e : y - xs = (y + d - xs) - d := by abel
    have : ‖y - xs‖ ≤ ‖y + d - xs‖ + ‖d‖ := by
      have := norm_sub_le (y + d - xs) d
      rw [← e] at this; exact this
    nlinarith [norm_nonneg (y - xs)]
  refine ⟨hA.trans (mul_le_mul_of_nonneg_right hε'2 (norm_nonneg _)), ?_⟩
  have hmem : y + d ∈ Metric.ball xs ρL := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖y + d - xs‖ ≤ 1 / 2 * ‖y - xs‖ :=
      hA.trans (mul_le_mul_of_nonneg_right hε'1 (norm_nonneg _))
    linarith
  have hdist := hK.dist_le_mul _ hmem xs (Metric.mem_ball_self hρL)
  rw [dist_eq_norm, dist_eq_norm, hzero, sub_zero] at hdist
  have h1 : (K:ℝ) * ε' * (2 * c) ≤ ε := by
    have h2 : (K:ℝ) * ε' * (2 * c) ≤ K * (ε / ((K + 1) * (2 * c))) * (2 * c) := by gcongr
    have h3 : (K:ℝ) * (ε / ((K + 1) * (2 * c))) * (2 * c) = K / (K + 1) * ε := by
      field_simp
    have h4 : (K:ℝ) / (K + 1) * ε ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc ‖F (y + d)‖ ≤ K * ‖y + d - xs‖ := hdist
    _ ≤ K * (ε' * ‖y - xs‖) := by gcongr
    _ ≤ K * (ε' * (2 * c * ‖F y‖)) := by gcongr
    _ = (K * ε' * (2 * c)) * ‖F y‖ := by ring
    _ ≤ ε * ‖F y‖ := by gcongr

lemma g53_unit_step {n : ℕ} (F : Eu n → Eu n) (hF : LocallyLipschitz F)
    (β σ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (x d : ℕ → Eu n) (α : ℕ → ℝ)
    (hrun : IsDampedNewtonRun F 1 β σ x d α)
    (xstar : Eu n)
    (hzero : F xstar = 0) (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    ∃ δbar > 0, ∀ k, ‖x k - xstar‖ ≤ δbar →
      α k = 1 ∧ x (k + 1) = x k + d k ∧ ‖x (k + 1) - xstar‖ ≤ (1 / 2) * ‖x k - xstar‖ := by
  set ε0 : ℝ := min (1 / 2) ((1 - 2 * σ) / 2) with hε0
  have hε0pos : 0 < ε0 := lt_min (by norm_num) (by linarith)
  have hε01 : ε0 ≤ 1 / 2 := min_le_left _ _
  have hε02 : ε0 ≤ (1 - 2 * σ) / 2 := min_le_right _ _
  obtain ⟨δ, hδ, hc⟩ := g53_cor34 F hF xstar hzero hss hreg hssN ε0 hε0pos
  refine ⟨δ, hδ, fun k hk => ?_⟩
  obtain ⟨hd, ⟨m, htest, hmin, hα⟩, hx⟩ := hrun k
  obtain ⟨hA, hB⟩ := hc (x k) hk (d k) hd
  have htest0 : armijoTest F 1 β σ (x k) (d k) 0 := by
    unfold armijoTest
    rw [g53_dirDeriv_normFn F (x k) (d k) hd]
    simp only [pow_zero, mul_one, one_smul]
    have hg : 0 ≤ normFn F (x k) := by unfold normFn; positivity
    have h1 : normFn F (x k + d k) ≤ ε0 ^ 2 * normFn F (x k) := by
      unfold normFn
      have : ‖F (x k + d k)‖ ^ 2 ≤ (ε0 * ‖F (x k)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hB 2
      nlinarith
    have h2 : ε0 ^ 2 ≤ 1 - 2 * σ := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 h2) hg]
  have hm0 : m = 0 := by
    by_contra hne
    exact hmin 0 (Nat.pos_of_ne_zero hne) htest0
  subst hm0
  have hα1 : α k = 1 := by rw [hα]; simp
  refine ⟨hα1, by rw [hx, hα1, one_smul], ?_⟩
  have e : x (k + 1) = x k + d k := by rw [hx, hα1, one_smul]
  rw [e]
  exact hA.trans (mul_le_mul_of_nonneg_right hε01 (norm_nonneg _))

end cor

end main

end QiNonsmoothEq.Damped

open QiNonsmoothEq.Damped
open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem solution {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (hB : ∀ y, BDiffAt F y)
    (β σ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hrun : IsDampedNewtonRun F 1 β σ x d α) (hne : ∀ k, F (x k) ≠ 0)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hzero : F xstar = 0) (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    ∃ δbar > 0, ∀ k, ‖x k - xstar‖ ≤ δbar →
      α k = 1 ∧ x (k + 1) = x k + d k ∧ ‖x (k + 1) - xstar‖ ≤ (1 / 2) * ‖x k - xstar‖ := by
  exact g53_unit_step F hF β σ hβ0 hβ1 hσ0 hσ1 x d α hrun xstar hzero hss hreg hssN
