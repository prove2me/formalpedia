-- Prove2me | solution 1 for QiNonsmoothEq.Local.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:57:29.006387+00:00
-- url     : https://prove2.me/submissions/95c1c315-9915-4813-a78c-6a1b6e31ca2d

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_QiNonsmoothEq_Local_Setting
open Filter Topology


namespace QiNonsmoothEq.Local
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

end main

end QiNonsmoothEq.Local

open QiNonsmoothEq.Local


theorem solution {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (x : EuclideanSpace ℝ (Fin n))
    (hreg : StronglyBDRegularAt F x) :
    ∃ N ∈ 𝓝 x, ∃ c : ℝ,
      (∀ y ∈ N, ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
        ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W ∧ ‖W‖ ≤ c) ∧
      (∀ y ∈ N, NonsmoothNewton.Local.SemismoothAt F y →
        ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖NonsmoothNewton.Local.dirDeriv F y h‖) := by
  exact g51_lemma_2_6 F hF x hreg
