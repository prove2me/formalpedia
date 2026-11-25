-- Prove2me | solution 1 for UpperTheory.map_mul_volume_of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:40.565861+00:00
-- url     : https://prove2.me/submissions/ecfbb560-be77-4304-a0d6-f17b453c499b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapMulVolumeOfSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Set
private lemma mulE_apply {n : ℕ} (a x : Fin n → Fin n → ℂ) (i j : Fin n) :
    mulE a x i j = ∑ k, a i k * x k j := by
  simp [mulE, Matrix.mul_apply]
private lemma continuous_mulE {n : ℕ} :
    Continuous (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => mulE p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulE_apply]
  fun_prop
private lemma measurable_mulE {n : ℕ} (a : Fin n → Fin n → ℂ) : Measurable (mulE a) :=
  (continuous_mulE.comp (Continuous.prodMk_right a)).measurable
private lemma norm_mulE_le {n : ℕ} (a x : Fin n → Fin n → ℂ) :
    ‖mulE a x‖ ≤ n * (‖a‖ * ‖x‖) := by
  have h0 : (0 : ℝ) ≤ n * (‖a‖ * ‖x‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  rw [mulE_apply]
  calc ‖∑ k, a i k * x k j‖ ≤ ∑ k, ‖a i k * x k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, ‖a‖ * ‖x‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (a i) k).trans (norm_le_pi_norm a i))
          ((norm_le_pi_norm (x k) j).trans (norm_le_pi_norm x k)) (norm_nonneg _) (norm_nonneg _)
    _ = n * (‖a‖ * ‖x‖) := by simp
private lemma continuous_detE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ => (Matrix.of v).det) :=
  Continuous.matrix_det (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id
private lemma continuous_adjE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ =>
      (Matrix.of.symm (Matrix.of v).adjugate : Fin n → Fin n → ℂ)) :=
  Continuous.matrix_adjugate (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id
private lemma haarE (n : ℕ) :
    (volume : Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure ℂ)
  exact Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure (Fin n → ℂ))
private lemma exists_pair (n : ℕ) :
    ∃ V K : Set (Fin n → Fin n → ℂ), IsCompact V ∧ IsCompact K ∧ 0 < volume V ∧
      ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K := by
  haveI := haarE n
  have hU : IsOpen {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} :=
    isOpen_ne_fun continuous_detE continuous_const
  have h1 : (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) ∈
      {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} := by simp
  obtain ⟨V, hV, hi, hsub⟩ := exists_compact_subset hU h1
  refine ⟨V, (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
    ((Matrix.of p.2).det)⁻¹ • mulE p.1 (Matrix.of.symm (Matrix.of p.2).adjugate)) '' (V ×ˢ V),
    hV, ?_, Measure.measure_pos_of_nonempty_interior _ ⟨_, hi⟩, ?_⟩
  · refine (hV.prod hV).image_of_continuousOn ?_
    refine ContinuousOn.fun_smul ?_ ?_
    · exact (continuous_detE.comp continuous_snd).continuousOn.inv₀ fun p hp => hsub hp.2
    · exact (continuous_mulE.comp
        (continuous_fst.prodMk (continuous_adjE.comp continuous_snd))).continuousOn
  · rintro y v hv w hw rfl
    refine ⟨(mulE y v, v), ⟨hw, hv⟩, ?_⟩
    have hd : (Matrix.of v).det ≠ 0 := hsub hv
    have : mulE (mulE y v) (Matrix.of.symm (Matrix.of v).adjugate) = (Matrix.of v).det • y := by
      simp only [mulE, Equiv.apply_symm_apply, Matrix.mul_assoc, Matrix.mul_adjugate,
        Matrix.mul_smul, Matrix.mul_one]
      rfl
    simp only [this, smul_smul, inv_mul_cancel₀ hd, one_smul]
private lemma mulE_cancel {n : ℕ} {a y v w : Fin n → Fin n → ℂ} (ha : (Matrix.of a).det ≠ 0)
    (h : mulE (mulE a y) v = mulE a w) : mulE y v = w := by
  have hu : IsUnit (Matrix.of a) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit ha)
  have h' : Matrix.of a * (Matrix.of y * Matrix.of v) = Matrix.of a * Matrix.of w := by
    rw [← Matrix.mul_assoc]
    exact h
  exact hu.mul_left_cancel h'
private lemma key {n : ℕ} {G : Set (Fin n → Fin n → ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
    [SFinite μ] (hG : μ Gᶜ = 0) (hdet : ∀ a ∈ G, (Matrix.of a).det ≠ 0)
    (hvol : ∀ a ∈ G, Measure.map (mulE a) volume = volume)
    (hinv : ∀ a ∈ G, Measure.map (mulE a) μ = μ)
    {V K B D : Set (Fin n → Fin n → ℂ)} (hV : IsCompact V) (hB : IsCompact B)
    (hD : MeasurableSet D)
    (hK : ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K)
    (hBD : ∀ g ∈ B, ∀ v ∈ V, mulE g v ∈ D) :
    volume V * μ B ≤ μ K * volume D := by
  set S : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
    (fun p => (p.1, mulE p.1 p.2)) '' (B ×ˢ V) with hS
  have hSm : MeasurableSet S :=
    ((hB.prod hV).image (continuous_fst.prodMk continuous_mulE)).measurableSet
  have hae : ∀ᵐ g ∂μ, g ∈ G := hG
  have h1 : volume V * μ B ≤ (μ.prod volume) S := by
    rw [Measure.prod_apply hSm, ← lintegral_indicator_const hB.measurableSet]
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    by_cases hgB : g ∈ B
    · rw [indicator_of_mem hgB]
      have hm : MeasurableSet (Prod.mk g ⁻¹' S) := measurable_prodMk_left hSm
      calc volume V ≤ volume (mulE g ⁻¹' (Prod.mk g ⁻¹' S)) :=
            measure_mono fun v hv => ⟨(g, v), ⟨hgB, hv⟩, rfl⟩
        _ = volume (Prod.mk g ⁻¹' S) := by
            rw [← Measure.map_apply (measurable_mulE g) hm, hvol g hg]
    · rw [indicator_of_notMem hgB]
      exact zero_le
  have h2 : (μ.prod volume) S ≤ μ K * volume D := by
    rw [Measure.prod_apply_symm hSm, ← lintegral_indicator_const hD]
    refine lintegral_mono fun x => ?_
    have hm : MeasurableSet ((fun g => (g, x)) ⁻¹' S) := measurable_prodMk_right hSm
    by_cases hne : (((fun g => (g, x)) ⁻¹' S) ∩ G).Nonempty
    · obtain ⟨a, ⟨⟨a', w⟩, ⟨haB, hw⟩, he⟩, haG⟩ := hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      show μ _ ≤ _
      rw [indicator_of_mem (hBD _ haB _ hw), ← hinv _ haG,
        Measure.map_apply (measurable_mulE _) hm, hinv _ haG]
      refine measure_mono ?_
      rintro y ⟨⟨g, v⟩, ⟨-, hv⟩, he'⟩
      obtain ⟨rfl, h'⟩ := Prod.mk.inj he'
      exact hK y v hv w hw (mulE_cancel (hdet _ haG) h')
    · have : μ ((fun g => (g, x)) ⁻¹' S) = 0 :=
        measure_mono_null (fun g hg hgG => hne ⟨g, hg, hgG⟩) hG
      show μ _ ≤ _
      rw [this]
      exact zero_le
  exact h1.trans h2
end

set_option autoImplicit false
open MeasureTheory Set
namespace UpperTheory
theorem _root_.solution :
    ∀ (n : ℕ) (G : Set (Fin n → Fin n → ℂ)) (μ : MeasureTheory.Measure (Fin n → Fin n → ℂ)),
        μ Gᶜ = 0 →
        (∀ a ∈ G, ‖(Matrix.of a).det‖ = 1) →
        (∀ a ∈ G, MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume) →
        (∀ a ∈ G, MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x)) μ = μ) →
        (∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) →
        ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
          μ {g | Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ R} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2)) := by
  intro n G μ hG hdet hvol hinv hfin
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hfin K hK⟩
  haveI := haarE n
  obtain ⟨V, K, hV, hK, hpos, hVK⟩ := exists_pair n
  obtain ⟨M, hM0, hM⟩ := hV.isBounded.exists_pos_norm_le
  have hdim : Module.finrank ℝ (Fin n → Fin n → ℂ) = 2 * n ^ 2 := by
    simp [Module.finrank_pi_fintype]
    ring
  set c : ENNReal := μ K * volume (Metric.ball (0 : Fin n → Fin n → ℂ) 1) / volume V with hc
  have hcf : c ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (hfin K hK).ne measure_ball_lt_top.ne) hpos.ne'
  refine ⟨c.toReal * (n * M) ^ (2 * n ^ 2), fun R hR => ?_⟩
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hk := key (μ := μ) hG (fun a ha h => by simpa [h] using hdet a ha) hvol hinv hV
    (isCompact_closedBall (0 : Fin n → Fin n → ℂ) R)
    (D := Metric.closedBall 0 (n * M * R)) measurableSet_closedBall hVK (fun g hg v hv => by
      rw [mem_closedBall_zero_iff] at hg ⊢
      refine (norm_mulE_le g v).trans ?_
      have := hM v hv
      calc (n : ℝ) * (‖g‖ * ‖v‖) ≤ n * (R * M) := by gcongr
        _ = n * M * R := by ring)
  rw [Measure.addHaar_closedBall volume _ (by positivity), hdim] at hk
  have hsub : {g : Fin n → Fin n → ℂ | Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ R} ⊆
      Metric.closedBall 0 R := by
    intro g hg
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hR0).2 fun i => (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
    refine le_trans (Real.le_sqrt_of_sq_le ?_) hg
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (g i j) ≤ ∑ j, Complex.normSq (g i j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq (g i j))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
          Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  refine (measure_mono hsub).trans ?_
  have hVf : volume V ≠ ⊤ := hV.measure_lt_top.ne
  calc μ (Metric.closedBall 0 R) ≤ (μ K * (ENNReal.ofReal ((n * M * R) ^ (2 * n ^ 2)) *
        volume (Metric.ball (0 : Fin n → Fin n → ℂ) 1))) / volume V := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hVf), mul_comm]
        exact hk
    _ = c * ENNReal.ofReal ((n * M * R) ^ (2 * n ^ 2)) := by
        rw [hc, div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ = ENNReal.ofReal (c.toReal * (n * M) ^ (2 * n ^ 2) * R ^ (2 * n ^ 2)) := by
        rw [mul_assoc c.toReal, ← mul_pow, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hcf]
end UpperTheory
