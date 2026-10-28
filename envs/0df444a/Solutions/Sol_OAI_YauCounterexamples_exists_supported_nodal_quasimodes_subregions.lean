-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:12:21.731998+00:00
-- url     : https://prove2.me/submissions/7aebcbb2-3a2f-4a98-b805-b06808334b12

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_compact_actual_waves_subregions_supported
import Theorems.Thm_OAI_YauCounterexamples_contDiff_complexLaplaceBeltrami_self
import Theorems.Thm_OAI_YauCounterexamples_finiteWaveSuperposition_residual

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma normalWaveEquiv_single (i : Fin 3) :
    normalWaveEquiv (Pi.single i 1) = EuclideanSpace.basisFun (Fin 3) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace YauCounterexamples.SignTests

theorem swept_subset_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (s : Set (ι → ℝ)) (p : ι → ℝ) (hp : p ∈ s)
    (hs : ediam s ≠ (∞ : ℝ≥0∞)) :
    swept i d s ⊆ Icc (fun j => p j - Metric.diam s - if j = i then d else 0)
      (fun j => p j + Metric.diam s) := by
  rintro x ⟨z, hz, t, ht, rfl⟩
  have hdist : ∀ j, dist (z j) (p j) ≤ Metric.diam s :=
    (dist_pi_le_iff Metric.diam_nonneg).mp (Metric.dist_le_diam_of_mem' hs hz hp)
  constructor
  · intro j
    have hj := abs_le.mp (hdist j)
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      linarith [ht.2]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hji, ite_eq_right hji, sub_zero]
      linarith
  · intro j
    have hj := abs_le.mp (hdist j)
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.single_eq_same]
      linarith [ht.1]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hji, sub_zero]
      linarith

lemma prod_one_special {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommMonoid R] (i : ι) (a b : R) :
    (∏ j : ι, if j = i then a else b) = a * b ^ (Fintype.card ι - 1) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then a else b)
    (Finset.mem_univ i)]
  simp only [↓reduceIte]
  congr 1
  calc
    (∏ j ∈ Finset.univ.erase i, if j = i then a else b) =
        ∏ _j ∈ Finset.univ.erase i, b := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
    _ = b ^ (Fintype.card ι - 1) := by simp

lemma swept_box_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d r : ℝ) (p : ι → ℝ) :
    volume (Icc (fun j => p j - r - if j = i then d else 0) (fun j => p j + r)) =
      ENNReal.ofReal (2 * r + d) * (ENNReal.ofReal (2 * r)) ^ (Fintype.card ι - 1) := by
  rw [Real.volume_Icc_pi]
  have h (j : ι) : ENNReal.ofReal (p j + r - (p j - r - if j = i then d else 0)) =
      if j = i then ENNReal.ofReal (2 * r + d) else ENNReal.ofReal (2 * r) := by
    split_ifs <;> congr 1 <;> ring
  simp only [h]
  exact prod_one_special i _ _

theorem sweptVolume_le_of_ediam_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (s : Set (ι → ℝ))
    (hs : ediam s ≤ ENNReal.ofReal d) :
    sweptVolume i d s ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        ediam s ^ (Fintype.card ι - 1) := by
  obtain hse | ⟨p, hp⟩ := s.eq_empty_or_nonempty
  · subst s
    simp
  have hfin : ediam s ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hr : Metric.diam s ≤ d := ENNReal.toReal_le_of_le_ofReal hd.le hs
  have hr0 : 0 ≤ Metric.diam s := Metric.diam_nonneg
  have her : ENNReal.ofReal (Metric.diam s) = ediam s :=
    ENNReal.ofReal_toReal hfin
  change volume (swept i d s) ≤ _
  calc
    volume (swept i d s) ≤
        volume (Icc (fun j => p j - Metric.diam s - if j = i then d else 0)
          (fun j => p j + Metric.diam s)) :=
      measure_mono (swept_subset_box i d s p hp hfin)
    _ = ENNReal.ofReal (2 * Metric.diam s + d) *
        (ENNReal.ofReal (2 * Metric.diam s)) ^ (Fintype.card ι - 1) :=
      swept_box_volume i _ _ _
    _ ≤ ENNReal.ofReal (3 * d) *
        (ENNReal.ofReal (2 * Metric.diam s)) ^ (Fintype.card ι - 1) := by
      gcongr
      linarith
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), her, mul_pow]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

theorem sweptVolume_le_hausdorff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (s : Set (ι → ℝ)) :
    volume (swept i d s) ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) s := by
  let c : ℝ≥0∞ := 3 * ENNReal.ofReal d * 2 ^ (Fintype.card ι - 1)
  have hc : c ≠ (∞ : ℝ≥0∞) := by
    dsimp [c]
    finiteness
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have h := OuterMeasure.le_mkMetric
    (fun r : ℝ≥0∞ => c * r ^ (Fintype.card ι - 1 : ℕ)) (sweptVolume i d)
    (ENNReal.ofReal d) (ENNReal.ofReal_pos.mpr hd)
    (sweptVolume_le_of_ediam_le i d hd)
  have heq : (fun r : ℝ≥0∞ => c * r ^ (Fintype.card ι - 1 : ℕ)) =
      c • (fun r : ℝ≥0∞ => r ^ ((Fintype.card ι - 1 : ℕ) : ℝ)) := by
    ext r
    simp [ENNReal.rpow_natCast]
  rw [heq, OuterMeasure.mkMetric_smul _ hc hc0] at h
  have hs := h s
  simpa only [smul_apply, smul_eq_mul, OuterMeasure.coe_mkMetric,
    Measure.hausdorffMeasure, sweptVolume, c, OuterMeasure.coe_mk] using hs

theorem oppositeSet_subset_swept {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 ≤ d) (D P : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f P)
    (hseg : ∀ x ∈ D, ∀ t ∈ Icc 0 d, x + Pi.single i t ∈ P) :
    oppositeSet D id (fun x => x + Pi.single i d) f ⊆
      swept i d (P ∩ {z | f z = 0}) := by
  rintro x ⟨hx, hsign⟩
  let g : ℝ → ℝ := fun t => f (x + Pi.single i t)
  have hcont : ContinuousOn g (Icc 0 d) := by
    apply hf.comp (continuous_const.add (continuous_single i)).continuousOn
    exact fun t ht => hseg x hx t ht
  have hg0 : g 0 = f x := by simp [g]
  have hgd : g d = f (x + Pi.single i d) := rfl
  have hz : (0 : ℝ) ∈ g '' Icc 0 d := by
    rcases mul_neg_iff.mp hsign with h | h
    · apply intermediate_value_Icc' hd hcont
      simpa only [hg0, hgd, mem_Icc, id_eq] using And.intro h.2.le h.1.le
    · apply intermediate_value_Icc hd hcont
      simpa only [hg0, hgd, mem_Icc, id_eq] using And.intro h.1.le h.2.le
  obtain ⟨t, ht, hzero⟩ := hz
  refine ⟨x + Pi.single i t, ⟨hseg x hx t ht, hzero⟩, t, ht, ?_⟩
  simp

theorem signMass_le_hausdorff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (D P : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f P)
    (hseg : ∀ x ∈ D, ∀ t ∈ Icc 0 d, x + Pi.single i t ∈ P) :
    signMass volume D id (fun x => x + Pi.single i d) f ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) (P ∩ {z | f z = 0}) :=
  (measure_mono (oppositeSet_subset_swept i d hd.le D P f hf hseg)).trans
    (sweptVolume_le_hausdorff i d hd _)

theorem signCertificate_le_hausdorff_on_union {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (hd : ∀ p, 0 < d p)
    (hPi : ∀ p, IsOpen (P p)) (hPc : ∀ p, Convex ℝ (P p))
    (hPd : Pairwise fun p q => Disjoint (P p) (P q)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f (⋃ p, P p)) :
    signCertificate P d f ≤
      ((Fintype.card ι : ℝ≥0∞) * (3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1))) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) ((⋃ p, P p) ∩ {z | f z = 0}) := by
  let μ : Measure (ι → ℝ) := Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ)
  let c : ℝ≥0∞ := 3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)
  have hterm (p : J) (i : ι) : (ENNReal.ofReal (d p))⁻¹ *
      signMass volume {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
        id (fun x => x + Pi.single i (d p)) f ≤ c * μ (P p ∩ {z | f z = 0}) := by
    have hseg : ∀ x ∈ {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p},
        ∀ t ∈ Icc 0 (d p), x + Pi.single i t ∈ P p := by
      rintro x ⟨hx, hy⟩ t ht
      have hc := hPc p hx hy (show 0 ≤ 1 - t / d p by
        have := (div_le_one (hd p)).mpr ht.2
        linarith) (div_nonneg ht.1 (hd p).le) (by ring : 1 - t / d p + t / d p = 1)
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same]
        field_simp [ne_of_gt (hd p)]
        ring
      · simp only [Pi.single_eq_of_ne hji]
        ring
    have h := signMass_le_hausdorff i (d p) (hd p) _ (P p) f (hf.mono (subset_iUnion P p)) hseg
    have hc0 : ENNReal.ofReal (d p) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hd p))
    calc
      _ ≤ (ENNReal.ofReal (d p))⁻¹ *
          ((3 * ENNReal.ofReal (d p) * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
            μ (P p ∩ {z | f z = 0})) := mul_le_mul_right h _
      _ = _ := by
        unfold c
        rw [show 3 * ENNReal.ofReal (d p) * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1) =
          ENNReal.ofReal (d p) * (3 * 2 ^ (Fintype.card ι - 1)) by ring,
          ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  have hms (p : J) : MeasurableSet (P p ∩ {z | f z = 0}) := by
    obtain ⟨C, hC, heq⟩ := continuousOn_iff_isClosed.mp (hf.mono (subset_iUnion P p))
      {0} isClosed_singleton
    change MeasurableSet (P p ∩ f ⁻¹' {0})
    rw [inter_comm, heq]
    exact hC.measurableSet.inter (hPi p).measurableSet
  have hdis : Pairwise (fun p q => Disjoint (P p ∩ {z | f z = 0})
      (P q ∩ {z | f z = 0})) := by
    intro p q hpq
    exact (hPd hpq).mono inter_subset_left inter_subset_left
  have hsum : ∑ p, μ (P p ∩ {z | f z = 0}) ≤ μ ((⋃ p, P p) ∩ {z | f z = 0}) := by
    have heq : μ (⋃ p, P p ∩ {z | f z = 0}) = ∑ p, μ (P p ∩ {z | f z = 0}) := by
      simpa only [tsum_fintype] using measure_iUnion hdis hms
    rw [← heq]
    rw [iUnion_inter]

  calc
    signCertificate P d f ≤ ∑ p : J, ∑ _i : ι, c * μ (P p ∩ {z | f z = 0}) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun i _ => hterm p i
    _ = ((Fintype.card ι : ℝ≥0∞) * c) * ∑ p : J, μ (P p ∩ {z | f z = 0}) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hsum _

end YauCounterexamples.SignTests
end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

lemma normalWaveEquiv_axis_shift (x : Fin 3 → ℝ) (d : ℝ) (i : Fin 3) :
    normalWaveEquiv (x+Pi.single i d) =
      normalWaveEquiv x+d • EuclideanSpace.basisFun (Fin 3) ℝ i := by
  rw [map_add,←normalWaveEquiv_single]
  have he : Pi.single i d = d • Pi.single i (1:ℝ) := by
    ext j
    by_cases h : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  rw [he,map_smul]

lemma coordinateRegionMeasure_sign_le (C P : Set (Fin 3 → ℝ))
    (d : ℝ) (i : Fin 3) (hC : ∀ x ∈ C, x ∈ P ∧ x+Pi.single i d ∈ P)
    {f : NormalWaveSpace → ℝ} (hf : Continuous f) :
    coordinateRegionMeasure C {x | f x*f (x+d • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0} ≤
      SignTests.signMass volume {x | x ∈ P ∧ x+Pi.single i d ∈ P}
        id (fun x => x+Pi.single i d) (f ∘ normalWaveEquiv) := by
  have hm : MeasurableSet {x | f x*f (x+d • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0} :=
    isOpen_lt (hf.mul (hf.comp (continuous_id.add continuous_const))) continuous_const |>.measurableSet
  rw [coordinateRegionMeasure,Measure.map_apply normalWaveEquiv.continuous.measurable hm,
    Measure.restrict_apply (hm.preimage normalWaveEquiv.continuous.measurable)]
  apply measure_mono
  rintro x ⟨hx,hxC⟩
  refine ⟨hC x hxC,?_⟩
  simpa only [mem_preimage,mem_ofPred_eq,Function.comp_apply,id_eq,normalWaveEquiv_axis_shift] using hx

lemma coordinateRegionMeasure_univ (C : Set (Fin 3 → ℝ)) :
    coordinateRegionMeasure C univ = volume C := by
  rw [coordinateRegionMeasure,Measure.map_apply normalWaveEquiv.continuous.measurable MeasurableSet.univ]
  simp

lemma coordinateRegionMeasure_ae {C : Set (Fin 3 → ℝ)} (hC : MeasurableSet C)
    {P : NormalWaveSpace → Prop} (hP : ∀ x ∈ C, P (normalWaveEquiv x)) :
    ∀ᵐ y ∂coordinateRegionMeasure C, P y := by
  have h : ∀ᵐ y ∂coordinateRegionMeasure C, normalWaveEquiv.symm y ∈ C := by
    apply (ae_map_iff normalWaveEquiv.continuous.measurable.aemeasurable
      (hC.preimage normalWaveEquiv.symm.continuous.measurable)).mpr
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ae_restrict_mem hC
  filter_upwards [h] with y hy
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hP (normalWaveEquiv.symm y) hy

theorem coordinate_region_score_le_certificate {J : Type*} [Fintype J]
    (P C : J → Set (Fin 3 → ℝ)) (d : J → ℝ) (hd : ∀ a, 0 < d a)
    (hC : ∀ a, ∀ x ∈ C a, ∀ i : Fin 3, x ∈ P a ∧ x+Pi.single i (d a) ∈ P a)
    (hfin : ∀ a, IsFiniteMeasure (coordinateRegionMeasure (C a)))
    {f : NormalWaveSpace → ℝ} (hf : Continuous f) :
    ENNReal.ofReal (∑ a, (d a)⁻¹ * ∑ i : Fin 3,
      (coordinateRegionMeasure (C a)
        {x | f x*f (x+d a • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0}).toReal) ≤
      SignTests.signCertificate P d (f ∘ normalWaveEquiv) := by
  classical
  have hnon (a : J) : 0 ≤ (d a)⁻¹ * ∑ i : Fin 3,
      (coordinateRegionMeasure (C a)
        {x | f x*f (x+d a • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0}).toReal := by
    exact mul_nonneg (inv_nonneg.mpr (hd a).le) (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => hnon a)]
  apply Finset.sum_le_sum
  intro a _
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hd a).le),
    ENNReal.ofReal_inv_of_pos (hd a),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  gcongr
  exact coordinateRegionMeasure_sign_le (C a) (P a) (d a) i
    (fun x hx => hC a x hx i) hf

theorem coordinate_region_score_le_nodal {J : Type*} [Fintype J]
    (P C : J → Set (Fin 3 → ℝ)) (d : J → ℝ) (hd : ∀ a, 0 < d a)
    (hP : ∀ a, IsOpen (P a)) (hPc : ∀ a, Convex ℝ (P a))
    (hPd : Pairwise fun a b => Disjoint (P a) (P b))
    (hC : ∀ a, ∀ x ∈ C a, ∀ i : Fin 3, x ∈ P a ∧ x+Pi.single i (d a) ∈ P a)
    (hfin : ∀ a, IsFiniteMeasure (coordinateRegionMeasure (C a)))
    {f : NormalWaveSpace → ℝ} (hf : Continuous f) :
    ENNReal.ofReal (∑ a, (d a)⁻¹ * ∑ i : Fin 3,
      (coordinateRegionMeasure (C a)
        {x | f x*f (x+d a • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0}).toReal) ≤
      36 * Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | f (normalWaveEquiv x) = 0}) := by
  apply (coordinate_region_score_le_certificate P C d hd hC hfin hf).trans
  have h := SignTests.signCertificate_le_hausdorff_on_union P d hd hP hPc hPd
    (f ∘ normalWaveEquiv) (hf.comp normalWaveEquiv.continuous).continuousOn
  norm_num at h
  exact h

end YauCounterexamples

end

open Set Function MeasureTheory
open scoped ENNReal
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivCompLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

lemma contDiff_finiteWaveSuperposition {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → ℝ} {U : I → Fin 3 → E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) : ContDiff ℝ ∞ (finiteWaveSuperposition w U γ) :=
  hw.add (ContDiff.sum (fun i _ => ContDiff.sum (fun ℓ _ =>
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ)))))

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_real_complex_mul {u : E → ℂ}
    (hu : ContDiff ℝ ∞ u) (a : ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (a*u y).re) x‖ ≤
      ‖a‖*‖iteratedFDeriv ℝ j u x‖ := by
  have h : ContDiff ℝ ∞ (fun y => a*u y) := contDiff_const.mul hu
  have hh := Complex.reCLM.norm_iteratedFDeriv_comp_left h.contDiffAt (x := x) (n := j) (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have he : iteratedFDeriv ℝ j (fun y => a*u y) x = a • iteratedFDeriv ℝ j u x :=
    by simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := a) (x := x) (hu.of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt
  simpa only [Complex.reCLM_norm,one_mul,he,norm_smul,Function.comp_def,Complex.reCLM_apply] using hh

lemma norm_iteratedFDeriv_finiteWaveSum {I : Type*} [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤
      ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ := by
  classical
  have hs (i) (ℓ) : ContDiff ℝ ∞ (fun y => (γ i ℓ*U i ℓ y).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ))
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    ((ContDiff.sum (fun ℓ _ => hs i ℓ)).of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [iteratedFDeriv_fun_sum_apply (fun ℓ _ => ((hs i ℓ).of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ℓ _ =>
    norm_iteratedFDeriv_real_complex_mul (hU i ℓ) (γ i ℓ) j x))

theorem finiteWaveSum_derivative_bound {I : Type*} [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q T W : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E) (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤
      (3*Q*T)*n^(j+4)*W := by
  classical
  calc
    _ ≤ ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ :=
      norm_iteratedFDeriv_finiteWaveSum hU γ j x
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, n*(T*n^j*W) := by
      apply Finset.sum_le_sum; intro i _
      exact Finset.sum_le_sum (fun ℓ _ =>
        mul_le_mul (hγ i ℓ) (hbound i ℓ) (norm_nonneg _) hn)
    _ = (Fintype.card I : ℝ)*3*(n*(T*n^j*W)) := by simp; ring
    _ ≤ (Q*n^3)*3*(n*(T*n^j*W)) := by gcongr
    _ = _ := by rw [pow_add]; ring
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FiniteSumTsupportSubset
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
lemma finite_sum_tsupport_subset {E I : Type*} [TopologicalSpace E]
    {V : Set E} (s : Finset I) (f : I → E → ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ V) :
    tsupport (fun x => ∑ i ∈ s, f i x) ⊆ V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (tsupport_add _ _).trans (union_subset (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

lemma finiteWaveSuperposition_tsupport {E I : Type*} [TopologicalSpace E] [Fintype I]
    {O : Set E} {U : I → Fin 3 → E → ℂ}
    (hU : ∀ i ℓ, tsupport (U i ℓ) ⊆ O) (γ : I → Fin 3 → ℂ) :
    tsupport (finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ) ⊆ O := by
  classical
  have he : finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ =
      fun x => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ x).re := by
    funext x; exact zero_add _
  rw [he]
  apply finite_sum_tsupport_subset
  intro i _
  apply finite_sum_tsupport_subset
  intro ℓ _
  exact (tsupport_comp_subset (g := Complex.re) rfl (fun x => γ i ℓ*U i ℓ x)).trans
    (tsupport_mul_subset_right.trans (hU i ℓ))
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_QuarticReparameterization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples

lemma quartic_reparameterization (P : ℝ → Prop) {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ s : ℝ, N ≤ s → P (s^4)) :
    ∀ n : ℝ, N^4 ≤ n → P n := by
  intro n hn
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hn0 : 0 ≤ n := (pow_nonneg hN0 _).trans hn
  let s := Real.sqrt (Real.sqrt n)
  have hs4 : s^4 = n := by
    calc
      _ = (s^2)^2 := by ring
      _ = (Real.sqrt n)^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg n)]
      _ = n := Real.sq_sqrt hn0
  have hsN : N ≤ s := by
    have hh := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hn)
    have he : Real.sqrt (Real.sqrt (N^4)) = N := by
      rw [show N^4 = (N^2)^2 by ring,Real.sqrt_sq (sq_nonneg N),Real.sqrt_sq hN0]
    simpa only [he] using hh
  simpa only [hs4] using h s hsN
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_ExistsMetricSignQuasimodesSubregions
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

lemma finiteWaveSuperposition_compact {E I : Type*} [TopologicalSpace E] [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, HasCompactSupport (U i ℓ))
    (γ : I → Fin 3 → ℂ) : HasCompactSupport (finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ) := by
  classical
  have h (i) (ℓ) : HasCompactSupport (fun x => (γ i ℓ*U i ℓ x).re) :=
    ((hU i ℓ).mul_left (f := fun _ => γ i ℓ)).comp_left (g := Complex.re) rfl
  have hs := HasCompactSupport.finset_sum (s := (Finset.univ : Finset I))
    (fun i _ => HasCompactSupport.finset_sum (s := (Finset.univ : Finset (Fin 3))) (fun ℓ _ => h i ℓ))
  have he : finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ =
      ∑ i, ∑ ℓ, fun x => (γ i ℓ*U i ℓ x).re := by
    funext x
    simp only [finiteWaveSuperposition,zero_add,Finset.sum_apply]
  rw [he]
  exact hs

lemma norm_iteratedFDeriv_finiteWaveSum_uniform {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q R : ℝ} (hn : 0 ≤ n) (hR : 0 ≤ R)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E) (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤ 3*Q*n^4*R := by
  classical
  calc
    _ ≤ ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ :=
      norm_iteratedFDeriv_finiteWaveSum hU γ j x
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, n*R := by
      apply Finset.sum_le_sum; intro i _
      exact Finset.sum_le_sum (fun ℓ _ => mul_le_mul (hγ i ℓ) (hbound i ℓ) (norm_nonneg _) hn)
    _ = (Fintype.card I : ℝ)*3*(n*R) := by simp; ring
    _ ≤ (Q*n^3)*3*(n*R) := by gcongr
    _ = _ := by ring

end


open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_metric_sign_quasimodes_subregions_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ J : Set NormalWaveSpace, J ⊆ K →
        (∀ y ∈ J, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ J ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ J)) →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | (w+u) x *
              (w+u) (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_waves_subregions_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m (D+4) T₀ H hT₀ hH
  have hN1 : 1 ≤ N := by linarith
  refine ⟨c₀,hc₀,3*Q*T,by positivity,N^4,one_le_pow₀ hN1,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (one_le_pow₀ hN1 : 1 ≤ N^4).trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  obtain ⟨s,hs,hs4⟩ := quartic_reparameterization
    (fun x => ∃ s : ℝ, N ≤ s ∧ s^4 = x) hN1 (fun s hs => ⟨s,hs,rfl⟩) n hn
  have hh := hdata s hs
  dsimp only at hh
  rw [hs4] at hh
  obtain ⟨t,p,U,hSupport,ht,hU,hgood⟩ := hh
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog J hJK hb P _ ℓ q hq ν hν hv hregion
  obtain ⟨γ,hcoef,hjet,hscore⟩ := hgood S hS E hES hEK w hw W hW hW0 hWlower hWupper
    hwbound hlog J hJK hb P ℓ q hq ν hν hv hregion
  let u := finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ
  have hu : ContDiff ℝ ∞ u := contDiff_finiteWaveSuperposition contDiff_const (fun i j => (hU i j).1) γ
  have he : w+u = finiteWaveSuperposition w U γ := by
    funext x
    change w x + (0+_) = w x + _
    rw [zero_add]
  have he' : (w+u) ∘ normalWaveEquiv =
      finiteWaveSuperposition (w ∘ normalWaveEquiv) (fun i j => U i j ∘ normalWaveEquiv) γ := by
    rw [he]; rfl
  refine ⟨u,hu,finiteWaveSuperposition_compact (fun i j => (hU i j).2.1) γ,
    finiteWaveSuperposition_tsupport hSupport γ,?_,?_,?_⟩
  · intro x j hj
    have hcard : (Fintype.card t : ℝ) ≤ Q*n^3 := by simpa using ht
    have hj' : j ≤ max m 2 := hj.trans (le_max_left _ _)
    constructor
    · have hbound (i) (ℓ) : ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*Real.exp (n*φ x) := by
        apply ((hU i ℓ).2.2.2 x j hj').1.trans
        apply mul_le_of_le_one_right (by positivity)
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hn0.le) (sq_nonneg _)
      have hsum := finiteWaveSum_derivative_bound (fun i ℓ => (hU i ℓ).1) γ hn0.le hT.le
        (Real.exp_pos _).le hcard hcoef j x hbound
      have he₀ : u = fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re := by
        funext y; exact zero_add _
      rw [he₀]
      exact hsum
    · rw [finiteWaveSuperposition_residual g (fun i ℓ => (hU i ℓ).1) γ (n*(n+2))]
      let R : t → Fin 3 → NormalWaveSpace → ℂ := fun i ℓ y =>
        complexLaplaceBeltrami g (U i ℓ) y+(n : ℂ)*((n : ℂ)+2)*U i ℓ y
      have hR (i) (ℓ) : ContDiff ℝ ∞ (R i ℓ) :=
        (contDiff_complexLaplaceBeltrami_self g (hU i ℓ).1).add (contDiff_const.mul (hU i ℓ).1)
      have hb := norm_iteratedFDeriv_finiteWaveSum_uniform hR γ hn0.le
        (show 0 ≤ T*(n^((D+4)+1))⁻¹*Real.exp (n*φ x) by positivity)
        hcard hcoef j x (fun i ℓ => ((hU i ℓ).2.2.2 x j hj').2)
      simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat] at *
      apply hb.trans_eq
      simp only [show D+4+1 = (D+1)+4 by omega,pow_add]
      field_simp
  · rw [he']; exact hjet
  · rw [he]; exact hscore


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExistsSupportedBoxNodalQuasimodes
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_supported_nodal_quasimodes_subregions_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ R : Set NormalWaveSpace, R ⊆ K →
        (∀ y ∈ R, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (J : Type) [Fintype J] (P Cₛ : J → Set (Fin 3 → ℝ)) (ℓ : J → ℝ),
        (∀ a, 0 < ℓ a) → (∀ a, IsOpen (P a)) → (∀ a, Convex ℝ (P a)) →
        (Pairwise fun a b => Disjoint (P a) (P b)) →
        (∀ a, MeasurableSet (Cₛ a)) → (∀ a, IsFiniteMeasure (volume.restrict (Cₛ a))) →
        (∀ a, normalWaveEquiv '' P a ⊆ R) →
        (∀ a, ∀ x ∈ Cₛ a, x ∈ P a ∧
          profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
          ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a)) ∈ P a) →
        0 < ∑ a, ℓ a*(volume (Cₛ a)).toReal →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            SignTests.signCertificate P (fun a => ε/(n*ℓ a)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            36*Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_metric_sign_quasimodes_subregions_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,C,hC,N,hN,?_⟩
  intro n hn S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog R hRK hb
    J _ P Cₛ ℓ hℓ hP hPc hPd hCₛ hfin hPK hregion hmass
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans hn)
  let d : J → ℝ := fun a => ε/(n*ℓ a)
  let ν : J → Measure NormalWaveSpace := fun a => coordinateRegionMeasure (Cₛ a)
  have hd : ∀ a, 0 < d a := fun a => div_pos hε (mul_pos hn0 (hℓ a))
  have hν : ∀ a, IsFiniteMeasure (ν a) := fun a => coordinateRegionMeasure_finite (Cₛ a)
  have htotal : (∑ a, (d a)⁻¹*(ν a univ).toReal) =
      (n/ε)*(∑ a, ℓ a*(volume (Cₛ a)).toReal) := by
    simp only [ν,coordinateRegionMeasure_univ,d,inv_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; ring
  have hpos : 0 < ∑ a, (d a)⁻¹*(ν a univ).toReal := by
    rw [htotal]; exact mul_pos (div_pos hn0 hε) hmass
  have hreg (a : J) : ∀ᵐ y ∂ν a, y ∈ R ∧ profileFrequencyScale g φ y ≤ ℓ a ∧
      ℓ a ≤ 2*profileFrequencyScale g φ y ∧
      ∀ j, packetAxisShift y n ε (ℓ a) j ∈ R := by
    apply coordinateRegionMeasure_ae (hCₛ a)
    intro x hx
    have hr := hregion a x hx
    refine ⟨hPK a ⟨x,hr.1,rfl⟩,hr.2.1,hr.2.2.1,?_⟩
    intro j
    have hh := hPK a ⟨x+Pi.single j (ε/(n*ℓ a)),hr.2.2.2 j,rfl⟩
    simpa only [normalWaveEquiv_axis_shift,packetAxisShift] using hh
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore⟩ := hdata n hn S hS E hES hEK w hw W hW hW0
    hWlower hWupper hwbound hlog R hRK hb J ℓ (fun a => (d a)⁻¹)
    (fun a => (inv_pos.mpr (hd a)).le) ν hν hpos hreg
  have hcore (a : J) (x) (hx : x ∈ Cₛ a) (j : Fin 3) :
      x ∈ P a ∧ x+Pi.single j (d a) ∈ P a :=
    ⟨(hregion a x hx).1,(hregion a x hx).2.2.2 j⟩
  have hsc := coordinate_region_score_le_certificate P Cₛ d hd hcore hν (hw.continuous.add hu.continuous)
  have hnod := coordinate_region_score_le_nodal P Cₛ d hd hP hPc hPd hcore hν (hw.continuous.add hu.continuous)
  have he : (p₀/2)*(∑ a, (d a)⁻¹*(ν a univ).toReal) =
      (p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal) := by rw [htotal]; ring
  rw [he] at hscore
  have hlt := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity :
    0 ≤ (p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal))).mpr hscore
  exact ⟨u,hu,huc,hus,hder,hjet,hlt.trans_le hsc,hlt.trans_le hnod⟩

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
open BoxIntegral


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions_oai := @OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions_oai
