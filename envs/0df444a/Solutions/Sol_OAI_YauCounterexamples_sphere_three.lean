-- Prove2me | solution 1 for OAI.YauCounterexamples.sphere_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:43:47.24826+00:00
-- url     : https://prove2.me/submissions/3851dcfd-3a16-4057-8cdc-c1bd424c1586

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_fixed_witnesses
import Theorems.Thm_OAI_YauCounterexamples_nodalMeasure_coordinates_lower_bound

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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

open Set Function MeasureTheory
open scoped ENNReal
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_InverseChartIntrinsicLipschitz
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma inverse_chart_intrinsic_lipschitz (p : M) :
    ∃ r > (0 : ℝ), ∃ C : ℝ≥0, 0 < C ∧
      ball (extChartAt 𝓘(ℝ,E) p p) r ⊆ (extChartAt 𝓘(ℝ,E) p).target ∧
      ∀ y ∈ ball (extChartAt 𝓘(ℝ,E) p p) r, ∀ z ∈ ball (extChartAt 𝓘(ℝ,E) p p) r,
        riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm y) ((extChartAt 𝓘(ℝ,E) p).symm z)
          ≤ C * edist y z := by
  let c := extChartAt 𝓘(ℝ,E) p
  let d (y : E) : E →L[ℝ] TangentSpace 𝓘(ℝ,E) (c.symm y) :=
    mfderiv[Set.range 𝓘(ℝ,E)] c.symm y
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝓘(ℝ,E) p
  obtain ⟨r,hr,hrsub'⟩ : ∃ r > 0, ball (c p) r ∩ range 𝓘(ℝ,E) ⊆
      c.target ∩ {y | ‖d y‖ₑ < C} :=
    mem_nhdsWithin_iff.mp (inter_mem (extChartAt_target_mem_nhdsWithin p) hC)
  have hrsub : ball (c p) r ⊆ c.target ∩ {y | ‖d y‖ₑ < C} := by
    simpa using hrsub'
  refine ⟨r,hr,C,hCpos,fun y hy => (hrsub hy).1,?_⟩
  intro y hy z hz
  let η := ContinuousAffineMap.lineMap (R := ℝ) y z
  let γ := c.symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' (c.target ∩ {w | ‖d w‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap, η]
    exact ((convex_ball _ _).segment_subset hy hz).trans hrsub
  simp only [preimage_inter, subset_inter_iff] at hη
  have hηs : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hdist : riemannianEDist 𝓘(ℝ,E) (c.symm y) (c.symm z) ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηs hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hc : mfderiv[Icc 0 1] γ t =
      (mfderiv[Set.range 𝓘(ℝ,E)] c.symm (η t)).comp (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact hηs.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range p))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hcv : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[Set.range 𝓘(ℝ,E)] c.symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($hc 1)
  rw [hcv]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_CompactRegularLevelIntrinsicFinite
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



section
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [EMetricSpace N] [MeasurableSpace N] [BorelSpace N]

theorem regular_level_local_finite {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hd : fderiv ℝ f x ≠ 0)
    {φ : E → N} {B : Set E} (hB : B ∈ 𝓝 x) {C : ℝ≥0}
    (hφ : LipschitzOnWith C φ B) :
    ∃ O ∈ 𝓝 x, Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ)
      (φ '' {y | y ∈ O ∧ f y = f x}) < (∞ : ℝ≥0∞) := by
  let L := fderiv ℝ f x
  have hL : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := L.toLinearMap) (by simp)
    intro hh
    apply hd
    ext y
    exact DFunLike.congr_fun hh y
  have hs : HasStrictFDerivAt f L x := hf.hasStrictFDerivAt one_ne_zero
  let e := hs.implicitToOpenPartialHomeomorph f L hL
  let g := hs.implicitFunction f L hL (f x)
  have hdx : HasStrictFDerivAt g L.ker.subtypeL 0 := hs.to_implicitFunction hL
  have hg0 : g 0 = x := hs.implicitFunction_apply_image hL
  obtain ⟨K,V,hV,hgV⟩ := hdx.exists_lipschitzOnWith
  have hN : V ∩ g ⁻¹' B ∈ 𝓝 (0 : L.ker) :=
    inter_mem hV (hdx.continuousAt.tendsto (hg0 ▸ hB))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hN
  let S := ball (0 : L.ker) r
  have hSg : MapsTo g S B := fun y hy => (hrsub hy).2
  have hgS : LipschitzOnWith K g S := hgV.mono (fun y hy => (hrsub hy).1)
  have he : x ∈ e.source := hs.mem_implicitToOpenPartialHomeomorph_source hL
  have he0 : e x = (f x,0) := hs.implicitToOpenPartialHomeomorph_self hL
  have hpre : e ⁻¹' (Set.univ ×ˢ S) ∈ 𝓝 x := by
    apply (e.continuousAt he).tendsto
    rw [he0]
    exact IsOpen.mem_nhds (isOpen_univ.prod isOpen_ball) ⟨mem_univ _,mem_ball_self hr⟩
  let O := e.source ∩ e ⁻¹' (Set.univ ×ˢ S)
  have hO : O ∈ 𝓝 x := inter_mem (e.open_source.mem_nhds he) hpre
  refine ⟨O,hO,?_⟩
  have hsub : φ '' {y | y ∈ O ∧ f y = f x} ⊆ (φ ∘ g) '' S := by
    rintro _ ⟨y,hy,rfl⟩
    refine ⟨(e y).2,hy.1.2.2,?_⟩
    change φ (g (e y).2) = φ y
    congr 1
    change e.symm (f x,(e y).2) = y
    rw [← hy.2]
    change e.symm (e y) = y
    exact e.left_inv hy.1.1
  have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ E - 1 := by
    have hh := LinearMap.finrank_range_add_finrank_ker L.toLinearMap
    rw [hL] at hh
    simp only [finrank_top, Module.finrank_self] at hh
    omega
  let : MeasurableSpace L.ker := borel L.ker
  let : BorelSpace L.ker := ⟨rfl⟩
  have hfinite : Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ) S < (∞ : ℝ≥0∞) := by
    rw [← hdim]
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : L.ker) r).measure_lt_top
  apply lt_of_le_of_lt (measure_mono hsub)
  apply lt_of_le_of_lt ((hφ.comp hgS hSg).hausdorffMeasure_image_le (by positivity))
  rw [ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfinite

end



open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [EMetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] [MeasurableSpace M] [BorelSpace M]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

theorem compact_regular_level_intrinsic_finite {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {K : Set M} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, u x = 0 →
      fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0) :
    Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ) (K ∩ {x | u x = 0}) < (∞ : ℝ≥0∞) := by
  let Z := K ∩ {x | u x = 0}
  have hZ : IsCompact Z := hK.inter_right (isClosed_eq hu.continuous continuous_const)
  apply hZ.measure_lt_top_of_nhdsWithin
  intro x hx
  let c := chartAt E x
  have hxs : x ∈ c.source := mem_chart_source E x
  have hxt : c x ∈ c.target := c.map_source hxs
  have hcU : ContDiffAt ℝ 1 (u ∘ c.symm) (c x) := by
    apply (contMDiffAt_iff_contDiffAt.mp ((hu (c.symm (c x))).comp (c x)
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hxt))).of_le
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 1
  obtain ⟨r,hr,C,_,_,hCL⟩ := inverse_chart_intrinsic_lipschitz (E := E) x
  have hCL' : LipschitzOnWith C c.symm (ball (c x) r) := by
    intro y hy z hz
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ,E))]
    exact hCL y hy z hz
  obtain ⟨O,hO,hfin⟩ := regular_level_local_finite hcU (hreg x hx.1 hx.2)
    (ball_mem_nhds (c x) hr) hCL'
  let V := c.source ∩ c ⁻¹' O
  have hV : V ∈ 𝓝 x := inter_mem (c.open_source.mem_nhds hxs) ((c.continuousAt hxs).tendsto hO)
  refine ⟨V ∩ Z, by simpa only [inter_comm] using inter_mem_nhdsWithin Z hV, ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) hfin
  intro y hy
  refine ⟨c y,⟨hy.1.2,?_⟩,c.left_inv hy.1.1⟩
  simp only [Function.comp_apply, c.left_inv hy.1.1, c.left_inv hxs]
  exact hy.2.2.trans hx.2.symm


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_SphericalNodalFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma spherical_nodal_finite (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (u : Sphere 3 → ℝ) (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u)
    (hreg : SphericalRegular u) : nodalMeasure g 2 u ≠ (∞ : ℝ≥0∞) := by
  let : RiemannianBundle (fun x : Sphere 3 => TangentSpace 𝓘(ℝ,Euclidean 3) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (Euclidean 3) (fun x : Sphere 3 => TangentSpace 𝓘(ℝ,Euclidean 3) x) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (Sphere 3) := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,Euclidean 3) (Sphere 3)
  let : MeasurableSpace (Sphere 3) := borel (Sphere 3)
  let : BorelSpace (Sphere 3) := ⟨rfl⟩
  have hh := compact_regular_level_intrinsic_finite hu (K:=univ) isCompact_univ (fun x _ => hreg x)
  change Measure.hausdorffMeasure 2 {x | u x=0}≠(∞ : ℝ≥0∞)
  apply ne_of_lt
  simpa [Euclidean] using hh

lemma spherical_signCertificate_bound (g : SmoothMetric (Euclidean 3) (Sphere 3)) :
    ∃ D : ℝ≥0, 0<D ∧ ∀ (u : Sphere 3 → ℝ),
      Continuous u → ∀ (partition : TaggedPrepartition sourceSignBox)
      (d : {J : Box (Fin 3) // J∈partition.boxes} → ℝ), (∀ j, 0<d j) →
      SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) ≤
          (D:ℝ≥0∞)*nodalMeasure g 2 u := by
  classical
  let K : Set (Euclidean 3) := normalWaveEquiv '' Box.Icc sourceSignBox
  have hK : IsCompact K := sourceSignBox.isCompact_Icc.image normalWaveEquiv.continuous
  obtain ⟨C,hC,hCbound⟩ := nodalMeasure_coordinates_lower_bound g sourcePole hK
    (by rw [sphere_chart_target]; exact subset_univ _)
  let L : ℝ≥0 := max ‖normalWaveEquiv.symm.toContinuousLinearMap‖₊ 1
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlip : LipschitzWith L normalWaveEquiv.symm :=
    normalWaveEquiv.symm.toContinuousLinearMap.lipschitz.weaken (le_max_left _ _)
  refine ⟨36*L^2*(C:ℝ≥0)^2,by positivity,?_⟩
  intro u hu partition d hd
  let f := ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)
  have hf : Continuous f := hu.comp ((sphere_chart_symm_continuous sourcePole).comp normalWaveEquiv.continuous)
  let Z := (⋃ j : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo j.val) ∩ {z | f z=0}
  have hsign : SignTests.signCertificate (fun j => Box.Ioo j.val) d f ≤
      36*Measure.hausdorffMeasure 2 Z := by
    have hh := SignTests.signCertificate_le_hausdorff_on_union
      (fun j : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo j.val) d hd
      (fun j => isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo))
      (fun j => convex_pi (fun i _ => convex_Ioo _ _))
      (fun j k hjk => (partition.toPrepartition.disjoint_coe_of_mem j.property k.property
        (fun hh => hjk (Subtype.ext hh))).mono j.val.Ioo_subset_coe k.val.Ioo_subset_coe)
      f hf.continuousOn
    norm_num [Z] at hh ⊢
    exact hh
  have hZsub : Z ⊆ normalWaveEquiv.symm '' (K ∩ {y | u ((chartAt (Euclidean 3) sourcePole).symm y)=0}) := by
    rintro x ⟨hx,hfx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    refine ⟨normalWaveEquiv x,⟨⟨x,?_,rfl⟩,hfx⟩,normalWaveEquiv.symm_apply_apply x⟩
    exact Box.coe_subset_Icc (partition.toPrepartition.le_of_mem j.property (j.val.Ioo_subset_coe hj))
  have hmeasure : Measure.hausdorffMeasure 2 Z ≤ (L:ℝ≥0∞)^2*(C:ℝ≥0∞)^2*nodalMeasure g 2 u := by
    calc
      _ ≤ Measure.hausdorffMeasure 2 (normalWaveEquiv.symm ''
        (K ∩ {y | u ((chartAt (Euclidean 3) sourcePole).symm y)=0})) := measure_mono hZsub
      _ ≤ (L:ℝ≥0∞)^(2:ℝ)*Measure.hausdorffMeasure 2
        (K ∩ {y | u ((chartAt (Euclidean 3) sourcePole).symm y)=0}) :=
          hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2) _
      _ ≤ (L:ℝ≥0∞)^(2:ℝ)*((C:ℝ≥0∞)^(2:ℝ)*nodalMeasure g 2 u) :=
          mul_le_mul' le_rfl (hCbound u 2 (by norm_num))
      _ = _ := by rw [ENNReal.rpow_two,ENNReal.rpow_two,mul_assoc]
  apply hsign.trans
  calc
    _ ≤ 36*((L:ℝ≥0∞)^2*(C:ℝ≥0∞)^2*nodalMeasure g 2 u) := mul_le_mul' le_rfl hmeasure
    _ = _ := by simp only [ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_ofNat]; ring

lemma spherical_sign_nodal_real (g : SmoothMetric (Euclidean 3) (Sphere 3)) :
    ∃ D : ℝ, 0<D ∧ ∀ (u : Sphere 3 → ℝ),
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u → SphericalRegular u →
      ∀ L : ℝ, 0≤L → SphericalSignAbove u L → L < D*(nodalMeasure g 2 u).toReal := by
  obtain ⟨D,hD,hbound⟩ := spherical_signCertificate_bound g
  refine ⟨D,hD,?_⟩
  intro u hu hr L hL hs
  obtain ⟨partition,_,d,hd,hscore⟩ := hs
  have hh := hscore.trans_le (hbound u hu.continuous partition d hd)
  have hfin := spherical_nodal_finite g u hu hr
  have hr := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).mpr hh
  simpa only [ENNReal.toReal_ofReal hL,ENNReal.toReal_mul,ENNReal.coe_toReal] using hr

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalWitnessesUnbounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
namespace YauCounterexamples

theorem spherical_witnesses_unbounded (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (h : ∀ n : ℕ, SphericalLargeWitness g ((n:ℝ)+1) ((n:ℝ)+1)) :
    HasUnboundedNodalRatio g 3 := by
  classical
  choose k hk e u heB heD hu hu0 hue hreg hscore using h
  have hepos (n : ℕ) : 0<e n := lt_of_lt_of_le (by positivity : (0:ℝ)<(n:ℝ)+1) (heB n).le
  have hfin (n : ℕ) : nodalMeasure g 2 (u n) ≠ (∞ : ℝ≥0∞) := spherical_nodal_finite g (u n) (hu n) (hreg n)
  obtain ⟨D,hD,hbound⟩ := spherical_sign_nodal_real g
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have heratio (n : ℕ) : ((n:ℝ)+1)/(2*D) ≤ (nodalMeasure g 2 (u n)).toReal / Real.sqrt (e n) := by
    have hkpos : (0:ℝ)<k n := by exact_mod_cast (show 0<k n by have := hk n; omega)
    have hnp : (0:ℝ)≤(n:ℝ)+1 := by positivity
    have hscore' := hbound (u n) (hu n) (hreg n) (((n:ℝ)+1)*(k n:ℝ)) (mul_nonneg hnp hkpos.le) (hscore n)
    have hsqrtpos := Real.sqrt_pos.mpr (hepos n)
    have hsq := Real.sq_sqrt (hepos n).le
    have hsqrt : Real.sqrt (e n) ≤ 2*(k n:ℝ) := by
      have := heD n
      nlinarith
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*D) hsqrtpos).mpr
    have hh := mul_le_mul_of_nonneg_left hsqrt hnp
    nlinarith
  refine ⟨u,e,?_,?_,?_⟩
  · intro n
    exact ⟨hu n,hu0 n,hepos n,hue n,hfin n⟩
  · exact tendsto_atTop_mono (fun n => (heB n).le) hbase
  · exact tendsto_atTop_mono heratio (hbase.atTop_div_const (by positivity : (0:ℝ)<2*D))
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

theorem sphere_three_oai (gRound : SmoothMetric (Euclidean 3) (Sphere 3))
    (hRound : IsRound gRound) :
    ∀ N : Set (SmoothMetric (Euclidean 3) (Sphere 3)),
      IsSmoothNeighborhood gRound N →
      ∃ g ∈ N, HasUnboundedNodalRatio g 3 := by
  intro N hN
  obtain ⟨g,hgN,hg⟩ := exists_spherical_fixed_witnesses gRound hRound N hN
  exact ⟨g,hgN,spherical_witnesses_unbounded g hg⟩
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.sphere_three_oai := @OAI.YauCounterexamples.sphere_three_oai
