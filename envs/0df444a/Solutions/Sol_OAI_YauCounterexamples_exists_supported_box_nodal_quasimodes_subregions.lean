-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:11:58.402261+00:00
-- url     : https://prove2.me/submissions/b7b4dedc-415f-4109-b72d-7b507df82c8f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_supported_nodal_quasimodes_subregions

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_MiddleBox
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology
namespace YauCounterexamples

lemma middleBox_Icc_subset (I : Box (Fin 3)) : Box.Icc (middleBox I) ⊆ Box.Ioo I := by
  intro x hx i _
  have hlo := hx.1 i
  have hup := hx.2 i
  change (3*I.lower i+I.upper i)/4 ≤ x i at hlo
  change x i ≤ (I.lower i+3*I.upper i)/4 at hup
  constructor <;> linarith [I.lower_lt_upper i]

lemma middleBox_volume (I : Box (Fin 3)) :
    (volume (Box.Icc (middleBox I))).toReal = (volume (Box.Ioo I)).toReal/8 := by
  rw [←measure_congr (middleBox I).coe_ae_eq_Icc,
    ←measure_congr (I.coe_ae_eq_Icc.trans I.Ioo_ae_eq_Icc.symm)]
  simp only [Box.volume_apply']
  simp only [middleBox]
  rw [Fin.prod_univ_three,Fin.prod_univ_three]
  ring

lemma middleBox_shift_mem (I : Box (Fin 3)) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : ∀ i, d < (I.upper i-I.lower i)/4)
    {x : Fin 3 → ℝ} (hx : x ∈ Box.Icc (middleBox I)) (j : Fin 3) :
    x+Pi.single j d ∈ Box.Ioo I := by
  intro i _
  have hxi := middleBox_Icc_subset I hx i trivial
  have hu := hx.2 i
  change x i ≤ (I.lower i+3*I.upper i)/4 at hu
  by_cases hij : i=j
  · subst i
    simp only [Pi.add_apply,Pi.single_eq_same]
    constructor <;> linarith [hsmall j,hxi.1]
  · simpa only [Pi.add_apply,Pi.single_eq_of_ne hij,add_zero] using hxi

lemma middleBox_eventually_shift_mem (I : Box (Fin 3)) {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) :
    ∀ᶠ n : ℝ in atTop, ∀ x ∈ Box.Icc (middleBox I), ∀ j : Fin 3,
      x+Pi.single j (ε/(n*ℓ)) ∈ Box.Ioo I := by
  have hd : Tendsto (fun n : ℝ => ε/(n*ℓ)) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds (x := ε)).mul (tendsto_inv_atTop_zero.mul_const (ℓ⁻¹))
    simpa only [mul_zero,zero_mul,div_eq_mul_inv,mul_inv_rev,mul_comm (ℓ⁻¹)] using ht
  have he : ∀ᶠ n : ℝ in atTop, ∀ j : Fin 3, ε/(n*ℓ) < (I.upper j-I.lower j)/4 := by
    rw [Filter.eventually_all]
    intro j
    exact (tendsto_order.mp hd).2 _ (by linarith [I.lower_lt_upper j])
  filter_upwards [he,eventually_ge_atTop (1:ℝ)] with n hn hn1
  intro x hx j
  exact middleBox_shift_mem I (div_nonneg hε.le (mul_nonneg (by linarith) hℓ.le)) hn hx j

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_BoxProfileIntegralPos
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology

theorem exists_profile_box_partition (I : Box (Fin 3)) (L : (Fin 3 → ℝ) → ℝ)
    (hL : ContinuousOn L (Box.Icc I)) (hpos : ∀ x ∈ Box.Icc I, 0 < L x) :
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧
      ∃ ℓ : Box (Fin 3) → ℝ, ∀ J ∈ partition, 0 < ℓ J ∧
        ∀ x ∈ Box.Icc J, ℓ J/2 ≤ L x ∧ L x ≤ ℓ J := by
  classical
  have hr : ∀ x, ∃ r > (0:ℝ), ∀ y ∈ Box.Icc I,
      dist y x ≤ r → x ∈ Box.Icc I → |L y-L x| < L x/3 := by
    intro x
    by_cases hx : x ∈ Box.Icc I
    · obtain ⟨δ,hδ,hδprop⟩ := Metric.continuousWithinAt_iff.mp (hL x hx) (L x/3) (div_pos (hpos x hx) (by norm_num))
      refine ⟨δ/2,by positivity,?_⟩
      intro y hy hyδ _
      have := hδprop hy (lt_of_le_of_lt hyδ (by linarith))
      simpa only [Real.dist_eq] using this
    · exact ⟨1,by norm_num,fun _ _ _ h => (hx h).elim⟩
  choose r hr0 hr using hr
  obtain ⟨partition,hπ,hHen,hsub,-,-⟩ :=
    I.exists_taggedPartition_isHenstock_isSubordinate_homothetic (fun x => ⟨r x,hr0 x⟩)
  refine ⟨partition,hπ,fun J => (4/3:ℝ)*L (partition.tag J),?_⟩
  intro J hJ
  have ht := partition.tag_mem_Icc J
  refine ⟨mul_pos (by norm_num) (hpos _ ht),?_⟩
  intro x hx
  have hxi : x ∈ Box.Icc I := (Box.le_iff_Icc.mp (partition.le_of_mem hJ)) hx
  have hab := hr (partition.tag J) x hxi (hsub J hJ hx) ht
  have hh := abs_lt.mp hab
  constructor <;> linarith

theorem profile_integral_le_partition (I : Box (Fin 3))
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContinuousOn L (Box.Icc I))
    (partition : TaggedPrepartition I) (hπ : partition.IsPartition) (ℓ : Box (Fin 3) → ℝ)
    (hbound : ∀ J ∈ partition, ∀ x ∈ Box.Icc J, L x ≤ ℓ J) :
    (∫ x in Box.Icc I, L x) ≤ ∑ J ∈ partition.boxes, ℓ J*(volume (Box.Ioo J)).toReal := by
  have hi : IntegrableOn L (Box.Icc I) := hL.integrableOn_compact I.isCompact_Icc
  have hpart : (∫ x in Box.Icc I, L x) = ∑ J ∈ partition.boxes, ∫ x in (J : Set (Fin 3 → ℝ)), L x := by
    calc
      (∫ x in Box.Icc I, L x) = ∫ x in (I : Set (Fin 3 → ℝ)), L x :=
        setIntegral_congr_set I.coe_ae_eq_Icc.symm
      _ = ∫ x in partition.toPrepartition.iUnion, L x := by rw [hπ.iUnion_eq]
      _ = _ := integral_biUnion_finset partition.boxes (fun J _ => J.measurableSet_coe)
        partition.pairwiseDisjoint (fun J hJ => hi.mono_set (fun x hx => Box.coe_subset_Icc (partition.le_of_mem hJ hx)))
  rw [hpart]
  refine Finset.sum_le_sum fun J hJ => ?_
  have hJI : (J : Set (Fin 3 → ℝ)) ⊆ Box.Icc I :=
    fun x hx => Box.coe_subset_Icc (partition.le_of_mem hJ hx)
  calc
    (∫ x in (J : Set (Fin 3 → ℝ)), L x) ≤ ∫ _ in (J : Set (Fin 3 → ℝ)), ℓ J := by
      apply setIntegral_mono_on (hi.mono_set hJI) (integrableOn_const (J.measure_coe_lt_top volume).ne) J.measurableSet_coe
      exact fun x hx => hbound J hJ x (Box.coe_subset_Icc hx)
    _ = ℓ J*(volume (Box.Ioo J)).toReal := by
      rw [MeasureTheory.integral_const]
      have he : volume (J : Set (Fin 3 → ℝ)) = volume (Box.Ioo J) :=
        measure_congr (J.coe_ae_eq_Icc.trans J.Ioo_ae_eq_Icc.symm)
      simp [measureReal_def,he,smul_eq_mul,mul_comm]

end

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology

lemma box_profile_integral_pos (I : Box (Fin 3)) (L : (Fin 3 → ℝ) → ℝ)
    (hL : ContinuousOn L (Box.Icc I)) (hL1 : ∀ x ∈ Box.Icc I, 1 ≤ L x) :
    0 < ∫ x in Box.Icc I, L x := by
  have hv : 0 < (volume (Box.Icc I)).toReal := by
    rw [←measure_congr I.coe_ae_eq_Icc,Box.volume_apply']
    exact Finset.prod_pos (fun i _ => sub_pos.mpr (I.lower_lt_upper i))
  have hi := setIntegral_mono_on (integrableOn_const (I.measure_Icc_lt_top volume).ne)
    (hL.integrableOn_compact I.isCompact_Icc) I.measurableSet_Icc hL1
  have he : (∫ _ in Box.Icc I, (1:ℝ)) = (volume (Box.Icc I)).toReal := by simp [measureReal_def]
  rw [he] at hi
  exact hv.trans_le hi

lemma middleBox_partition_mass (I : Box (Fin 3)) (L : (Fin 3 → ℝ) → ℝ)
    (hL : ContinuousOn L (Box.Icc I)) (partition : TaggedPrepartition I)
    (hπ : partition.IsPartition) (ℓ : Box (Fin 3) → ℝ)
    (hbound : ∀ J ∈ partition, ∀ x ∈ Box.Icc J, L x ≤ ℓ J) :
    (∫ x in Box.Icc I, L x)/8 ≤
      ∑ J : {J : Box (Fin 3) // J ∈ partition.boxes}, ℓ J.val*(volume (Box.Icc (middleBox J.val))).toReal := by
  classical
  simp_rw [middleBox_volume,←mul_div_assoc]
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [Finset.sum_coe_sort partition.boxes (fun J => ℓ J*(volume (Box.Ioo J)).toReal)]
  exact profile_integral_le_partition I L hL partition hπ ℓ hbound

lemma box_Ioo_open (I : Box (Fin 3)) : IsOpen (Box.Ioo I) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

lemma box_Ioo_convex (I : Box (Fin 3)) : Convex ℝ (Box.Ioo I) :=
  convex_pi (fun _ _ => convex_Ioo _ _)

lemma partition_Ioo_disjoint (I : Box (Fin 3)) (partition : TaggedPrepartition I) :
    Pairwise fun A B : {J : Box (Fin 3) // J ∈ partition.boxes} => Disjoint (Box.Ioo A.val) (Box.Ioo B.val) := by
  intro A B hAB
  exact (partition.disjoint_coe_of_mem A.property B.property (fun h => hAB (Subtype.ext h))).mono A.val.Ioo_subset_coe B.val.Ioo_subset_coe

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProfileFrequencyEnergy
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma profileFrequencyEnergy_ge_one (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    1 ≤ profileFrequencyEnergy g φ x := by
  unfold profileFrequencyEnergy
  by_cases h : coordinateMetricGradient g φ x = 0
  · simp [h]
  · linarith [selfMetricFlat_pos g x h]

lemma profileFrequencyScale_sq (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    profileFrequencyScale g φ x ^ 2 = profileFrequencyEnergy g φ x :=
  Real.sq_sqrt (zero_le_one.trans (profileFrequencyEnergy_ge_one g φ x))

lemma profileFrequencyScale_ge_one (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    1 ≤ profileFrequencyScale g φ x := by
  have h := Real.sqrt_nonneg (profileFrequencyEnergy g φ x)
  have he := profileFrequencyScale_sq g φ x
  have h1 := profileFrequencyEnergy_ge_one g φ x
  change 0 ≤ profileFrequencyScale g φ x at h
  nlinarith

lemma continuous_profileFrequencyEnergy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (profileFrequencyEnergy g φ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  have hg : Continuous (coordinateMetricGradient g φ) :=
    (hGi.clm_apply (hφ.fderiv_right (m := ∞) (by simp))).continuous
  exact continuous_const.add (((contDiff_selfMetricFlat g).continuous.clm_apply hg).clm_apply hg)

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

theorem exists_supported_box_nodal_quasimodes_subregions_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ K →
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
    (∀ J ∈ partition, 0 < ℓ J) ∧
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
        (∀ y ∈ normalWaveEquiv '' Box.Icc I, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(16*ε))*n*(∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x))) <
            SignTests.signCertificate
              (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
              (fun a => ε/(n*ℓ a.val)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(16*ε))*n*(∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x))) <
            36*Measure.hausdorffMeasure 2 ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_supported_nodal_quasimodes_subregions g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit I hIK
  let L : (Fin 3 → ℝ) → ℝ := fun x => profileFrequencyScale g φ (normalWaveEquiv x)
  have hL : Continuous L := Real.continuous_sqrt.comp
    ((continuous_profileFrequencyEnergy g hφ).comp normalWaveEquiv.continuous)
  have hL1 : ∀ x, 1 ≤ L x := fun x => profileFrequencyScale_ge_one g φ _
  obtain ⟨partition,hπ,ℓ,hℓ⟩ := exists_profile_box_partition I L hL.continuousOn
    (fun x _ => zero_lt_one.trans_le (hL1 x))
  let J := {J : Box (Fin 3) // J ∈ partition.boxes}
  let P : J → Set (Fin 3 → ℝ) := fun a => Box.Ioo a.val
  let Cₛ : J → Set (Fin 3 → ℝ) := fun a => Box.Icc (middleBox a.val)
  have hmass := middleBox_partition_mass I L hL.continuousOn partition hπ ℓ
    (fun a ha x hx => (hℓ a ha).2 x hx |>.2)
  have hmasspos : 0 < ∑ a : J, ℓ a.val*(volume (Cₛ a)).toReal := by
    exact (div_pos (box_profile_integral_pos I L hL.continuousOn (fun x _ => hL1 x)) (by norm_num)).trans_le hmass
  have hshifts : ∀ᶠ n : ℝ in atTop, ∀ a : J, ∀ x ∈ Cₛ a, ∀ j : Fin 3,
      x+Pi.single j (ε/(n*ℓ a.val)) ∈ P a := by
    rw [Filter.eventually_all]
    intro a
    exact middleBox_eventually_shift_mem a.val hε (hℓ a.val a.property).1
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.1 hshifts
  refine ⟨partition,hπ,ℓ,fun a ha => (hℓ a ha).1,?_⟩
  intro m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,C,hC,max N N₁,hN.trans (le_max_left _ _),?_⟩
  intro n hn S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog hb
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans ((le_max_left _ _).trans hn))
  have hPK (a : J) : normalWaveEquiv '' P a ⊆ normalWaveEquiv '' Box.Icc I := by
    rintro y ⟨x,hx,rfl⟩
    exact ⟨x,Box.le_iff_Icc.mp (partition.le_of_mem a.property) (Box.Ioo_subset_Icc a.val hx),rfl⟩
  have hregion (a : J) (x : Fin 3 → ℝ) (hx : x ∈ Cₛ a) :
      x ∈ P a ∧ profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a.val ∧
      ℓ a.val ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
      ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a.val)) ∈ P a := by
    have hxp := middleBox_Icc_subset a.val hx
    have hscale := (hℓ a.val a.property).2 x (Box.Ioo_subset_Icc a.val hxp)
    refine ⟨hxp,hscale.2,?_,hN₁ n ((le_max_right _ _).trans hn) a x hx⟩
    change ℓ a.val ≤ 2*L x
    linarith [hscale.1]
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ :=
    hdata n ((le_max_left _ _).trans hn) S hS E hES hEK w hw W hW hW0
      hWlower hWupper hwbound hlog (normalWaveEquiv '' Box.Icc I) hIK hb J P Cₛ (fun a => ℓ a.val)
      (fun a => (hℓ a.val a.property).1) (fun a => box_Ioo_open a.val)
      (fun a => box_Ioo_convex a.val) (partition_Ioo_disjoint I partition)
      (fun a => (middleBox a.val).measurableSet_Icc)
      (fun a => isFiniteMeasure_restrict.mpr ((middleBox a.val).measure_Icc_lt_top volume).ne)
      hPK hregion hmasspos
  have hle : (p₀/(16*ε))*n*(∫ x in Box.Icc I, L x) ≤
      (p₀/(2*ε))*n*(∑ a : J, ℓ a.val*(volume (Cₛ a)).toReal) := by
    calc
      _ = (p₀/(2*ε))*n*((∫ x in Box.Icc I, L x)/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  exact ⟨u,hu,huc,hus,hder,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions_oai := @OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions_oai
