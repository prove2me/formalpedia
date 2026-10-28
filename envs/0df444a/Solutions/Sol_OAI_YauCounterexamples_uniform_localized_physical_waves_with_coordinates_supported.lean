-- Prove2me | solution 1 for OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:40:34.56277+00:00
-- url     : https://prove2.me/submissions/8a3d848e-d124-40ed-99a2-dd428703273f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_compact_normal_image_neighborhood
import Theorems.Thm_OAI_YauCounterexamples_exists_normal_wave_chart_family
import Theorems.Thm_OAI_YauCounterexamples_normalChartWave_residual_germ
import Theorems.Thm_OAI_YauCounterexamples_normalFamilyWave_at_zero
import Theorems.Thm_OAI_YauCounterexamples_normal_family_wave_localized_estimates

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

lemma coordinateKoszul_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w z : E) :
    coordinateKoszul D v w z = (D v w z+D w v z-D z v w)/2 := by
  change (1/2 : ℝ) * (D v w z+D w v z-D z v w) = _
  ring

lemma metricChristoffel_pairing (g : SmoothMetric E E) (x v w z : E) :
    selfMetricFlat g x (metricChristoffel g x v w) z =
      (fderiv ℝ (selfMetricFlat g) x v w z+fderiv ℝ (selfMetricFlat g) x w v z-
        fderiv ℝ (selfMetricFlat g) x z v w)/2 := by
  have h := (selfMetricFlat_invertible g x).inverse_apply_eq.mp
    (show (selfMetricFlat g x).inverse (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x) v w) =
      metricChristoffel g x v w from rfl)
  exact (congrArg (fun l : E →L[ℝ] ℝ => l z) h.symm).trans (coordinateKoszul_apply _ _ _ _)

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

omit [FiniteDimensional ℝ E] in
lemma fderiv_selfMetricFlat_symm (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z = fderiv ℝ (selfMetricFlat g) x v z w := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  have he : (fun y => selfMetricFlat g y w z) = (fun y => selfMetricFlat g y z w) :=
    funext (fun y => selfMetricFlat_symm g y w z)
  have h := congrArg (fun f : E → ℝ => fderiv ℝ f x v) he
  have heval (w z : E) : fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
    rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
        (differentiableAt_const z),
      fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  simpa only [heval] using h

lemma metricChristoffel_symm (g : SmoothMetric E E) (x v w : E) :
    metricChristoffel g x v w = metricChristoffel g x w v := by
  apply (selfMetricFlat_invertible g x).injective
  ext z
  rw [metricChristoffel_pairing,metricChristoffel_pairing,
    fderiv_selfMetricFlat_symm g x z v w]
  ring

lemma metricChristoffel_compatible (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z =
      selfMetricFlat g x (metricChristoffel g x v w) z +
      selfMetricFlat g x w (metricChristoffel g x v z) := by
  rw [selfMetricFlat_symm g x w, metricChristoffel_pairing,metricChristoffel_pairing,
    fderiv_selfMetricFlat_symm g x v z w]
  ring

lemma compact_selfMetricFlat_lower (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ selfMetricFlat g x v v :=
  compact_positive_bilinear_lower hK (selfMetricFlat g) (contDiff_selfMetricFlat g).continuous
    (fun x _ _ hv => selfMetricFlat_pos g x hv)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MultilinearPolynomial
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
variable {σ : Type*}

variable [Fintype σ]

theorem contDiff_realPolyEval (p : MvPolynomial σ ℂ) : ContDiff ℝ ∞ (realPolyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c by funext x; exact realPolyEval_C c x]
    exact contDiff_const
  | add p q hp hq =>
    rw [show realPolyEval (p + q) = fun x => realPolyEval p x + realPolyEval q x by funext x; exact realPolyEval_add p q x]
    exact hp.add hq
  | mul_X p i hp =>
    have hx : ContDiff ℝ ∞ (fun x : σ → ℝ => (x i : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
    rw [show realPolyEval (p * X i) = fun x => realPolyEval p x * (x i : ℂ) by funext x; simp]
    exact hp.mul hx


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WaveDeriv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

section WaveDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem contDiff_waveDeriv (v : E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (waveDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end WaveDifferentiation


end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmoothFiniteWaveSum
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*}

variable {ι : Type*} [Fintype ι]

lemma contDiff_waveCoordinateOperator (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (V : E → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (waveCoordinateOperator e G b V) :=
  (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hG i j).mul (contDiff_waveDeriv (e i) _ (contDiff_waveDeriv (e j) V hV))))).add
      (ContDiff.sum (fun i _ => (hb i).mul (contDiff_waveDeriv (e i) V hV)))

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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Type*}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff (S : E → ℂ) (V : ℕ → E → ℂ) (ζ : E → ℂ) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S (fun j x => ζ x * V j x) J n = fun x => ζ x * smoothFiniteWave S V J n x := by
  funext x
  simp only [smoothFiniteWave,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff_support (S : E → ℂ) (V : ℕ → E → ℂ) (ζ : E → ℂ) (J : ℕ) (n : ℝ) :
    Function.support (smoothFiniteWave S (fun j x => ζ x * V j x) J n) ⊆ Function.support ζ := by
  rw [smoothFiniteWave_cutoff]
  exact Function.support_mul_subset_left _ _

omit [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff_compact (S : E → ℂ) (V : ℕ → E → ℂ) (ζ : E → ℂ)
    (hζ : HasCompactSupport ζ) (J : ℕ) (n : ℝ) :
    HasCompactSupport (smoothFiniteWave S (fun j x => ζ x * V j x) J n) :=
  hζ.mono (smoothFiniteWave_cutoff_support S V ζ J n)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalJetMapFirstPhase
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFormNorm
attribute [local instance] OAI.YauCounterexamples.normalDualSpace
attribute [local instance] OAI.YauCounterexamples.normalFormSpace
local instance normalTriNorm_r0045f6_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma contDiff_normalJetMap (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (normalJetMap p A C) :=
  (contDiff_const.add A.contDiff).sub ((C.contDiff.clm_apply contDiff_id).const_smul (1/2 : ℝ))

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_zero (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    normalJetMap p A C 0 = p := by simp [normalJetMap]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    HasFDerivAt (normalJetMap p A C) (A - C x) x := by
  have h := ((hasFDerivAt_const p x).add A.hasFDerivAt).sub
    ((C.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (1/2 : ℝ))
  change HasFDerivAt (fun y => p + A y - (1/2 : ℝ) • C y y) (A - C x) x
  apply h.congr_fderiv
  ext v
  simp only [_root_.sub_apply, _root_.add_apply,
    zero_add, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, id_eq, hC v x, ← two_smul ℝ, smul_smul]
  norm_num

lemma normalMetricTensor_at_zero (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) :
    normalMetricTensor g p A 0 = (selfMetricFlat g p).bilinearComp A A := by
  simp [normalMetricTensor, normalJetMap_zero]

local instance normalTriSpace_r0045f6_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma contDiff_normalMetricTensor_apply (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (v w : E) :
    ContDiff ℝ ∞ (fun x => normalMetricTensor g p A x v w) := by
  let C := (metricChristoffel g p).bilinearComp A A
  have hF := contDiff_normalJetMap p A C
  have hV (v : E) : ContDiff ℝ ∞ (fun x => (A - C x) v) :=
    (contDiff_const.sub C.contDiff).clm_apply contDiff_const
  exact (((contDiff_selfMetricFlat g).comp hF).clm_apply (hV v)).clm_apply (hV w)

lemma normalMetricTensor_normal_jet (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (v w : E) :
    fderiv ℝ (fun x => normalMetricTensor g p A x v w) 0 = 0 := by
  let C := (metricChristoffel g p).bilinearComp A A
  have hC : ∀ v w, C v w = C w v := fun v w => metricChristoffel_symm g p (A v) (A w)
  have hF : HasFDerivAt (normalJetMap p A C) A 0 := by
    simpa only [map_zero, sub_zero] using hasFDerivAt_normalJetMap p A C hC 0
  have hB := ((contDiff_selfMetricFlat g).differentiable (by simp) p).hasFDerivAt
  have hV (v : E) : HasFDerivAt (fun x => (A - C x) v) (-(C.flip v)) 0 := by
    have hh := (hasFDerivAt_const (A v) (0 : E)).sub (C.flip v).hasFDerivAt
    have hh' := hh.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun x => show (A - C x) v = ((fun _ : E => A v) - (C.flip v : E → E)) x by rfl))
    simpa only [zero_sub] using hh'
  have hBF : HasFDerivAt (fun x => selfMetricFlat g (normalJetMap p A C x))
      ((fderiv ℝ (selfMetricFlat g) p).comp A) 0 := by
    have hB' : HasFDerivAt (selfMetricFlat g) (fderiv ℝ (selfMetricFlat g) p)
        (normalJetMap p A C 0) := by rw [normalJetMap_zero]; exact hB
    exact hB'.comp 0 hF
  have hD := (hBF.clm_apply (hV v)).clm_apply (hV w)
  have hz : HasFDerivAt (fun x => normalMetricTensor g p A x v w) (0 : E →L[ℝ] ℝ) 0 := by
    change HasFDerivAt (fun y => selfMetricFlat g (normalJetMap p A C y)
      ((A - C y) v) ((A - C y) w)) (0 : E →L[ℝ] ℝ) 0
    apply hD.congr_fderiv
    ext u
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, _root_.neg_apply, map_neg,
      normalJetMap_zero, map_zero, sub_zero, _root_.zero_apply]
    change -selfMetricFlat g p (A v) (C u w) +
      (-selfMetricFlat g p (C u v) (A w) +
        fderiv ℝ (selfMetricFlat g) p (A u) (A v) (A w)) = 0
    rw [metricChristoffel_compatible]
    dsimp only [C, ContinuousLinearMap.bilinearComp_apply]
    ring
  exact hz.fderiv


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
open Set Filter Manifold
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_FrameDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance frameDualNorm_r0045f6_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_r0045f6_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_r0045f6_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_isClosed (g : SmoothMetric E E) {K : Set E} (hK : IsClosed K) :
    IsClosed (metricFrameSet g K) := by
  apply (hK.preimage continuous_fst).inter
  change IsClosed {q : E × (E →L[ℝ] E) | ∀ v w : E,
    selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  exact isClosed_eq
    (((contDiff_selfMetricFlat g).continuous.comp continuous_fst).clm_apply
      (continuous_snd.clm_apply continuous_const) |>.clm_apply
      (continuous_snd.clm_apply continuous_const)) continuous_const

lemma metricFrameSet_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2‖ ≤ R := by
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_⟩
  intro q hq
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml q.1 hq.1 (q.2 v)
  rw [hq.2 v v, real_inner_self_eq_norm_sq] at hlow
  have hh : Real.sqrt m * ‖q.2 v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]

theorem metricFrameSet_isCompact (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    IsCompact (metricFrameSet g K) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  apply (hK.prod (isCompact_closedBall (0 : E →L[ℝ] E) R)).of_isClosed_subset
    (metricFrameSet_isClosed g hK.isClosed)
  intro q hq
  exact ⟨hq.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb q hq⟩

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalFamilyVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualSpace
local instance normalFamilyFormNorm_r0045f6_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace_r0045f6_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma contDiff_frameChristoffel (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) =>
      (metricChristoffel g q.1).bilinearComp q.2 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => (metricChristoffel g q.1).comp q.2) :=
    ((contDiff_metricChristoffel g).comp contDiff_fst).clm_comp contDiff_snd
  have h2 := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h1
  have h3 := h2.clm_comp contDiff_snd
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h3

lemma contDiff_normalJetFamily (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => (metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) :=
    (contDiff_frameChristoffel g).comp contDiff_fst
  exact (contDiff_fst.fst.add (contDiff_fst.snd.clm_apply contDiff_snd)).sub
    ((hC.clm_apply contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

lemma contDiff_normalMetricFamily_apply (g : SmoothMetric E E) (v w : E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalMetricTensor g q.1.1 q.1.2 q.2 v w) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) :=
    ((contDiff_frameChristoffel g).comp contDiff_fst).clm_apply contDiff_snd
  have hD := (show ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => q.1.2) from contDiff_fst.snd).sub hC
  exact (((contDiff_selfMetricFlat g).comp (contDiff_normalJetFamily g)).clm_apply
    (hD.clm_apply contDiff_const)).clm_apply (hD.clm_apply contDiff_const)

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
open scoped Topology ContDiff
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma normal_iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma parameter_iteratedFDeriv (f : P × E → F) (t : P) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let q : P × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : P × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := normal_iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_parameter_iteratedFDeriv (f : P × E → F) {z : P × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : P × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact parameter_iteratedFDeriv f w.1 w.2 n hw


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
open scoped Topology ContDiff
section ParameterDerivative
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma parameter_fderiv_apply (f : P × E → F) (hf : Differentiable ℝ f)
    (p : P) (x v : E) :
    fderiv ℝ (fun y => f (p,y)) x v = fderiv ℝ f (p,x) (0,v) := by
  have h := (hf (p,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
  exact congrArg (fun T => T v) h.fderiv

lemma contDiff_parameter_fderiv_apply (f : P × E → F) (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun q : P × E => fderiv ℝ (fun x => f (q.1,x)) q.2 v) := by
  simp only [parameter_fderiv_apply f (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma continuous_parameter_iteratedFDeriv (f : P × E → F) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ k (fun x => f (q.1,x)) q.2) :=
  continuous_iff_continuousAt.mpr (fun _ => continuousAt_parameter_iteratedFDeriv f k hf.contDiffAt)
end ParameterDerivative

variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]
lemma contDiff_matrix_det (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) :
    ContDiff ℝ ∞ (fun p => (A p).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hA _ _

lemma contDiff_matrix_adjugate (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun p => (A p).adjugate i j) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro k _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hA _ _

lemma contDiffOn_matrix_inv (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) (i j : ι) :
    ContDiffOn ℝ ∞ (fun p => (A p)⁻¹ i j) {p | (A p).det ≠ 0} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_matrix_det A hA).contDiffOn.inv (fun _ hp => hp)).mul
    (contDiff_matrix_adjugate A hA i j).contDiffOn

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
open Set Filter Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise

lemma contDiff_normalWaveMetric (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun q : NormalWaveParameter × NormalWaveSpace => normalWaveMetric g q.1 q.2 i j) :=
  contDiff_normalMetricFamily_apply g _ _

lemma normalWaveMetric_zero (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    normalWaveMetric g q 0 = 1 := by
  ext i j
  change normalMetricTensor g q.1 q.2 0 _ _ = _
  rw [normalMetricTensor_at_zero]
  change selfMetricFlat g q.1 (q.2 _) (q.2 _) = _
  rw [hq.2]
  exact (EuclideanSpace.basisFun (Fin 3) ℝ).inner_eq_ite i j

lemma normalWaveMetric_first_jet (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) : HasFDerivAt (𝕜 := ℝ) (normalWaveMetric g q) 0 0 := by
  have hc (i j : Fin 3) : HasFDerivAt (𝕜 := ℝ) (fun x => normalWaveMetric g q x i j) 0 0 := by
    have h := (contDiff_normalMetricTensor_apply g q.1 q.2
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)).differentiable (by simp) 0
    simpa only [normalWaveMetric, normalMetricTensor_normal_jet] using h.hasFDerivAt
  convert (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_pi.mpr (fun j => hc i j))) using 1 <;> rfl

lemma hasFDerivAt_matrix_inv_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Matrix ι ι ℝ) {x : E} (hA : HasFDerivAt (𝕜 := ℝ) A 0 x) (hdet : (A x).det ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun y => (A y)⁻¹) 0 x := by
  have hc (i j : ι) : ContDiffAt ℝ ∞ (fun M : Matrix ι ι ℝ => M⁻¹ i j) (A x) := by
    have hO : IsOpen {M : Matrix ι ι ℝ | M.det ≠ 0} :=
      isOpen_ne_fun (contDiff_matrix_det id (fun _ _ => by fun_prop)).continuous continuous_const
    exact (contDiffOn_matrix_inv id (fun _ _ => by fun_prop) i j _ hdet).contDiffAt
      (hO.mem_nhds hdet)
  have hi : DifferentiableAt ℝ (fun M : Matrix ι ι ℝ => M⁻¹) (A x) := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hc i j).differentiableAt (by simp)
  have h := hi.hasFDerivAt.comp x hA
  erw [ContinuousLinearMap.comp_zero] at h
  exact h

lemma normalWaveInverse_first_jet (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    HasFDerivAt (𝕜 := ℝ) (fun x => (normalWaveMetric g q x)⁻¹) 0 0 :=
  hasFDerivAt_matrix_inv_zero _ (normalWaveMetric_first_jet g q) (by rw [normalWaveMetric_zero g hq]; simp)

theorem exists_normal_inverse_extension (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ A : NormalWaveParameter × NormalWaveSpace → Matrix (Fin 3) (Fin 3) ℝ,
      ∃ d : NormalWaveParameter × NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ d ∧
      ∃ O : Set (NormalWaveParameter × NormalWaveSpace), IsOpen O ∧
        metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ O ∧
        ∀ q ∈ O, A q = (normalWaveMetric g q.1 q.2)⁻¹ ∧
          d q = (normalWaveMetric g q.1 q.2).det⁻¹ := by
  let G := fun q : NormalWaveParameter × NormalWaveSpace => normalWaveMetric g q.1 q.2
  let V := {q | (G q).det ≠ 0}
  have hG (i j : Fin 3) : ContDiff ℝ ∞ (fun q => G q i j) := contDiff_normalWaveMetric g i j
  have hV : IsOpen V := isOpen_ne_fun (contDiff_matrix_det G hG).continuous continuous_const
  have hc : IsCompact (metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)}) :=
    (metricFrameSet_isCompact g hK).prod isCompact_singleton
  have hsub : metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ V := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    subst x
    change (normalWaveMetric g q 0).det ≠ 0
    rw [normalWaveMetric_zero g hq]
    simp
  have hF : ContDiffOn ℝ ∞ (fun q => ((G q)⁻¹,(G q).det⁻¹)) V := by
    apply ContDiffOn.prodMk
    · apply contDiffOn_pi.mpr
      intro i
      apply contDiffOn_pi.mpr
      intro j
      exact contDiffOn_matrix_inv G hG i j
    · exact (contDiff_matrix_det G hG).contDiffOn.inv (fun _ h => h)
  obtain ⟨ψ,hψ,he⟩ := smooth_extension_near_compact hc hV hsub hF
  obtain ⟨O,hO,hKO,hEq⟩ := mem_nhdsSet_iff_exists.mp he
  refine ⟨fun q => (ψ q).1,fun q => (ψ q).2,hψ.fst,hψ.snd,O,hO,hKO,?_⟩
  intro q hq
  have hh := hEq hq
  exact ⟨(congrArg Prod.fst hh).symm,(congrArg Prod.snd hh).symm⟩

lemma normalWaveMetric_det_first_jet (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) : HasFDerivAt (𝕜 := ℝ)
      (fun x => (normalWaveMetric g q x).det) 0 0 := by
  have hd := (contDiff_matrix_det (id : Matrix (Fin 3) (Fin 3) ℝ → _) (fun _ _ => by fun_prop)).differentiable (by simp)
  have h := (hd (normalWaveMetric g q 0)).hasFDerivAt.comp 0
    (normalWaveMetric_first_jet g q)
  erw [ContinuousLinearMap.comp_zero] at h
  exact h

lemma normalWaveFirstCoefficient_zero (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    normalWaveFirstCoefficient g q 0 = 0 := by
  let : ContinuousSMul ℝ NormalWaveSpace := IsBoundedSMul.continuousSMul
  funext j
  have hi := normalWaveInverse_first_jet g hq
  have hc (i j : Fin 3) : fderiv ℝ (fun y => (normalWaveMetric g q y)⁻¹ i j) 0 = 0 := by
    have h1 := (ContinuousLinearMap.proj i : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ)).hasFDerivAt.comp 0 hi
    have h2 := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp 0 h1
    have h := h2.fderiv
    erw [ContinuousLinearMap.comp_zero] at h
    exact h
  simp [normalWaveFirstCoefficient,hc,(normalWaveMetric_det_first_jet g q).fderiv]

theorem exists_normal_wave_coefficients (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ A : NormalWaveParameter × NormalWaveSpace → Matrix (Fin 3) (Fin 3) ℝ,
      ∃ b : NormalWaveParameter × NormalWaveSpace → Fin 3 → ℝ,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      ∃ r > 0, ∀ q ∈ metricFrameSet g K,
        A (q,0) = 1 ∧ HasFDerivAt (𝕜 := ℝ) (fun x => A (q,x)) 0 0 ∧ b (q,0) = 0 ∧
        ∀ x ∈ Metric.ball (0 : NormalWaveSpace) r,
          A (q,x) = (normalWaveMetric g q x)⁻¹ ∧ b (q,x) = normalWaveFirstCoefficient g q x := by
  obtain ⟨A,d,hA,hd,O,hO,hsub,he⟩ := exists_normal_inverse_extension g hK
  let b := fun q : NormalWaveParameter × NormalWaveSpace => fun j : Fin 3 =>
    ∑ i, (fderiv ℝ (fun x => A (q.1,x) i j) q.2 (EuclideanSpace.basisFun (Fin 3) ℝ i) +
      (1/2 : ℝ) * A q i j * d q * fderiv ℝ (fun x => (normalWaveMetric g q.1 x).det) q.2
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hb : ContDiff ℝ ∞ b := by
    apply contDiff_pi.mpr
    intro j
    dsimp only [b]
    apply ContDiff.sum
    intro i _
    apply ContDiff.add
    · exact contDiff_parameter_fderiv_apply (fun q => A q i j) (contDiff_pi.mp (contDiff_pi.mp hA i) j) _
    · exact ((contDiff_const.mul (contDiff_pi.mp (contDiff_pi.mp hA i) j)).mul hd).mul
        (contDiff_parameter_fderiv_apply _
          (contDiff_matrix_det _ (contDiff_normalWaveMetric g)) _)
  have hgerm (q : NormalWaveParameter) (x : NormalWaveSpace) (hx : (q,x) ∈ O) :
      (fun y => A (q,y)) =ᶠ[𝓝 x] (fun y => (normalWaveMetric g q y)⁻¹) := by
    have ht : Tendsto (fun y : NormalWaveSpace => (q,y)) (𝓝 x) (𝓝 (q,x)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [ht (hO.mem_nhds hx)] with y hy
    exact (he (q,y) hy).1
  have hbe (q : NormalWaveParameter) (x : NormalWaveSpace) (hx : (q,x) ∈ O) :
      b (q,x) = normalWaveFirstCoefficient g q x := by
    funext j
    dsimp only [b,normalWaveFirstCoefficient]
    apply Finset.sum_congr rfl
    intro i _
    have hg : (fun y => A (q,y) i j) =ᶠ[𝓝 x] (fun y => (normalWaveMetric g q y)⁻¹ i j) :=
      (hgerm q x hx).fun_comp (fun M => M i j)
    rw [hg.fderiv_eq,(he (q,x) hx).1,(he (q,x) hx).2]
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton hO hsub
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  refine ⟨A,b,hA,hb,r,hr,?_⟩
  intro q hq
  have hq0 : (q,0) ∈ O := hsub ⟨hq,mem_singleton 0⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [(he (q,0) hq0).1,normalWaveMetric_zero g hq]; simp
  · exact (normalWaveInverse_first_jet g hq).congr_of_eventuallyEq (hgerm q 0 hq0)
  · rw [hbe q 0 hq0,normalWaveFirstCoefficient_zero g hq]
  · intro x hx
    have hqx : (q,x) ∈ O := hUV ⟨hKU hq,hrV hx⟩
    exact ⟨(he (q,x) hqx).1,hbe q x hqx⟩


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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem exists_normal_wave_pi_coefficients (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ,
      ∃ b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      ∃ r > 0, ∀ q ∈ metricFrameSet g K,
        (∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
        (∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
        b (q,0) = 0 ∧
        ∀ x, ‖normalWaveEquiv x‖ < r →
          (∀ i j, A (q,x) i j = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ)) ∧
          (∀ j, b (q,x) j = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ)) := by
  obtain ⟨A,b,hA,hb,r,hr,he⟩ := exists_normal_wave_coefficients g hK
  let Ap := fun q : NormalWaveParameter × (Fin 3 → ℝ) =>
    fun i j : Fin 3 => (A (q.1,normalWaveEquiv q.2) i j : ℂ)
  let bp := fun q : NormalWaveParameter × (Fin 3 → ℝ) =>
    fun j : Fin 3 => (b (q.1,normalWaveEquiv q.2) j : ℂ)
  have hT : ContDiff ℝ ∞ (fun q : NormalWaveParameter × (Fin 3 → ℝ) => (q.1,normalWaveEquiv q.2)) :=
    contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd)
  have hAp : ContDiff ℝ ∞ Ap := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_pi.mp (contDiff_pi.mp hA i) j).comp hT)
  have hbp : ContDiff ℝ ∞ bp := by
    apply contDiff_pi.mpr
    intro j
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_pi.mp hb j).comp hT)
  refine ⟨Ap,bp,hAp,hbp,r,hr,?_⟩
  intro q hq
  obtain ⟨h0,hd,hb0,heq⟩ := he q hq
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    simp only [Ap,map_zero,h0,Matrix.one_apply]
    split_ifs <;> simp
  · intro i j
    let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj i : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ)))
    have hf := (L.hasFDerivAt.comp 0 hd).comp 0 normalWaveEquiv.hasFDerivAt
    have hf' : HasFDerivAt (fun x => Ap (q,x) i j)
        ((L.comp 0).comp normalWaveEquiv.toContinuousLinearMap) 0 := hf
    simpa only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp] using hf'.fderiv
  · ext j
    simp [bp,hb0]
  · intro x hx
    have h := heq (normalWaveEquiv x) (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
    exact ⟨fun i j => by dsimp [Ap]; rw [h.1],fun j => by dsimp [bp]; rw [h.2]⟩


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

lemma contDiff_smoothFiniteWave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : E → ℂ} {V : ℕ → E → ℂ} (hS : ContDiff ℝ ∞ S)
    (hV : ∀ j, ContDiff ℝ ∞ (V j)) (J : ℕ) (n : ℝ) :
    ContDiff ℝ ∞ (smoothFiniteWave S V J n) := by
  unfold smoothFiniteWave
  exact (contDiff_const.mul hS).cexp.mul
    (ContDiff.sum (fun j _ => contDiff_const.mul (hV j)))

lemma contDiff_canonicalCutoffWave
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (m D : ℕ) (n : ℝ) :
    ContDiff ℝ ∞ (canonicalCutoffWave A b s z Q ζ m D n) :=
  contDiff_smoothFiniteWave (contDiff_realPolyEval _)
    (fun _ => hζ.mul (contDiff_realPolyEval _)) _ _



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Matrix Manifold
open scoped Topology ContDiff
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma laplaceBeltrami_self (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    laplaceBeltrami g u x =
      coordinateMetricLaplacian (Module.finBasis ℝ E) (metricCoefficients g x) u x := by
  simp only [laplaceBeltrami,coordinateMetricLaplacian,coordinateMetricFlux,
    chartAt_self_eq,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,
    Function.comp_id,id_eq]


end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalChartWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open scoped Topology ContDiff
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_apply (e : OpenPartialHomeomorph E F) (f : E → V)
    {x : E} (hx : x ∈ e.source) : smoothChartPush e f (e x) = f x := by
  simp only [smoothChartPush,Set.indicator_of_mem (e.map_source hx),Function.comp_apply,
    e.left_inv hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_support (e : OpenPartialHomeomorph E F) (f : E → V) :
    Function.support (smoothChartPush e f) ⊆ e '' tsupport f := by
  intro y hy
  have ht : y ∈ e.target := by
    by_contra hh
    exact hy (by simp [smoothChartPush,hh])
  refine ⟨e.symm y, subset_closure ?_,e.right_inv ht⟩
  simpa only [smoothChartPush,Set.indicator_of_mem ht,Function.comp_apply,
    Function.mem_support] using hy

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_tsupport (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : HasCompactSupport f) (hsub : tsupport f ⊆ e.source) :
    tsupport (smoothChartPush e f) ⊆ e '' tsupport f := by
  apply closure_minimal (smoothChartPush_support e f)
  exact (hf.image_of_continuousOn (e.continuousOn.mono hsub)).isClosed

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_compact (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : HasCompactSupport f) (hsub : tsupport f ⊆ e.source) :
    HasCompactSupport (smoothChartPush e f) :=
  (hf.image_of_continuousOn (e.continuousOn.mono hsub)).of_isClosed_subset
    isClosed_closure (smoothChartPush_tsupport e hf hsub)

lemma contDiff_smoothChartPush (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hsub : tsupport f ⊆ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (smoothChartPush e f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · have hg : smoothChartPush e f =ᶠ[𝓝 y] f ∘ e.symm := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact Set.indicator_of_mem hz _
    exact (hf.contDiffAt.comp y ((hi y hy).contDiffAt (e.open_target.mem_nhds hy))).congr_of_eventuallyEq hg
  · have hn : y ∉ e '' tsupport f := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hsub hx))
    have hs : y ∉ tsupport (smoothChartPush e f) := fun h => hn (smoothChartPush_tsupport e hc hsub h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hs)

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

lemma normalChartWave_compact (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source) :
    HasCompactSupport (normalChartWave e f) := by
  apply smoothChartPush_compact e (hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph)
  change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
  rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
  intro x hx
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm x) hx

lemma contDiff_normalChartWave (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (normalChartWave e f) := by
  apply contDiff_smoothChartPush e (hf.comp normalWaveEquiv.symm.contDiff)
    (hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph) _ hi
  change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
  rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
  intro x hx
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm x) hx

lemma normalChartWave_apply (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) :
    normalChartWave e f (e (normalWaveEquiv x)) = f x := by
  simpa only [normalChartWave,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using
    smoothChartPush_apply e (f ∘ normalWaveEquiv.symm) hx



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_NormalWaveMetricCommonPositive
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

lemma normalWaveMetric_common_positive (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x : NormalWaveSpace, ‖x‖ < r →
      0 < (normalWaveMetric g q x).det := by
  let G : NormalWaveParameter × NormalWaveSpace → Matrix (Fin 3) (Fin 3) ℝ :=
    fun w => normalWaveMetric g w.1 w.2
  have hG (i j : Fin 3) : ContDiff ℝ ∞ (fun w => G w i j) := contDiff_normalWaveMetric g i j
  let O := {w : NormalWaveParameter × NormalWaveSpace | 0 < (G w).det}
  have hO : IsOpen O := isOpen_lt continuous_const (contDiff_matrix_det G hG).continuous
  have hs : metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ O := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    have he : x = 0 := mem_singleton_iff.mp hx
    subst x
    change 0 < (normalWaveMetric g q 0).det
    rw [normalWaveMetric_zero g hq]
    simp
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton hO hs
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  refine ⟨r,hr,?_⟩
  intro q hq x hx
  change (q,x) ∈ O
  apply hUV
  refine ⟨hKU hq,hrV ?_⟩
  simpa only [Metric.mem_ball,dist_zero_right] using hx

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_UniformJetBoundsFiberComp
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
open scoped Topology ContDiff
variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma compact_fiber_jet_bound (ψ : P × E → F) (hψ : ContDiff ℝ (∞ : WithTop ℕ∞) ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ w ∈ L, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖ ≤ D := by
  let B := fun w : P × E => ∑ i ∈ Finset.range (m+1),
    ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖
  have hB : Continuous B := continuous_finsetSum _
    (fun i _ => (continuous_parameter_iteratedFDeriv ψ hψ i).norm)
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro w hw i hi
  calc
    _ ≤ B w := Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    _ ≤ ‖B w‖ := le_abs_self _
    _ ≤ C := hC w hw
    _ ≤ max 1 C := le_max_right _ _

theorem compact_fiber_comp_derivative_bound (ψ : P × E → F) (hψ : ContDiff ℝ (∞ : WithTop ℕ∞) ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ C > 0, ∀ w ∈ L, ∀ f : F → V, ContDiff ℝ (∞ : WithTop ℕ∞) f →
      ∀ n : ℝ, 1 ≤ n → ∀ a : ℝ, 0 ≤ a →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (ψ w)‖ ≤ a*n^i) → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (fun y => f (ψ (w.1,y))) w.2‖ ≤ C*a*n^k := by
  obtain ⟨D,hD,hDb⟩ := compact_fiber_jet_bound ψ hψ hL m
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨(m.factorial : ℝ)*D^m,mul_pos (by positivity) (pow_pos hDp _),?_⟩
  intro w hw f hf n hn a ha hb k hk
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have hCk : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f (ψ w)‖ ≤ a*n^k := by
    intro i hi
    exact (hb i (hi.trans hk)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn hi) ha)
  have hDk : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖ ≤ D^i := by
    intro i hi hik
    exact (hDb w hw i (hik.trans hk)).trans (by
      simpa only [pow_one] using (pow_le_pow_right₀ hD hi))
  have hbnd := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) hf
    (hψ.comp (contDiff_const.prodMk contDiff_id))
    (show (k : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl k) w.2 hCk hDk
  have hfact : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hk
  have hpow : D^k ≤ D^m := pow_le_pow_right₀ hD hk
  calc
    _ ≤ (k.factorial : ℝ)*(a*n^k)*D^k := hbnd
    _ ≤ (m.factorial : ℝ)*(a*n^k)*D^m := by gcongr
    _ = _ := by ring

end

open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactNormalForwardBound
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma compact_normal_forward_bound (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ ≤ R →
      ‖normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (normalWaveEquiv x)-q.1‖ ≤ C*‖x‖ := by
  let F := fun w : NormalWaveParameter × (Fin 3 → ℝ) =>
    normalJetMap w.1.1 w.1.2 ((metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) (normalWaveEquiv w.2)
  have hF : ContDiff ℝ ∞ F := (contDiff_normalJetFamily g).comp
    (contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd))
  have hL : IsCompact (metricFrameSet g K ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) R) :=
    (metricFrameSet_isCompact g hK).prod (isCompact_closedBall 0 R)
  obtain ⟨C,hC,hb⟩ := compact_fiber_jet_bound F hF hL 1
  refine ⟨C,hC,?_⟩
  intro q hq x hx
  have hFq : ContDiff ℝ ∞ (fun x => F (q,x)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hd (v) (hv : v ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
      ‖fderiv ℝ (fun x => F (q,x)) v‖ ≤ C := by
    rw [←norm_iteratedFDeriv_one]
    exact hb (q,v) ⟨hq,hv⟩ 1 le_rfl
  have hh := (convex_closedBall (0 : Fin 3 → ℝ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hFq.differentiable (by simp) v) hd (Metric.mem_closedBall_self hR)
    (show x ∈ Metric.closedBall (0 : Fin 3 → ℝ) R by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  simpa only [F,map_zero,normalJetMap_zero,sub_zero] using hh

lemma gaussian_coordinate_to_physical {c C n : ℝ} (hc : 0 ≤ c) (hC : 0 < C) (hn : 0 ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ C*a) :
    Real.exp (-c*n*a^2) ≤ Real.exp (-(c/C^2)*n*b^2) := by
  apply Real.exp_le_exp.mpr
  have hsq : b^2 ≤ C^2*a^2 := by
    calc
      b^2 ≤ (C*a)^2 := by
        simpa only [pow_two] using mul_le_mul hba hba hb (mul_nonneg hC.le ha)
      _ = C^2*a^2 := mul_pow C a 2
  have hm := mul_le_mul_of_nonneg_left hsq (div_nonneg (mul_nonneg hc hn) (sq_nonneg C))
  have hnC : C^2 ≠ 0 := pow_ne_zero _ hC.ne'
  have he : (c*n/C^2)*(C^2*a^2) = c*n*a^2 := by field_simp
  rw [he] at hm
  calc
    -c*n*a^2 = -(c*n*a^2) := by ring
    _ ≤ -((c*n/C^2)*b^2) := neg_le_neg hm
    _ = -(c/C^2)*n*b^2 := by ring
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalInverseVecNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalInverseVecNorm
attribute [local instance] OAI.YauCounterexamples.normalInverseVecSpace
local instance normalInverseBiVecNorm_r0045f6_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalInverseBiVecSpace_r0045f6_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
lemma normalFamilyTotal_smooth (g : SmoothMetric E E) : ContDiff ℝ (∞ : WithTop ℕ∞) (normalFamilyTotal g) :=
  contDiff_fst.prodMk (contDiff_normalJetFamily g)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactFiberLocalCompBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples
section LocalCompTransfer
variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_fiber_local_comp_bound (ψ : P × E → F) (hψ : ContDiff ℝ ∞ ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ C > 0, ∀ q : P, ∀ u : E → V, ∀ f : F → V, ContDiff ℝ ∞ f →
      (∀ y ∈ tsupport u, (q,y) ∈ L ∧ u =ᶠ[𝓝 y] (fun z => f (ψ (q,z)))) →
      ∀ n : ℝ, 1 ≤ n → ∀ a : E → ℝ, (∀ y, 0 ≤ a y) →
      (∀ y ∈ tsupport u, ∀ i ≤ m,
        ‖iteratedFDeriv ℝ i f (ψ (q,y))‖ ≤ a y*n^i) →
      ∀ y, ∀ k ≤ m, ‖iteratedFDeriv ℝ k u y‖ ≤ C*a y*n^k := by
  obtain ⟨C,hC,hb⟩ := compact_fiber_comp_derivative_bound ψ hψ hL m (V := V)
  refine ⟨C,hC,?_⟩
  intro q u f hf hu n hn a ha he y k hk
  by_cases hy : y ∈ tsupport u
  · obtain ⟨hyL,hug⟩ := hu y hy
    rw [(hug.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hb (q,y) hyL f hf n hn (a y) (ha y) (he y hy) k hk
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hy
    rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds]
    simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg (mul_nonneg hC.le (ha y)) (pow_nonneg (le_trans zero_le_one hn) _)
end LocalCompTransfer

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_CoordinateMetricLaplacianGerm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open scoped Topology ContDiff
namespace YauCounterexamples
section MetricLocality
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_germ (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    coordinateMetricLaplacian b G u x = coordinateMetricLaplacian b G v x := by
  unfold coordinateMetricLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => coordinateMetricFlux b G u y i) =ᶠ[𝓝 x]
      (fun y => coordinateMetricFlux b G v y i) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [coordinateMetricFlux,hy]
  rw [he.fderiv_eq]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_zero (b : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ) (x : E) :
    coordinateMetricLaplacian b G (0 : E → ℝ) x = 0 := by
  simp [coordinateMetricLaplacian,coordinateMetricFlux]

lemma complexLaplaceBeltrami_self_germ (g : SmoothMetric E E)
    {u v : E → ℂ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    complexLaplaceBeltrami g u x = complexLaplaceBeltrami g v x := by
  apply Complex.ext
  · simp only [complexLaplaceBeltrami,laplaceBeltrami_self]
    exact coordinateMetricLaplacian_germ _ _ (h.fun_comp Complex.re)
  · simp only [complexLaplaceBeltrami,laplaceBeltrami_self]
    exact coordinateMetricLaplacian_germ _ _ (h.fun_comp Complex.im)

lemma complexLaplaceBeltrami_self_zero (g : SmoothMetric E E) (x : E) :
    complexLaplaceBeltrami g (0 : E → ℂ) x = 0 := by
  apply Complex.ext <;>
    change laplaceBeltrami g (0 : E → ℝ) x = 0 <;>
    rw [laplaceBeltrami_self,coordinateMetricLaplacian_zero]

lemma complexLaplaceBeltrami_residual_tsupport (g : SmoothMetric E E) (u : E → ℂ) (lam : ℂ) :
    tsupport (fun y => complexLaplaceBeltrami g u y + lam*u y) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he := notMem_tsupport_iff_eventuallyEq.mp hn
  have hz := complexLaplaceBeltrami_self_germ g he
  rw [complexLaplaceBeltrami_self_zero] at hz
  apply hx
  change complexLaplaceBeltrami g u x + lam*u x = 0
  rw [hz,he.eq_of_nhds]
  simp
end MetricLocality

lemma canonicalCutoffWave_tsupport
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (m D : ℕ) (n : ℝ) :
    tsupport (canonicalCutoffWave A b s z Q ζ m D n) ⊆ tsupport ζ :=
  closure_mono (smoothFiniteWave_cutoff_support _ _ _ _ _)

lemma canonicalCutoffWave_compact
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : HasCompactSupport ζ) (m D : ℕ) (n : ℝ) :
    HasCompactSupport (canonicalCutoffWave A b s z Q ζ m D n) :=
  smoothFiniteWave_cutoff_compact _ _ _ hζ _ _

lemma normalChartWave_tsupport (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source) :
    tsupport (normalChartWave e f) ⊆ (fun x => e (normalWaveEquiv x)) '' tsupport f := by
  have hc' := hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph
  have hs' : tsupport (f ∘ normalWaveEquiv.symm) ⊆ e.source := by
    change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
    rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
    intro y hy
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm y) hy
  intro y hy
  obtain ⟨x,hx,rfl⟩ := smoothChartPush_tsupport e hc' hs' hy
  refine ⟨normalWaveEquiv.symm x,?_,by simp⟩
  rwa [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph] at hx

lemma normalChartWave_germ (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) {y : NormalWaveSpace} (hy : y ∈ e.target) :
    normalChartWave e f =ᶠ[𝓝 y] (fun z => f (normalWaveEquiv.symm (e.symm z))) := by
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact Set.indicator_of_mem hz _
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_UniformCoordinatePacketsCommonSlope2
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
theorem uniform_localized_physical_waves_with_coordinates_supported_oai (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {V : Set NormalWaveSpace} (hV : IsOpen V) (hKV : K ⊆ V)
    :
    ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
      (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
      (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
    ∃ ρ > 0,
      (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
      ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0,
        (∀ q ∈ metricFrameSet g K, ∀ z Q n, tsupport (U q z Q n) ⊆ V) ∧
        (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
          U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
        ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
        U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤
            T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
            (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y) := by
  obtain ⟨A,b,hA,hb,rc,hrc,hcoeff⟩ := exists_normal_wave_pi_coefficients g hK
  obtain ⟨ri,hri,e,he,hi,hsource,ψ,hψ,hgerm⟩ := exists_normal_wave_chart_family g hK
  obtain ⟨rp,hrp,hpos⟩ := normalWaveMetric_common_positive g hK
  refine ⟨A,b,e,hA,hb,(fun q hq => (hcoeff q hq).1),
    (fun q hq => (hcoeff q hq).2.1),he,?_⟩
  intro B C κ hκ m D
  obtain ⟨rw,hrw,hest⟩ := normal_family_wave_localized_estimates g φ hφ hK A b hA hb
    (fun q hq => (hcoeff q hq).1) (fun q hq => (hcoeff q hq).2.1) B C hκ m D
  obtain ⟨Cf,hCf,hforward⟩ := compact_normal_forward_bound g hK hrw.le
  have hCfpos : 0 < Cf := lt_of_lt_of_le zero_lt_one hCf
  let c := (κ/2)/Cf^2
  have hc : 0 < c := div_pos (half_pos hκ) (sq_pos_of_pos hCfpos)
  let R := min ri (min rc rp)
  have hR : 0 < R := lt_min hri (lt_min hrc hrp)
  obtain ⟨δ,hδ,hδmap⟩ := Metric.continuousAt_iff.mp normalWaveEquiv.continuousAt R hR
  obtain ⟨rv,hrv,hVmap⟩ := compact_normal_image_neighborhood g hK hV hKV
  refine ⟨min (min rw δ) rv,lt_min (lt_min hrw hδ) hrv,?_,?_⟩
  · intro q hq x hx
    have hx : ‖x‖ < min rw δ := hx.trans_le (min_le_left _ _)
    apply hsource q hq
    have hxδ : dist x 0 < δ := by simpa only [dist_zero_right] using hx.trans_le (min_le_right rw δ)
    have hxR : ‖normalWaveEquiv x‖ < R := by
      simpa only [map_zero,dist_zero_right] using hδmap hxδ
    simpa only [Metric.mem_closedBall,dist_zero_right] using hxR.le.trans (min_le_left ri (min rc rp))
  intro ζ hζ hcζ hsζ hζ0
  have hsζV : tsupport ζ ⊆ Metric.ball 0 rv := (Metric.ball_subset_ball (min_le_right _ _)).trans' hsζ
  have hsζ : tsupport ζ ⊆ Metric.ball 0 (min rw δ) := (Metric.ball_subset_ball (min_le_left _ _)).trans' hsζ
  obtain ⟨T,hT,hTbound⟩ := hest ζ hζ hζ0
  let L : Set (NormalWaveParameter × NormalWaveSpace) :=
    normalFamilyTotal g '' (metricFrameSet g K ×ˢ Metric.closedBall 0 ri)
  have hL : IsCompact L := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall 0 ri)).image (normalFamilyTotal_smooth g).continuous
  let Ψ : NormalWaveParameter × NormalWaveSpace → (Fin 3 → ℝ) := fun w => normalWaveEquiv.symm (ψ w)
  have hΨ : ContDiff ℝ ∞ Ψ := normalWaveEquiv.symm.contDiff.comp hψ
  obtain ⟨F,hF,hFbound⟩ := compact_fiber_local_comp_bound Ψ hΨ hL m (V := ℂ)
  let U := fun q z Q n => normalChartWave (e q) (normalFamilyWave g φ A b q z Q ζ m D n)
  refine ⟨U,F*T,mul_pos hF hT,c,hc,?_,?_,?_⟩
  · intro q hq z Q n
    let f := normalFamilyWave g φ A b q z Q ζ m D n
    have hfc : HasCompactSupport f := canonicalCutoffWave_compact _ _ _ _ _ _ hcζ _ _ _
    have hfs : tsupport f ⊆ tsupport ζ := canonicalCutoffWave_tsupport _ _ _ _ _ _ _ _ _
    have hxs (x) (hx : x ∈ tsupport f) : normalWaveEquiv x ∈ (e q).source := by
      apply hsource q hq
      have hxδ := Metric.ball_subset_ball (min_le_right rw δ) (hsζ (hfs hx))
      have hxR : ‖normalWaveEquiv x‖ < R := by
        simpa only [map_zero,dist_zero_right] using hδmap hxδ
      simpa only [Metric.mem_closedBall,dist_zero_right] using hxR.le.trans (min_le_left ri (min rc rp))
    intro y hy
    obtain ⟨x,hx,hxy⟩ := normalChartWave_tsupport (e q) hfc hxs hy
    rw [←hxy,he q]
    exact hVmap q hq x (by simpa only [Metric.mem_ball,dist_zero_right] using hsζV (hfs hx))
  · intro q z Q n x hx
    exact normalChartWave_apply (e q) _ hx
  intro q hq z Q hz hnQ hQ n hn hlin
  let f := normalFamilyWave g φ A b q z Q ζ m D n
  let u := U q z Q n
  let fR := fun x => waveCoordinateOperator (fun i => Pi.single i 1)
    (fun i j x => A (q,x) i j) (fun j x => b (q,x) j) f x + (n : ℂ)*((n : ℂ)+2)*f x
  let uR := fun y => complexLaplaceBeltrami g u y + (n : ℂ)*((n : ℂ)+2)*u y
  have hf : ContDiff ℝ ∞ f := contDiff_canonicalCutoffWave _ _ _ _ _ _ hζ _ _ _
  have hfc : HasCompactSupport f := canonicalCutoffWave_compact _ _ _ _ _ _ hcζ _ _ _
  have hfs : tsupport f ⊆ tsupport ζ := canonicalCutoffWave_tsupport _ _ _ _ _ _ _ _ _
  have hxw (x) (hx : x ∈ tsupport f) : x ∈ Metric.ball 0 rw :=
    Metric.ball_subset_ball (min_le_left _ _) (hsζ (hfs hx))
  have hxR (x) (hx : x ∈ tsupport f) : ‖normalWaveEquiv x‖ < R := by
    have hxδ := Metric.ball_subset_ball (min_le_right rw δ) (hsζ (hfs hx))
    simpa only [map_zero,dist_zero_right] using hδmap hxδ
  have hxri (x) (hx : x ∈ tsupport f) : normalWaveEquiv x ∈ Metric.closedBall 0 ri := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      le_trans (hxR x hx).le (min_le_left ri (min rc rp))
  have hxs (x) (hx : x ∈ tsupport f) : normalWaveEquiv x ∈ (e q).source := hsource q hq (hxri x hx)
  have hu : ContDiff ℝ ∞ u := contDiff_normalChartWave (e q) hf hfc hxs (hi q)
  have huc : HasCompactSupport u := normalChartWave_compact (e q) hfc hxs
  have hfR : ContDiff ℝ ∞ fR :=
    (contDiff_waveCoordinateOperator (fun i => Pi.single i 1) _ _
      (fun i j => ((contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)))
      (fun j => ((contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id))) f hf).add
      (contDiff_const.mul hf)
  have hcover (y) (hy : y ∈ tsupport u) : ∃ x ∈ tsupport f,
      y = e q (normalWaveEquiv x) ∧ Ψ (q,y) = x := by
    obtain ⟨x,hx,hxy⟩ := normalChartWave_tsupport (e q) hfc hxs hy
    refine ⟨x,hx,hxy.symm,?_⟩
    have hg := (hgerm q hq (normalWaveEquiv x) (hxri x hx)).eq_of_nhds
    rw [(e q).left_inv (hxs x hx)] at hg
    dsimp only [Ψ]
    rw [←hxy,←hg]
    exact normalWaveEquiv.symm_apply_apply x
  have hlocal (y) (hy : y ∈ tsupport u) : (q,y) ∈ L ∧
      u =ᶠ[𝓝 y] (fun w => f (Ψ (q,w))) ∧ uR =ᶠ[𝓝 y] (fun w => fR (Ψ (q,w))) := by
    obtain ⟨x,hx,rfl,hΨx⟩ := hcover y hy
    have hgi := hgerm q hq (normalWaveEquiv x) (hxri x hx)
    have hgw : u =ᶠ[𝓝 (e q (normalWaveEquiv x))] (fun w => f (Ψ (q,w))) :=
      (normalChartWave_germ (e q) f ((e q).map_source (hxs x hx))).trans
        (hgi.fun_comp (fun v => f (normalWaveEquiv.symm v)))
    have hxr : ‖normalWaveEquiv x‖ < min rc rp := lt_of_lt_of_le (hxR x hx) (min_le_right _ _)
    have hgr := normalChartWave_residual_germ g q (e q) (he q) hf hfc hxs (hi q)
      (fun i j x => A (q,x) i j) (fun j x => b (q,x) j) ((n : ℂ)*((n : ℂ)+2))
      (fun v hv => hpos q hq v (lt_of_lt_of_le hv (min_le_right rc rp)))
      (fun x hx => ((hcoeff q hq).2.2.2 x (lt_of_lt_of_le hx (min_le_left rc rp))).1)
      (fun x hx => ((hcoeff q hq).2.2.2 x (lt_of_lt_of_le hx (min_le_left rc rp))).2)
      (hxs x hx) hxr
    refine ⟨?_,hgw,hgr.trans (hgi.fun_comp (fun v => fR (normalWaveEquiv.symm v)))⟩
    refine ⟨(q,normalWaveEquiv x),⟨hq,hxri x hx⟩,?_⟩
    change (q,normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
      (normalWaveEquiv x)) = (q,e q (normalWaveEquiv x))
    rw [he q]
  have hbwave : ∀ y ∈ tsupport u, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i f (Ψ (q,y))‖ ≤
        (T*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2))*n^i := by
    intro y hy i hi
    obtain ⟨x,hx,rfl,hΨx⟩ := hcover y hy
    rw [hΨx]
    have h := (hTbound q hq z Q hz hnQ hQ n hn hlin x (hxw x hx) i hi).1
    have hxrw : ‖x‖ ≤ rw := by
      exact (show ‖x‖ < rw by simpa only [Metric.mem_ball,dist_zero_right] using hxw x hx).le
    have hd := hforward q hq x hxrw
    have hga := gaussian_coordinate_to_physical (half_pos hκ).le hCfpos
      (le_trans zero_le_one hn) (norm_nonneg x)
      (norm_nonneg (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (normalWaveEquiv x)-q.1)) hd
    have h' := h.trans (mul_le_mul_of_nonneg_left hga
      (mul_nonneg (mul_nonneg hT.le (pow_nonneg (le_trans zero_le_one hn) _)) (Real.exp_pos _).le))
    rw [he q]
    change _ ≤ (T*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))*
      Real.exp (-c*n*‖normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (normalWaveEquiv x)-q.1‖^2))*n^i
    convert h' using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (unfold c; ring)
  have hbr : ∀ y ∈ tsupport uR, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i fR (Ψ (q,y))‖ ≤ (T*(n^(D+1))⁻¹*Real.exp (n*φ y))*1^i := by
    intro y hy i hi
    have hyu := complexLaplaceBeltrami_residual_tsupport g u ((n : ℂ)*((n : ℂ)+2)) hy
    obtain ⟨x,hx,rfl,hΨx⟩ := hcover y hyu
    rw [hΨx,one_pow,mul_one,he q]
    exact (hTbound q hq z Q hz hnQ hQ n hn hlin x (hxw x hx) i hi).2
  have hc0 : f 0 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) :=
    normalFamilyWave_at_zero g φ A b hA hb q (hcoeff q hq).1 (hcoeff q hq).2.1
      z Q hQ hnQ ζ hζ0 m D n
  have hu0 : u q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) := by
    have hs0 : normalWaveEquiv 0 ∈ (e q).source := by
      apply hsource q hq
      simp only [map_zero,Metric.mem_closedBall,dist_self]
      exact hri.le
    have hval := normalChartWave_apply (e q) f hs0
    simpa only [map_zero,he q,normalJetMap_zero,hc0] using hval
  refine ⟨hu,huc,hu0,?_⟩
  intro y k hk
  have hw := hFbound q u f hf (fun y hy => ⟨(hlocal y hy).1,(hlocal y hy).2.1⟩)
    n hn (fun y => T*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2))
    (fun y => mul_nonneg (mul_nonneg hT.le (Real.exp_pos _).le) (Real.exp_pos _).le)
    hbwave y k hk
  have hr := hFbound q uR fR hfR (fun y hy =>
    let h := hlocal y (complexLaplaceBeltrami_residual_tsupport g u ((n : ℂ)*((n : ℂ)+2)) hy)
    ⟨h.1,h.2.2⟩) 1 le_rfl (fun y => T*(n^(D+1))⁻¹*Real.exp (n*φ y))
    (fun y => mul_nonneg (mul_nonneg hT.le (inv_nonneg.mpr (pow_nonneg (le_trans zero_le_one hn) _)))
      (Real.exp_pos _).le) hbr y k hk
  constructor
  · convert hw using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · convert hr using 1
    all_goals try with_reducible_and_instances rfl
    ring
end


open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported_oai := @OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported_oai
