-- Prove2me | solution 1 for OAI.YauCounterexamples.three_exceptional_intrinsic_margin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:35:46.902283+00:00
-- url     : https://prove2.me/submissions/d53f569b-10fa-4e5a-95ce-8cc2637416ed

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff

section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
omit [FiniteDimensional ℝ E] in
lemma scalarDifferential_chart_vector {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (v : E) :
    scalarDifferential u ((chartAt E p).symm y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y v) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y v := by
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
      (n := ∞)).mdifferentiableAt (by simp)
  have he := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at he
  exact (congrArg (fun T => T v) he).symm

lemma chart_derivative_dual_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (v : E) :
    (fderiv ℝ (u ∘ (chartAt E p).symm) y v)^2 ≤
      coordinateGradientPair g u u ((chartAt E p).symm y)*chartMetricForm g p y v v := by
  have hh := scalarDifferential_dual_bound hu g ((chartAt E p).symm y)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y v)
  rw [scalarDifferential_chart_vector hu p hy] at hh
  simpa only [chartMetricForm_pairing] using hh
end


end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threePacketA_norm (y : Fin 3 → ℝ) :
    ‖threePacketA y‖=‖productA (threeNormalInv (normalWaveEquiv y)).1‖ := by
  simp only [threePacketA,Function.comp_apply,threeComplexPower,pow_one,norm_mul,Circle.norm_coe,mul_one]
  rfl
lemma threePacketB_norm (y : Fin 3 → ℝ) :
    ‖threePacketB y‖=threeCouplingRadius*‖productB (threeNormalInv (normalWaveEquiv y)).1‖ := by
  simp only [threePacketB,threeComplexPower,pow_one,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<threeCouplingRadius by norm_num [threeCouplingRadius])]
  rfl
lemma threePacket_radius_bound (k : ℕ) (y : Fin 3 → ℝ) :
    threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k≤‖threePacketA y‖^k+‖threePacketB y‖^k := by
  rw [threePacketA_norm,threePacketB_norm]
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  dsimp [threeGlobalRadius]
  rcases le_total ‖productA (threeNormalInv (normalWaveEquiv y)).1‖
    (threeCouplingRadius*‖productB (threeNormalInv (normalWaveEquiv y)).1‖) with h|h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeWeight_le_packet (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    threeWeight φ k (threeNormalInv (normalWaveEquiv y))≤threePacketWeight φ k y := by
  dsimp [threeWeight,threePacketWeight]
  linarith [threePacket_radius_bound k y]
lemma three_packet_productWeight (k : ℕ) (y : Fin 3 → ℝ) :
    ‖threePacketA y‖^k+‖threePacketB y‖^k=productWeight threeCouplingRadius k (threeNormalInv (normalWaveEquiv y)) := by
  rw [threePacketA_norm,threePacketB_norm,mul_pow]; rfl
lemma three_exceptional_chart_iff (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    y∈threeExceptionalInChart φ k ↔ threeNormalInv (normalWaveEquiv y)∈threeExceptional φ k := by
  dsimp [threeExceptionalInChart,threeExceptional]
  rw [three_packet_productWeight]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
attribute [local instance] OAI.YauCounterexamples.threeGlobalResidualNormedSpace
local instance threeGlobalResidualContinuousSMul_r69d330_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_pullback_smooth {f : ThreeManifold → ℝ}
    (hf : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ f) (p : ThreeManifold) :
    ContDiff ℝ ∞ (f ∘ (chartAt ThreeModel p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hf p (by rw [three_chart_target]; trivial)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
attribute [local instance] OAI.YauCounterexamples.threeJetDualNorm
attribute [local instance] OAI.YauCounterexamples.threeJetDualSpace
local instance threeJetFormNorm_r69d330_1 : NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeJetFormSpace_r69d330_1 : NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := inferInstance
lemma three_compact_direction_metric_bound (g : SmoothMetric ThreeModel ThreeManifold)
    (r : ℝ) : ∃ C ≥ 1, ∀ y∈closedBall (0:NormalWaveSpace) r, ∀ i : Fin 3,
      chartMetricForm g threeProfileCenter (threeNormalEquiv y)
        (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))
        (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))  ≤  C ^ 2 := by
  have hcont : Continuous (chartMetricForm g threeProfileCenter) := by
    exact continuousOn_univ.mp (by simpa only [three_chart_target] using
      (chartMetricForm_contDiffOn g threeProfileCenter).continuousOn)
  obtain ⟨T,hT⟩ := ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalEquiv.continuous).exists_bound_of_continuousOn hcont.norm.continuousOn
  let L := ‖threeNormalEquiv.toContinuousLinearMap‖
  let C := max 1 T+L^2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [le_max_left (1:ℝ) T,sq_nonneg L]
  refine ⟨C,hC,?_⟩
  intro y hy i
  let v := threeNormalEquiv (normalWaveEquiv (Pi.single i 1))
  have hv : ‖v‖ ≤ L := by
    have h := threeNormalEquiv.toContinuousLinearMap.le_opNorm (normalWaveEquiv (Pi.single i 1))
    simpa [v,L,normalWaveEquiv_single,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,mul_one] using h
  have hT' : ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y)‖ ≤ max 1 T :=
    (by simpa only [norm_norm] using hT _ ⟨y,hy,rfl⟩ : ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y)‖ ≤ T) |>.trans (le_max_right _ _)
  calc
    _  ≤  ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y) v v‖ := le_abs_self _
    _  ≤  ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y)‖*‖v‖*‖v‖ :=
      (chartMetricForm g threeProfileCenter (threeNormalEquiv y)).le_opNorm₂ v v
    _  ≤  max 1 T*L*L := by gcongr
    _  ≤  C ^ 2 := by
      have h1 : max 1 T ≤ C := by dsimp [C]; nlinarith [sq_nonneg L]
      have h2 : L^2 ≤ C := by dsimp [C]; linarith [le_max_left (1:ℝ) T]
      nlinarith [mul_le_mul h1 h2 (sq_nonneg L) (by linarith : 0 ≤ C)]

lemma three_realWaveJet_intrinsic_upper {U : ThreeManifold → ℝ}
    (hU : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ U)
    (g : SmoothMetric ThreeModel ThreeManifold) {n W C : ℝ}
    (hn : 0<n) (hW : 0<W) (hC : 1 ≤ C) (x : Fin 3 → ℝ)
    (hmetric : ∀ i : Fin 3, chartMetricForm g threeProfileCenter
      (threeNormalEquiv (normalWaveEquiv x))
      (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))
      (threeNormalEquiv (normalWaveEquiv (Pi.single i 1))) ≤ C ^ 2) :
    ‖realWaveJet n W ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x‖  ≤
      C*(|U (threeNormalInv (normalWaveEquiv x))|+
        Real.sqrt (coordinateGradientPair g U U (threeNormalInv (normalWaveEquiv x)))/n)/W := by
  let q := threeNormalInv (normalWaveEquiv x)
  let F := U ∘ (chartAt ThreeModel threeProfileCenter).symm
  have hF : ContDiff ℝ ∞ F := three_chart_pullback_smooth hU _
  have hG : 0 ≤ coordinateGradientPair g U U q := coordinateGradientPair_nonneg g U q
  have hC0 : 0 ≤ C := by linarith
  have hder (i : Fin 3) : |fderiv ℝ ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x (Pi.single i 1)|  ≤
      C*Real.sqrt (coordinateGradientPair g U U q) := by
    have hd := chart_derivative_dual_bound hU g threeProfileCenter
      (show threeNormalEquiv (normalWaveEquiv x)∈(chartAt ThreeModel threeProfileCenter).target by rw [three_chart_target]; trivial)
      (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))
    have hd' := hd.trans (mul_le_mul_of_nonneg_left (hmetric i) hG)
    have he := ((hF.differentiable (by simp) _).hasFDerivAt.comp
      (normalWaveEquiv x) threeNormalEquiv.hasFDerivAt).comp x normalWaveEquiv.hasFDerivAt
    have he' := congrArg (fun T => T (Pi.single i 1)) he.fderiv
    change fderiv ℝ ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x (Pi.single i 1)=
      fderiv ℝ F (threeNormalEquiv (normalWaveEquiv x))
        (threeNormalEquiv (normalWaveEquiv (Pi.single i 1))) at he'
    rw [he']
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC0 (Real.sqrt_nonneg _))).mp
    rw [sq_abs,mul_pow,Real.sq_sqrt hG]
    exact hd'.trans_eq (mul_comm _ _)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rcases i with i|i
  · change ‖W⁻¹*U q‖  ≤  C*(|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),Real.norm_eq_abs]
    rw [mul_comm W⁻¹,←div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ hW.le
    calc
      _  ≤  |U q|+Real.sqrt (coordinateGradientPair g U U q)/n :=
        le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hn.le)
      _  ≤  _ := le_mul_of_one_le_left (by positivity) hC
  · change ‖n⁻¹*W⁻¹*fderiv ℝ ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x (Pi.single i 1)‖  ≤
      C*(|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),abs_of_pos (inv_pos.mpr hn)]
    calc
      _  ≤  n⁻¹*W⁻¹*(C*Real.sqrt (coordinateGradientPair g U U q)) :=
        mul_le_mul_of_nonneg_left (hder i) (by positivity)
      _ = C*(Real.sqrt (coordinateGradientPair g U U q)/n)/W := by ring
      _  ≤  _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (abs_nonneg _)) hC0) hW.le
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma three_exceptional_intrinsic_margin_oai (g : SmoothMetric ThreeModel ThreeManifold)
    (r : ℝ) : ∃ C ≥ 1, ∀ k : ℕ, 1 ≤ k → C ≤ productWaveFrequency k →
      ∀ φ : ThreeManifold → ℝ, threeExceptional φ k⊆threeNormalInv '' closedBall 0 r →
      ∀ U : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ U →
      (∀ y∈threeExceptionalInChart φ k, 1/productWaveFrequency k^110 ≤
        ‖realWaveJet (productWaveFrequency k) (threePacketWeight φ k y)
          ((U ∘ threeNormalInv) ∘ normalWaveEquiv) y‖) →
      ∀ p∈threeExceptional φ k, threeWeight φ k p/productWaveFrequency k^111 ≤
        |U p|+Real.sqrt (coordinateGradientPair g U U p)/productWaveFrequency k := by
  obtain ⟨C,hC,hmetric⟩ := three_compact_direction_metric_bound g r
  refine ⟨C,hC,?_⟩
  intro k hk hCν φ hcover U hU hjet p hp
  obtain ⟨y,hy,rfl⟩ := hcover hp
  let x := normalWaveEquiv.symm y
  have hxy : normalWaveEquiv x=y := normalWaveEquiv.apply_symm_apply y
  have hx : x∈threeExceptionalInChart φ k := (three_exceptional_chart_iff φ k x).mpr (by simpa only [hxy] using hp)
  have hν1 : 1 ≤ productWaveFrequency k := hC.trans hCν
  have hν0 : 0<productWaveFrequency k := zero_lt_one.trans_le hν1
  have hW : 0<threePacketWeight φ k x := by
    dsimp [threePacketWeight]; positivity
  have hu := three_realWaveJet_intrinsic_upper hU g hν0 hW hC x (fun i => by
    simpa only [hxy] using hmetric y hy i)
  have hh := (le_div_iff₀ hW).mp ((hjet x hx).trans hu)
  let J := |U (threeNormalInv y)|+Real.sqrt (coordinateGradientPair g U U (threeNormalInv y))/productWaveFrequency k
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hh' : threePacketWeight φ k x ≤ (C*J)*productWaveFrequency k^110 := by
    apply (div_le_iff₀ (pow_pos hν0 110)).mp
    simpa only [J,hxy,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  apply (div_le_iff₀ (pow_pos hν0 111)).mpr
  calc
    _  ≤  threePacketWeight φ k x := by simpa only [hxy] using threeWeight_le_packet φ k x
    _  ≤  (C*J)*productWaveFrequency k^110 := hh'
    _  ≤  (productWaveFrequency k*J)*productWaveFrequency k^110 := by gcongr
    _ = J*productWaveFrequency k^111 := by rw [pow_succ]; ring

end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_exceptional_intrinsic_margin_oai := @OAI.YauCounterexamples.three_exceptional_intrinsic_margin_oai
