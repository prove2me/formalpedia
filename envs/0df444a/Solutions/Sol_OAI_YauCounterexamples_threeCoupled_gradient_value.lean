-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_gradient_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:44.629237+00:00
-- url     : https://prove2.me/submissions/e7940a16-4971-4b76-b3e3-3b26e790c397

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_ambient_derivative

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LpInverseGramFstContraction
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Function Module
open scoped Matrix InnerProductSpace
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma gram_mul_repr (b : Basis ι ℝ E) (u : E) :
    (Matrix.gram ℝ b) *ᵥ (fun i => b.repr u i) = fun i => inner ℝ (b i) u := by
  ext i
  calc
    _ = inner ℝ (b i) (∑ j, b.repr u j • b j) := by
      simp only [inner_sum,inner_smul_right,Matrix.mulVec,dotProduct,Matrix.gram_apply]
      simp only [mul_comm]
    _ = _ := by rw [b.sum_repr]

lemma inverse_gram_inner (b : Basis ι ℝ E) (u : E) :
    (Matrix.gram ℝ b)⁻¹ *ᵥ (fun i => inner ℝ (b i) u) = fun i => b.repr u i := by
  rw [← gram_mul_repr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')]
  simp

theorem inverse_gram_contraction (b : Basis ι ℝ E) (u v : E) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j) u * inner ℝ (b i) v =
      inner ℝ u v := by
  calc
    _ = ∑ i, b.repr u i * inner ℝ (b i) v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      have hh := congrFun (inverse_gram_inner b u) i
      change (∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j) u) = b.repr u i at hh
      rw [hh]
    _ = inner ℝ (∑ i, b.repr u i • b i) v := by
      simp only [sum_inner,inner_smul_left,conj_trivial]
    _ = _ := by rw [b.sum_repr]


end

open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_zero (p : E) (L : F →ₗᵢ[ℝ] E) : roundChart p L 0 = p := by
  simp [roundChart,stereoInvFunAux]

lemma roundChart_first (p : E) (L : F →ₗᵢ[ℝ] E) :
    HasFDerivAt (roundChart p L) L.toContinuousLinearMap 0 := by
  have h : HasFDerivAt (stereoInvFunAux (-p)) (ContinuousLinearMap.id ℝ E)
      (L.toContinuousLinearMap 0) := by simpa using hasFDerivAt_stereoInvFunAux (-p)
  convert h.comp (0:F) L.toContinuousLinearMap.hasFDerivAt using 1
  · rfl
  · ext z
    rfl


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
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LpProductLinearMap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
section LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
lemma lpProductFunction_hasFDerivAt {f : E → A} {g : F → B}
    {x : WithLp 2 (E×F)} {Df : E →L[ℝ] A} {Dg : F →L[ℝ] B}
    (hf : HasFDerivAt f Df x.fst) (hg : HasFDerivAt g Dg x.snd) :
    HasFDerivAt (lpProductFunction f g) (lpProductLinearMap Df Dg) x := by
  have hp := HasFDerivAt.prodMap (x.fst,x.snd) hf hg
  have hi := hp.comp x (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap.hasFDerivAt
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.hasFDerivAt.comp x hi
end LpProductJets
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_LpProductFunctionMetric
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
lemma lpProductRoundChart_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B) :
    HasFDerivAt (lpProductFunction (roundChart p L) (roundChart q K))
      (lpProductIsometry L K).toContinuousLinearMap 0 := by
  exact lpProductFunction_hasFDerivAt (roundChart_first p L) (roundChart_first q K)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma sphere_chart_center (p : Sphere n) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) 0 = _
    rw [sphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)


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
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphereFrame_orthogonal (p : Metric.sphere (0 : A) 1) (w : Euclidean n) :
    inner ℝ (p : A) (unitSphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : A) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : A)) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma unitSphere_chart_center (p : Metric.sphere (0 : A) 1) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : A)) 0 = _
    rw [unitSphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphereFrame_coordinates (p : Metric.sphere (0 : A) 1) (a : A) :
    unitSphereFrame (n:=n) p (unitSphereCoordinates (n:=n) p a) = unitSphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨unitSphereProjection p a,_⟩)) : A) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma unitSphereCoordinates_inner (p : Metric.sphere (0 : A) 1) (a b : A) :
    inner ℝ (unitSphereCoordinates (n:=n) p a) (unitSphereCoordinates (n:=n) p b) =
      inner ℝ a b - inner ℝ (p : A) a * inner ℝ (p : A) b := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates,unitSphereFrame_coordinates]
  simp [unitSphereProjection,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    real_inner_comm a (p : A)]

lemma unitSphereFrame_inner (p : Metric.sphere (0 : A) 1) (a : A) (w : Euclidean n) :
    inner ℝ (unitSphereFrame (n:=n) p w) a = inner ℝ w (unitSphereCoordinates (n:=n) p a) := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates]
  have hh := unitSphereFrame_orthogonal p w
  rw [real_inner_comm] at hh
  simp [unitSphereProjection,inner_sub_right,inner_smul_right,hh]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeModelContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
lemma three_chart_center (p : ThreeManifold) : chartAt ThreeModel p p = 0 := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · exact sphere_chart_center p.1
  · exact unitSphere_chart_center (n:=1) p.2
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace
lemma three_coordinate_embedding (p : ThreeManifold) (y v : ThreeModel) :
    mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion
      ((chartAt ThreeModel p).symm y)
      (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel p).symm y v) =
        fderiv ℝ (threeChartMap p) y v := by
  have hy : y ∈ (chartAt ThreeModel p).target := by rw [three_chart_target]; trivial
  have hh := mfderiv_comp y
    (threeImmersion_smooth.mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv,three_chart_symm] at he
  exact he.symm
lemma three_metricCoefficients (p : ThreeManifold) (y : ThreeModel) (i j : CoordIndex ThreeModel) :
    metricCoefficients threeBackgroundMetric p y i j =
      inner ℝ (fderiv ℝ (threeChartMap p) y (Module.finBasis ℝ ThreeModel i))
        (fderiv ℝ (threeChartMap p) y (Module.finBasis ℝ ThreeModel j)) := by
  change (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion ((chartAt ThreeModel p).symm y) (coordinateVector p y i)) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion ((chartAt ThreeModel p).symm y) (coordinateVector p y j)) = _
  simp only [coordinateVector,three_coordinate_embedding]
lemma three_metricCoefficients_zero (p : ThreeManifold) :
    metricCoefficients threeBackgroundMetric p 0 = Matrix.gram ℝ (Module.finBasis ℝ ThreeModel) := by
  have hh : fderiv ℝ (threeChartMap p) 0 = (threeFrame p).toContinuousLinearMap :=
    (lpProductRoundChart_first (p.1:Euclidean 3) (p.2:ℂ) (sphereFrame p.1)
      (unitSphereFrame (n:=1) p.2)).fderiv
  ext i j
  rw [three_metricCoefficients,hh]
  exact (threeFrame p).inner_map_map _ _
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma productAxis_coord (i : Fin 3) (x : Euclidean 3) : inner ℝ (productAxis i) x = x i := by
  simp [productAxis,EuclideanSpace.inner_single_left]
lemma productA_re (x : Euclidean 3) : (productA x).re=x 0 := by simp [productA,planarLinear,productAxis_coord]
lemma productA_im (x : Euclidean 3) : (productA x).im=x 1 := by simp [productA,planarLinear,productAxis_coord]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFormulaNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeFormula_dimension_fact
lemma three_gradient_pair_of_ambient_derivative (p : ThreeManifold) (u : ThreeManifold → ℝ)
    (a : Euclidean 3) (b : ℂ)
    (hd : ∀ v : ThreeModel, fderiv ℝ (u ∘ (chartAt ThreeModel p).symm) 0 v=
      inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) a+
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) b) :
    coordinateGradientPair threeBackgroundMetric u u p=
      inner ℝ a a-(inner ℝ (p.1:Euclidean 3) a)^2+
        (inner ℝ b b-(inner ℝ (p.2:ℂ) b)^2) := by
  let V : ThreeModel := WithLp.toLp 2
    (unitSphereCoordinates (n:=2) p.1 a,unitSphereCoordinates (n:=1) p.2 b)
  have hinner (v : ThreeModel) : fderiv ℝ (u ∘ (chartAt ThreeModel p).symm) 0 v=inner ℝ v V := by
    rw [hd]
    erw [unitSphereFrame_inner,unitSphereFrame_inner]
    rfl
  rw [coordinateGradientPair,three_chart_center,three_metricCoefficients_zero]
  simp only [hinner]
  have hswap (i j) :
      (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
        inner ℝ (Module.finBasis ℝ ThreeModel i) V * inner ℝ (Module.finBasis ℝ ThreeModel j) V =
      (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
        inner ℝ (Module.finBasis ℝ ThreeModel j) V * inner ℝ (Module.finBasis ℝ ThreeModel i) V := by ring
  calc
    _ = ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
        inner ℝ (Module.finBasis ℝ ThreeModel j) V * inner ℝ (Module.finBasis ℝ ThreeModel i) V := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hswap i j
    _ = inner ℝ V V := inverse_gram_contraction _ _ _
    _ = _ := ?_

  change inner ℝ (unitSphereCoordinates (n:=2) p.1 a) (unitSphereCoordinates (n:=2) p.1 a)+
    inner ℝ (unitSphereCoordinates (n:=1) p.2 b) (unitSphereCoordinates (n:=1) p.2 b)=_
  erw [unitSphereCoordinates_inner,unitSphereCoordinates_inner]
  ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeProjectionNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
lemma threeCoupled_gradient_value_oai (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold) :
    coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) p=
      (k:ℝ)^2*((( (p.2:ℂ)^k*productA p.1^(k-1)).re+
        ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).re)^2+
        ((p.2:ℂ)^k*productA p.1^(k-1)).im^2+
        ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).im^2-
        (threeCoupled r k p)^2+(threeCoupledComplex r k p).im^2) := by
  rw [three_gradient_pair_of_ambient_derivative p _ _ _ (threeCoupled_ambient_derivative r k hk p)]
  let α := (p.2:ℂ)^k*productA p.1^(k-1)
  let β := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
  have hp (z : ℂ) : z^(k-1)*z=z^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : α*productA p.1+β*productB p.1=threeCoupledComplex r k p := by
    dsimp only [α,β,threeCoupledComplex]
    rw [←hp (productA p.1),←hp (productB p.1)]
    ring
  have haxis (i : Fin 3) : inner ℝ (p.1:Euclidean 3) (productAxis i)=(p.1:Euclidean 3) i := by
    rw [real_inner_comm,productAxis_coord]
  have hrad : inner ℝ (p.1:Euclidean 3) (threeAmbientSphereGradient r k p)=(k:ℝ)*threeCoupled r k p := by
    change inner ℝ (p.1:Euclidean 3) ((k:ℝ) • ((α.re+β.re) • productAxis 0-
      α.im • productAxis 1-β.im • productAxis 2))=(k:ℝ)*(threeCoupledComplex r k p).re
    rw [←he]
    simp only [inner_smul_right,inner_sub_right,haxis,Complex.add_re,Complex.mul_re,
      productA_re,productA_im,productB_re,productB_im]
    ring
  have hn : inner ℝ (Complex.I*(p.2:ℂ)) (Complex.I*(p.2:ℂ))=1 := by
    rw [real_inner_self_eq_norm_sq,norm_mul,Complex.norm_I,p.2.norm_coe]
    norm_num
  have ho : inner ℝ (p.2:ℂ) (Complex.I*(p.2:ℂ))=0 := by
    simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [hrad]
  change inner ℝ ((k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2))
      ((k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2))-
      ((k:ℝ)*threeCoupled r k p)^2+
      (inner ℝ ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ)))
        ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ)))-
      (inner ℝ (p.2:ℂ) ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ))))^2)=_
  change _ = (k:ℝ)^2*((α.re+β.re)^2+α.im^2+β.im^2-
    (threeCoupled r k p)^2+(threeCoupledComplex r k p).im^2)
  simp only [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right,
    productAxis_inner,hn,ho]
  norm_num [Fin.ext_iff]
  ring
end


open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_gradient_value_oai := @OAI.YauCounterexamples.threeCoupled_gradient_value_oai
