-- Prove2me | solution 1 for OAI.YauCounterexamples.laplaceBeltrami_four_lift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:19:58.115994+00:00
-- url     : https://prove2.me/submissions/8c5325d9-e982-49b1-a195-d1c261b63224

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_laplaceBeltrami_any_basis_univ

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CoordinateMetricFlux
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma differentiableAt_coordinateMetricFlux {u : E → ℝ} {G : E → Matrix ι ι ℝ}
    {x : E} (hu : ContDiffAt ℝ 2 u x) (hG : DifferentiableAt ℝ G x)
    (hx : 0 < (G x).det) (b : Module.Basis ι ℝ E) :
    DifferentiableAt ℝ (coordinateMetricFlux b G u) x := by
  have hd : DifferentiableAt ℝ (fun y => (G y).det) x :=
    (differentiable_det _).comp x hG
  have hi := differentiableAt_matrix_inv hG (isUnit_iff_ne_zero.mpr hx.ne')
  have hu' := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply differentiableAt_pi.mpr
  intro i
  apply (hd.sqrt hx.ne').mul
  apply DifferentiableAt.fun_sum
  intro j hj
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hi i) j).mul
    (hu'.clm_apply (differentiableAt_const _))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_BlockDiagonalInverse
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E F H ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma blockDiagonal_inverse (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (Matrix.fromBlocks A 0 0 B)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 B⁻¹ := by
  have h := Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff A (0 : Matrix ι κ ℝ) B
    (iff_of_true ((Matrix.isUnit_iff_isUnit_det A).mpr hA) ((Matrix.isUnit_iff_isUnit_det B).mpr hB))
  simpa using h
omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_split (P : H →L[ℝ] E) (Q : H →L[ℝ] F)
    (a : Module.Basis ι ℝ E) (_ : Module.Basis κ ℝ F) (c : Module.Basis (ι ⊕ κ) ℝ H)
    (hPa : ∀ i, P (c (.inl i))=a i) (hPb : ∀ j, P (c (.inr j))=0)
    (hQa : ∀ i, Q (c (.inl i))=0)
    (A : E → Matrix ι ι ℝ) (B : F → Matrix κ κ ℝ)
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hpA : ∀ x, 0 < (A x).det) (hpB : ∀ x, 0 < (B x).det)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (x : H) :
    coordinateMetricLaplacian c (fun y => Matrix.fromBlocks (A (P y)) 0 0 (B (Q y))) (u ∘ P) x =
      coordinateMetricLaplacian a A u (P x) := by
  let ρ : H → ℝ := fun y => Real.sqrt (B (Q y)).det
  have hd (y : H) (v : H) : fderiv ℝ (u ∘ P) y v = fderiv ℝ u (P y) (P v) := by
    rw [fderiv_comp y (hu.differentiable (by simp) _) P.differentiableAt, P.fderiv]
    rfl
  have hρ : Differentiable ℝ ρ := fun y =>
    (((differentiable_det _).comp (Q y) (hB (Q y))).comp y Q.differentiableAt).sqrt (hpB (Q y)).ne'
  have hρa (i : ι) : fderiv ℝ ρ x (c (.inl i))=0 := by
    have hD := ((((differentiable_det _).comp (Q x) (hB (Q x))).sqrt (hpB (Q x)).ne').hasFDerivAt.comp x Q.hasFDerivAt)
    change (fderiv ℝ ((fun y => Real.sqrt ((Matrix.det ∘ B) y)) ∘ Q) x) _ = _
    rw [hD.fderiv]
    simp [ContinuousLinearMap.comp_apply,hQa]
  have hf (y : H) (i : ι) :
      coordinateMetricFlux c (fun z => Matrix.fromBlocks (A (P z)) 0 0 (B (Q z))) (u ∘ P) y (.inl i) =
        ρ y * coordinateMetricFlux a A u (P y) i := by
    simp only [coordinateMetricFlux,Matrix.det_fromBlocks_zero₂₁,
      blockDiagonal_inverse _ _ (isUnit_iff_ne_zero.mpr (hpA (P y)).ne') (isUnit_iff_ne_zero.mpr (hpB (Q y)).ne'),
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul,Finset.sum_const_zero,add_zero,hd,hPa]
    rw [Real.sqrt_mul (hpA (P y)).le]
    dsimp [ρ]
    ring
  have hv (j : κ) :
      (fun y => coordinateMetricFlux c (fun z => Matrix.fromBlocks (A (P z)) 0 0 (B (Q z))) (u ∘ P) y (.inr j)) = 0 := by
    funext y
    simp only [coordinateMetricFlux,
      blockDiagonal_inverse _ _ (isUnit_iff_ne_zero.mpr (hpA (P y)).ne') (isUnit_iff_ne_zero.mpr (hpB (Q y)).ne'),
      Fintype.sum_sum_type,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,Pi.zero_apply,
      zero_mul,Finset.sum_const_zero,zero_add,hd,hPb,map_zero,mul_zero]
  have hflux (i : ι) : Differentiable ℝ (fun y => coordinateMetricFlux a A u y i) := fun y =>
    (differentiableAt_pi.mp (differentiableAt_coordinateMetricFlux
      ((hu.of_le (show (2:WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) (hA y) (hpA y) a) i)
  have ha (i : ι) : fderiv ℝ (fun y => coordinateMetricFlux c
      (fun z => Matrix.fromBlocks (A (P z)) 0 0 (B (Q z))) (u ∘ P) y (.inl i)) x (c (.inl i)) =
      ρ x * fderiv ℝ (fun y => coordinateMetricFlux a A u y i) (P x) (a i) := by
    simp_rw [hf]
    change fderiv ℝ (ρ * ((fun y => coordinateMetricFlux a A u y i) ∘ P)) x _ = _
    rw [fderiv_mul (hρ x) ((hflux i (P x)).comp x P.differentiableAt)]
    rw [fderiv_comp x (hflux i (P x)) P.differentiableAt,P.fderiv]
    simp [ContinuousLinearMap.comp_apply,hρa,hPa]
  simp only [coordinateMetricLaplacian,Matrix.det_fromBlocks_zero₂₁,Fintype.sum_sum_type]
  simp_rw [ha,hv]
  simp only [fderiv_zero]
  rw [← Finset.mul_sum,Real.sqrt_mul (hpA (P x)).le]
  dsimp [ρ]
  have hn := (Real.sqrt_pos.mpr (hpB (Q x))).ne'
  field_simp
  simp
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_FourWaveThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
local instance fourChartThreeSmul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance fourChartFourSmul : ContinuousSMul ℝ FourModel := IsBoundedSMul.continuousSMul
local instance fourChartCircleSmul : ContinuousSMul ℝ (Euclidean 1) := IsBoundedSMul.continuousSMul
lemma four_chart_target (p : FourManifold) : (chartAt FourModel p).target=univ := by
  change (chartAt (Euclidean 2) p.1).target ×ˢ
    ((chartAt (Euclidean 1) p.2.1).target ×ˢ (chartAt (Euclidean 1) p.2.2).target)=univ
  have hc (z : Circle) : (chartAt (Euclidean 1) z).target=univ := by
    change (stereographic' 1 (-z)).target=univ
    exact stereographic'_target (-z)
  rw [sphere_chart_target,hc,hc,univ_prod_univ,univ_prod_univ]
lemma four_chart_symm_three (p : FourManifold) (y : FourModel) :
    fourToThree ((chartAt FourModel p).symm y)=
      (chartAt ThreeModel (fourToThree p)).symm (fourProjThree y) := by rfl
lemma four_chart_symm_circle (p : FourManifold) (y : FourModel) :
    fourToCircle ((chartAt FourModel p).symm y)=
      (chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y) := by rfl
lemma four_chart_three (p q : FourManifold) :
    fourProjThree (chartAt FourModel p q)=chartAt ThreeModel (fourToThree p) (fourToThree q) := by rfl
lemma four_chart_symm_smooth (p : FourManifold) :
    ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) ∞ (chartAt FourModel p).symm := by
  have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,FourModel)) (n:=∞) (x:=p)
  rwa [four_chart_target,contMDiffOn_univ] at h
lemma circle_chart_symm_smooth (p : Circle) :
    ContMDiff 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1) ∞ (chartAt (Euclidean 1) p).symm := by
  have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,Euclidean 1)) (n:=∞) (x:=p)
  have ht : (chartAt (Euclidean 1) p).target=univ := by
    change (stereographic' 1 (-p)).target=univ
    exact stereographic'_target (-p)
  rwa [ht,contMDiffOn_univ] at h
lemma four_chart_deriv_three (p : FourManifold) (y v : FourModel) :
    fourProjThree (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)=
      mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel (fourToThree p)).symm
        (fourProjThree y) (fourProjThree v) := by
  have hs : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) ∞ (chartAt ThreeModel (fourToThree p)).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,ThreeModel)) (n:=∞) (x:=fourToThree p)
    rwa [three_chart_target,contMDiffOn_univ] at h
  have h1 := mfderiv_comp y (fourToThree_smooth.mdifferentiable (by simp) _)
    ((four_chart_symm_smooth p).mdifferentiable (by simp) y)
  have he : fourToThree ∘ (chartAt FourModel p).symm =
      (chartAt ThreeModel (fourToThree p)).symm ∘ fourProjThree := funext (four_chart_symm_three p)
  rw [he,mfderiv_comp y (hs.mdifferentiable (by simp) _) fourProjThree.mdifferentiableAt] at h1
  have hh := congrArg (fun L => L v) h1
  change mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel (fourToThree p)).symm
      (fourProjThree y) (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourProjThree y v) =
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourToThree ((chartAt FourModel p).symm y)
      (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v) at hh
  have hp : (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourProjThree y :
      FourModel →L[ℝ] ThreeModel) = fourProjThree :=
    (mfderiv_eq_fderiv (f := (fourProjThree : FourModel → ThreeModel)) (x := y)).trans
      fourProjThree.fderiv
  have hm := mfderiv_fourToThree ((chartAt FourModel p).symm y)
    (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)
  exact hm.symm.trans (hh.symm.trans (congrArg
    (fun z : ThreeModel => mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel)
      (chartAt ThreeModel (fourToThree p)).symm (fourProjThree y) z)
    (congrArg (fun L : FourModel →L[ℝ] ThreeModel => L v) hp)))
lemma four_chart_deriv_circle (p : FourManifold) (y v : FourModel) :
    fourProjCircle (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)=
      mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1) (chartAt (Euclidean 1) (fourToCircle p)).symm
        (fourProjCircle y) (fourProjCircle v) := by
  have h1 := mfderiv_comp y (fourToCircle_smooth.mdifferentiable (by simp) _)
    ((four_chart_symm_smooth p).mdifferentiable (by simp) y)
  have he : fourToCircle ∘ (chartAt FourModel p).symm =
      (chartAt (Euclidean 1) (fourToCircle p)).symm ∘ fourProjCircle := funext (four_chart_symm_circle p)
  rw [he,mfderiv_comp y ((circle_chart_symm_smooth _).mdifferentiable (by simp) _) fourProjCircle.mdifferentiableAt] at h1
  have hh := congrArg (fun L => L v) h1
  change mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1) (chartAt (Euclidean 1) (fourToCircle p)).symm
      (fourProjCircle y) (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourProjCircle y v) =
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourToCircle ((chartAt FourModel p).symm y)
      (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v) at hh
  have hp : (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourProjCircle y :
      FourModel →L[ℝ] Euclidean 1) = fourProjCircle :=
    (mfderiv_eq_fderiv (f := (fourProjCircle : FourModel → Euclidean 1)) (x := y)).trans
      fourProjCircle.fderiv
  have hm := mfderiv_fourToCircle ((chartAt FourModel p).symm y)
    (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)
  exact hm.symm.trans (hh.symm.trans (congrArg
    (fun z : Euclidean 1 => mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1)
      (chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y) z)
    (congrArg (fun L : FourModel →L[ℝ] Euclidean 1 => L v) hp)))
lemma four_chartMetricForm (g : SmoothMetric ThreeModel ThreeManifold) (p : FourManifold)
    (y v w : FourModel) :
    chartMetricForm (fourProductMetric g) p y v w =
      chartMetricForm g (fourToThree p) (fourProjThree y) (fourProjThree v) (fourProjThree w)+
      chartMetricForm circleRoundMetric (fourToCircle p) (fourProjCircle y) (fourProjCircle v) (fourProjCircle w) := by
  rw [chartMetricForm_pairing,chartMetricForm_pairing,chartMetricForm_pairing]
  let D : FourModel →L[ℝ] FourModel :=
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y
  change fourProductInner g ((chartAt FourModel p).symm y) (D v) (D w) = _
  refine (fourProductInner_apply g ((chartAt FourModel p).symm y) (D v) (D w)).trans ?_
  change g.inner ((chartAt ThreeModel (fourToThree p)).symm (fourProjThree y))
      (fourProjThree (D v)) (fourProjThree (D w)) +
    circleRoundMetric.inner ((chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y))
      (fourProjCircle (D v)) (fourProjCircle (D w)) = _
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrArg₂ (fun a b : ThreeModel =>
      g.inner ((chartAt ThreeModel (fourToThree p)).symm (fourProjThree y)) a b)
      (four_chart_deriv_three p y v) (four_chart_deriv_three p y w))
    (congrArg₂ (fun a b : Euclidean 1 =>
      circleRoundMetric.inner ((chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y)) a b)
      (four_chart_deriv_circle p y v) (four_chart_deriv_circle p y w))
end


section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma fourSplitBasis_inl (i : CoordIndex ThreeModel) :
    fourSplitEquiv (fourSplitBasis (.inl i))=(Module.finBasis ℝ ThreeModel i,0) := by
  simp [fourSplitBasis,Module.Basis.prod_apply]
lemma fourSplitBasis_inr (i : CoordIndex (Euclidean 1)) :
    fourSplitEquiv (fourSplitBasis (.inr i))=(0,Module.finBasis ℝ (Euclidean 1) i) := by
  simp [fourSplitBasis,Module.Basis.prod_apply]
lemma fourSplitBasis_Pa (i : CoordIndex ThreeModel) : fourProjThree (fourSplitBasis (.inl i))=Module.finBasis ℝ ThreeModel i :=
  congrArg Prod.fst (fourSplitBasis_inl i)
lemma fourSplitBasis_Pb (i : CoordIndex (Euclidean 1)) : fourProjThree (fourSplitBasis (.inr i))=0 :=
  congrArg Prod.fst (fourSplitBasis_inr i)
lemma fourSplitBasis_Qa (i : CoordIndex ThreeModel) : fourProjCircle (fourSplitBasis (.inl i))=0 :=
  congrArg Prod.snd (fourSplitBasis_inl i)
lemma fourSplitBasis_Qb (i : CoordIndex (Euclidean 1)) : fourProjCircle (fourSplitBasis (.inr i))=Module.finBasis ℝ (Euclidean 1) i :=
  congrArg Prod.snd (fourSplitBasis_inr i)
lemma four_metric_block (g : SmoothMetric ThreeModel ThreeManifold) (p : FourManifold) (y : FourModel) :
    bilinearCoordinateMatrix fourSplitBasis (chartMetricForm (fourProductMetric g) p y)=
      Matrix.fromBlocks (metricCoefficients g (fourToThree p) (fourProjThree y)) 0 0
        (metricCoefficients circleRoundMetric (fourToCircle p) (fourProjCircle y)) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  all_goals simp only [bilinearCoordinateMatrix,four_chartMetricForm,fourSplitBasis_Pa,
    fourSplitBasis_Pb,fourSplitBasis_Qa,fourSplitBasis_Qb,map_zero,_root_.zero_apply,add_zero,zero_add,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply]
  all_goals first | rfl | (rw [chartMetricForm_pairing]; rfl)
lemma metricCoefficients_differentiable_univ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (g : SmoothMetric E M) (p : M) (ht : (chartAt E p).target=univ) :
    Differentiable ℝ (metricCoefficients g p) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  have h := contDiffOn_metricCoefficient g p i j
  rw [ht,contDiffOn_univ] at h
  exact h.differentiable (by simp)
lemma laplaceBeltrami_four_lift_oai (g : SmoothMetric ThreeModel ThreeManifold) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (p : FourManifold) :
    laplaceBeltrami (fourProductMetric g) (u ∘ fourToThree) p=laplaceBeltrami g u (fourToThree p) := by
  rw [laplaceBeltrami_any_basis_univ _ _ (four_chart_target p) fourSplitBasis (hu.comp fourToThree_smooth)]
  simp_rw [four_metric_block]
  have hfun : (u ∘ fourToThree) ∘ (chartAt FourModel p).symm =
      (u ∘ (chartAt ThreeModel (fourToThree p)).symm) ∘ fourProjThree := by
    funext y
    simp only [Function.comp_apply,four_chart_symm_three]
  rw [hfun]
  have ht : (chartAt (Euclidean 1) (fourToCircle p)).target=univ := by
    change (stereographic' 1 (-fourToCircle p)).target=univ
    exact stereographic'_target _
  have hs : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) ∞ (chartAt ThreeModel (fourToThree p)).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,ThreeModel)) (n:=∞) (x:=fourToThree p)
    rwa [three_chart_target,contMDiffOn_univ] at h
  rw [coordinateMetricLaplacian_split fourProjThree fourProjCircle
    (Module.finBasis ℝ ThreeModel) (Module.finBasis ℝ (Euclidean 1)) fourSplitBasis
    fourSplitBasis_Pa fourSplitBasis_Pb fourSplitBasis_Qa
    _ _ (metricCoefficients_differentiable_univ _ _ (three_chart_target _))
    (metricCoefficients_differentiable_univ _ _ ht)
    (fun y => metricCoefficients_det_pos _ _ (by rw [three_chart_target]; trivial))
    (fun y => metricCoefficients_det_pos _ _ (by rw [ht]; trivial))
    _ (contMDiff_iff_contDiff.mp (hu.comp hs))]
  rw [four_chart_three]
  rfl
end


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.laplaceBeltrami_four_lift_oai := @OAI.YauCounterexamples.laplaceBeltrami_four_lift_oai
