-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:30:11.287193+00:00
-- url     : https://prove2.me/submissions/a8fbf27b-38dd-42b9-b9d2-12bebbe2e330

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A028
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_intrinsic_test_det_bound

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma half_norm_sq_hasFDerivAt (p : E) :
    HasFDerivAt (fun v : E => ‖v‖^2/2) (innerSL ℝ p) p := by
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_smul (1/2:ℝ)
  convert! H using 1
  · ext v; simp only [Pi.smul_apply,smul_eq_mul,id_eq] <;> ring
  · ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      smul_apply,smul_eq_mul,innerSL_apply_apply,id_eq]
    ring

lemma half_norm_sq_fderiv :
    fderiv ℝ (fun v : E => ‖v‖^2/2) = innerSL ℝ := by
  funext p
  exact (half_norm_sq_hasFDerivAt p).fderiv

lemma half_norm_sq_second_fderiv (p a d : E) :
    fderiv ℝ (fderiv ℝ (fun v : E => ‖v‖^2/2)) p a d=inner ℝ a d := by
  rw [half_norm_sq_fderiv]
  rw [(innerSL ℝ).hasFDerivAt.fderiv]
  rfl

lemma half_norm_sq_contDiff : ContDiff ℝ ∞ (fun v : E => ‖v‖^2/2) := by
  simpa only [one_div,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    ((contDiff_norm_sq (𝕜 := ℝ) (E := E) (n := ∞)).const_smul (1/2:ℝ))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondFderivScalarComp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {φ : ℝ → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun h => φ (f h))) x ξ ξ =
      iteratedDeriv 2 φ (f x)*(fderiv ℝ f x ξ)^2+
        deriv φ (f x)*fderiv ℝ (fderiv ℝ f) x ξ ξ := by
  let g := fun t : ℝ => f (x+t • ξ)
  have hg : ContDiffAt ℝ 2 g 0 := by
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ => x+t • ξ) 0
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • ξ) from by simpa using hf).comp (0:ℝ)
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hg0 : g 0=f x := by simp [g]
  have hline : HasDerivAt (fun t : ℝ => x+t • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const ξ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hd : deriv g 0=fderiv ℝ f x ξ := by
    simpa only [Function.comp_def,g,zero_smul,add_zero] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • ξ) from by
        simpa only [zero_smul,add_zero] using (hf.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline).deriv
  have H := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (g 0) from hg0.symm ▸ hφ) hg
  rw [hg0,hd,show iteratedDeriv 2 g 0=fderiv ℝ (fderiv ℝ f) x ξ ξ from
    iteratedDeriv_two_affine_line hf ξ] at H
  change fderiv ℝ (fderiv ℝ (φ ∘ f)) x ξ ξ = _
  rw [←iteratedDeriv_two_affine_line (hφ.comp x hf) ξ]
  exact H

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarInverseJet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma exists_scalar_inverse_jet {φ : ℝ → ℝ} {v l : ℝ}
    (hφ : ContDiffAt ℝ 2 φ v) (hd : HasDerivAt φ l v) (hl : l≠0) :
    ∃ i : ℝ → ℝ, ContDiffAt ℝ 2 i (φ v) ∧ i (φ v)=v ∧
      HasDerivAt i l⁻¹ (φ v) ∧
      (∀ᶠ w in 𝓝 (φ v),φ (i w)=w) ∧
      iteratedDeriv 2 i (φ v)= -iteratedDeriv 2 φ v/l^3 := by
  let i := hφ.localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hi : ContDiffAt ℝ 2 i (φ v) := hφ.to_localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hiv : i (φ v)=v := hφ.localInverse_apply_image (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hr : ∀ᶠ w in 𝓝 (φ v),φ (i w)=w :=
    (hφ.hasStrictFDerivAt' (hd.hasFDerivAt_equiv hl) (by norm_num)).eventually_right_inverse
  have hiD : HasDerivAt i l⁻¹ (φ v) := (show HasDerivAt φ l (i (φ v)) from hiv.symm ▸ hd).of_local_left_inverse hi.continuousAt hl (by
    simpa only [hiv] using hr)
  refine ⟨i,hi,hiv,hiD,hr,?_⟩
  have hsecond := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (i (φ v)) from hiv.symm ▸ hφ) hi
  have hid : iteratedDeriv 2 (φ ∘ i) (φ v)=0 := by
    have H : (φ ∘ i)=ᶠ[𝓝 (φ v)] (fun w : ℝ => w) := hr
    have H2 := H.deriv.deriv_eq
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id'',deriv_const] using H2
  rw [hid,hiv,hd.deriv,hiD.deriv] at hsecond
  apply (eq_div_iff (pow_ne_zero 3 hl)).mpr
  field_simp at hsecond
  nlinarith only [hsecond]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scalar_inverse_lower_test {φ : ℝ → ℝ} (hmono : StrictMono φ)
    {v F : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ (v x))
    {l : ℝ} (hd : HasDerivAt φ l (v x)) (hl : l≠0)
    (hF : ContDiffAt ℝ 2 F x) (hval : F x=φ (v x))
    (hlo : ∀ᶠ y in 𝓝 x,F y≤φ (v y)) :
    ∃ f : E → ℝ, ContDiffAt ℝ 2 f x ∧ f x=v x ∧
      (∀ᶠ y in 𝓝 x,f y≤v y) ∧
      fderiv ℝ f x=l⁻¹ • fderiv ℝ F x ∧
      ∀ ξ : E, fderiv ℝ (fderiv ℝ f) x ξ ξ=
        l⁻¹*fderiv ℝ (fderiv ℝ F) x ξ ξ-
          (iteratedDeriv 2 φ (v x)/l^3)*(fderiv ℝ F x ξ)^2 := by
  obtain ⟨i,hi,hiv,hiD,hir,hi2⟩ := exists_scalar_inverse_jet hφ hd hl
  let f := i ∘ F
  have hiF : ContDiffAt ℝ 2 i (F x) := hval.symm ▸ hi
  have hiDF : HasDerivAt i l⁻¹ (F x) := hval.symm ▸ hiD
  refine ⟨f,hiF.comp x hF,by dsimp [f]; rw [hval,hiv],?_,?_,?_⟩
  · have hr' := hF.continuousAt.eventually (show ∀ᶠ a in 𝓝 (F x),φ (i a)=a by rwa [hval])
    filter_upwards [hlo,hr'] with y hy hry
    apply hmono.le_iff_le.mp
    simpa only [f,Function.comp_apply,hry] using hy
  · exact (hiDF.comp_hasFDerivAt x (hF.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  · intro ξ
    rw [show f=(fun y => i (F y)) from rfl,second_fderiv_scalar_comp hF hiF ξ,
      hval,hi2,hiD.deriv]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactJetCalculus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma continuous_linearized_det (J:F →L[ℝ] E) (H Q:E →L[ℝ] F) :
    Continuous (fun δ:ℝ=>|(J.comp (H-δ • Q)).det|) := by
  have hH:Continuous (fun δ:ℝ=>H-δ • Q):=continuous_const.sub (continuous_id.smul continuous_const)
  exact (ContinuousLinearMap.continuous_det.comp (continuous_const.clm_comp hH)).abs
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] in
lemma dualObjective_add_constants (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (a b : M →ᵇ ℝ) (k : ℝ) :
    dualObjective mu nu (a + BoundedContinuousFunction.const M (-k),
      b + BoundedContinuousFunction.const M k) = dualObjective mu nu (a,b) := by
  change (∫ x, (a x + -k) ∂mu) + (∫ y, (b y + k) ∂nu) = _
  rw [integral_add (a.integrable mu) (integrable_const _),
    integral_add (b.integrable nu) (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [dualObjective]
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EigenOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

lemma bilinearOperator_symmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w:E, B v w=B w v) : (bilinearOperator B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (bilinearOperator B v) w=inner ℝ v (bilinearOperator B w)
  calc
    _=B v w := bilinearOperator_inner B v w
    _=B w v := hB v w
    _=inner ℝ (bilinearOperator B w) v := (bilinearOperator_inner B w v).symm
    _=inner ℝ v (bilinearOperator B w) := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Aggregate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology BigOperators

namespace WeakMTWTransport

lemma symmetric_bilinear_eq_of_diagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ u v, A u v = A v u) (hB : ∀ u v, B u v = B v u)
    (hd : ∀ u, A u u = B u u) : A = B := by
  ext u v
  have H := hd (u+v)
  simp only [map_add,add_apply,hA v u,hB v u] at H
  linarith [hd u,hd v]

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_lower_of_unit (L : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v:E, ‖v‖=1 → c ≤ L v v) (v:E) : c*‖v‖^2 ≤ L v v := by
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : v=‖v‖ • w := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have H := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg ‖v‖)
  calc
    c*‖v‖^2 = ‖v‖^2*c := mul_comm _ _
    _ ≤ ‖v‖^2*L w w := H
    _ = L (‖v‖ • w) (‖v‖ • w) := by simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
    _ = L v v := by rw [←he]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveBilinearBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric

namespace WeakMTWTransport
section PositiveBilinearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bilinear_positive_baseline (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ m>0,∀ v : E,m*‖v‖^2≤B v v := by
  let S := sphere (0:E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hc : ContinuousOn (fun v:E => B v v) S :=
    (B.continuous.clm_apply continuous_id).continuousOn
  obtain ⟨m,hm,Hm⟩ : ∃ m>0,∀ v∈S,m≤B v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨v,hv,Hv⟩ := hS.exists_isMinOn hne hc
      have hn : ‖v‖=1 := by simpa only [S,mem_sphere,dist_zero_right] using hv
      have hp : 0 < B v v := hB v (by intro he; simp [he] at hn)
      exact ⟨B v v,hp,fun w hw => Hv hw⟩
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  exact ⟨m,hm,bilinear_lower_of_unit B (fun v hv => Hm v (by simpa only [S,mem_sphere,dist_zero_right] using hv))⟩

end PositiveBilinearBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section DividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma divided_hessian_decrease {a : M} {r ξ : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s<1) :
    hessianValue a (s • r) ξ/s ≤ hessianValue a (t • r) ξ/t := by
  rcases eq_or_lt_of_le hts with h | h
  · simp only [h,le_refl]
  by_cases hξ : ξ=0
  · subst ξ
    rw [hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr (ht.trans h) hs),
      hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr ht (h.trans hs))]
    simp only [map_zero,zero_div,le_refl]
  exact (divided_hessian_strict_decrease hr ht h hs hξ).le

lemma exists_divided_hessian_baseline {a : M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s0 : ℝ} (ht : 0 < t) (hts : t < s0) (hs0 : s0<1) :
    ∃ m>0,∀ s : ℝ,s0 ≤ s → s<1 → ∀ ξ : TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-hessianValue a (s • r) ξ/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := t⁻¹ • normalHessian a (t • r)-s0⁻¹ • normalHessian a (s0 • r)
  have hIDt := contracted_minimizer_mem_injectivityDomain hr ht (hts.trans hs0)
  have hIDs := contracted_minimizer_mem_injectivityDomain hr (ht.trans hts) hs0
  have hB (ξ : TangentSpace 𝓘(ℝ,Model n) a) : B ξ ξ=
      hessianValue a (t • r) ξ/t-hessianValue a (s0 • r) ξ/s0 := by
    rw [hessianValue_eq_normalHessian hIDt,hessianValue_eq_normalHessian hIDs]
    simp only [B,sub_apply,smul_apply,smul_eq_mul]
    ring
  obtain ⟨m,hm,Hm⟩ := exists_bilinear_positive_baseline B (fun ξ hξ => by
    rw [hB]
    exact sub_pos.mpr (divided_hessian_strict_decrease hr ht hts hs0 hξ))
  refine ⟨m,hm,?_⟩
  intro s hss hs1 ξ
  have H := Hm ξ
  rw [hB] at H
  have Hd := divided_hessian_decrease (ξ := ξ) hr (ht.trans hts) hss hs1
  linarith only [H,Hd]

end DividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BranchDividedBaseline
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchDividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_branch_hessian_inward_limit {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    (ξ : TangentSpace 𝓘(ℝ,Model n) a) :
    Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
      (𝓝 (fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ)) := by
  have H := cost_branch_normal_jets (r := r) (T := (1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs => contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have HH := (H.2.2 ξ).div (tendsto_id.mono_left nhdsWithin_le_nhds) (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
    (𝓝 ((fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a ((1:ℝ) • r))))) 0 ξ ξ / 1)) at HH
  simpa only [one_smul,div_one] using HH

lemma exists_branch_divided_baseline {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t:ℝ} (ht : 0 < t) (ht1 : t < 1)
    {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ m>0,∀ ξ:TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-
        fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ := by
  let s0 := (t+1)/2
  have hts : t < s0 := by dsimp [s0] <;> linarith
  have hs0 : s0 < 1 := by dsimp [s0] <;> linarith
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  refine ⟨m,hm,?_⟩
  intro ξ
  have H := ((tendsto_const_nhds (x := hessianValue a (t • r) ξ/t)).sub (cost_branch_hessian_inward_limit hr hG hagree ξ))
  apply ge_of_tendsto H
  filter_upwards [(eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs1
  exact Hm s hs.le hs1 ξ

end BranchDividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FixedJoinSpectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section FixedJoinSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]

local instance tangentFiniteSpectrum_ra515c2_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma tangent_finrank (x : M) : finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)=n :=
  finrank_euclideanSpace_fin
end FixedJoinSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_sub {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f a-g a)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ g) x v w := by
  have he : fderiv ℝ (fun a => f a-g a) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ f a-fderiv ℝ g a) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with a ha hb
    exact fderiv_fun_sub (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  rw [fderiv_fun_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rfl

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma symmetric_eigenvalue_pos {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hn : finrank ℝ E=n) (hpos : ∀ x:E, x≠0 → 0 < inner ℝ (A x) x) (i:Fin n) :
    0 < hA.eigenvalues hn i := by
  have H := hpos (hA.eigenvectorBasis hn i) ((hA.eigenvectorBasis hn).toBasis.ne_zero i)
  rw [hA.apply_eigenvectorBasis,real_inner_smul_left,real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).norm_eq_one] at H
  simpa using H
end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenteredQuadratic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CenteredQuadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centered_half_norm_sq_c2 (z : E) :
    ContDiff ℝ 2 (fun w : E => ‖w-z‖^2/2) :=
  (half_norm_sq_contDiff.comp (contDiff_id.sub contDiff_const)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

end CenteredQuadratic

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SecondFderivAdd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_add_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun w => f w+g w)) z =
      fderiv ℝ (fderiv ℝ f) z+fderiv ℝ (fderiv ℝ g) z := by
  have he : fderiv ℝ (fun w => f w+g w) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ f w+fderiv ℝ g w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with w hw hw'
    exact fderiv_fun_add (hw.differentiableAt (by norm_num)) (hw'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_QuadraticTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section QuadraticTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma diag_bilinear_c2 (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ 2 (fun h : E => B h h/2) := by
  convert! ((B.contDiff.clm_apply contDiff_id).const_smul (1/2:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  simp only [smul_eq_mul,id_eq]
  ring

lemma diag_bilinear_fderiv (B : E →L[ℝ] E →L[ℝ] ℝ) :
    fderiv ℝ (fun h:E => B h h/2) = fun h => (1/2:ℝ) • (B+B.flip) h := by
  funext h
  have H := (B.hasFDerivAt.clm_apply (hasFDerivAt_id h)).const_smul (1/2:ℝ)
  have hfun : ((1/2:ℝ) • (fun y:E => B y (id y)))=(fun y:E => B y y/2) := by
    ext y
    simp only [Pi.smul_apply,smul_eq_mul,id_eq]
    ring
  rw [hfun] at H
  rw [H.fderiv]
  ext d
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.id_apply,id_eq]

lemma diag_bilinear_second (B : E →L[ℝ] E →L[ℝ] ℝ) (d : E) :
    fderiv ℝ (fderiv ℝ (fun h:E => B h h/2)) 0 d d=B d d := by
  rw [diag_bilinear_fderiv]
  change fderiv ℝ ((1/2:ℝ) • (B+B.flip)) 0 d d=B d d
  rw [ContinuousLinearMap.fderiv]
  simp only [smul_apply,add_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

lemma HasLowerSecondTaylor.exists_smooth_minorant {f : E → ℝ}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor f l B) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : E → ℝ, ContDiffAt ℝ 2 q 0 ∧ q 0=f 0 ∧ fderiv ℝ q 0=l ∧
      (∀ᶠ h in 𝓝 0,q h≤f h) ∧
      ∀ d:E,fderiv ℝ (fderiv ℝ q) 0 d d = B d d-ε*‖d‖^2 := by
  let q : E → ℝ := fun h => f 0+l h+B h h/2-ε*(‖h‖^2/2)
  have hB : ContDiffAt ℝ 2 (fun h:E => B h h/2) 0 := (diag_bilinear_c2 B).contDiffAt
  have hn : ContDiffAt ℝ 2 (fun h:E => ‖h‖^2/2) 0 := by
    simpa only [sub_zero] using (centered_half_norm_sq_c2 (0:E)).contDiffAt
  have hc : ContDiffAt ℝ 2 (fun h:E => f 0+l h) 0 := contDiffAt_const.add l.contDiff.contDiffAt
  refine ⟨q,(hc.add hB).sub (contDiffAt_const.mul hn),by simp [q],?_,?_,?_⟩
  · rw [show q=(fun h => (f 0+l h+B h h/2)-ε*(‖h‖^2/2)) from rfl,
      fderiv_fun_sub ((hc.add hB).differentiableAt (by norm_num))
        ((contDiffAt_const.mul hn).differentiableAt (by norm_num)),
      fderiv_fun_add (hc.differentiableAt (by norm_num)) (hB.differentiableAt (by norm_num)),
      (l.hasFDerivAt.const_add (f 0)).fderiv,diag_bilinear_fderiv]
    have Hn := ((half_norm_sq_hasFDerivAt (0:E)).const_mul ε).fderiv
    rw [Hn]
    simp only [map_zero,smul_zero,add_zero,sub_zero]

  · filter_upwards [hf (ε/2) (by positivity)] with h hh
    dsimp only [q]
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro d
    rw [show q=(fun h => (f 0+l h+B h h/2)-ε*(‖h‖^2/2)) from rfl,
      second_fderiv_sub (hc.add hB) (contDiffAt_const.mul hn),
      second_fderiv_add_eq hc hB,add_apply,add_apply,second_fderiv_const_mul,diag_bilinear_second,
      half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq]
    have hlin : fderiv ℝ (fun h:E => f 0+l h)=fun _ => l := by
      funext h
      exact (l.hasFDerivAt.const_add (f 0)).fderiv
    rw [hlin,(hasFDerivAt_const l (0:E)).fderiv]
    simp only [zero_apply,zero_add]

end QuadraticTest
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_mem {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ normalizedDualPairs x0) :
    reverseNormalizedPair x0 uv ∈ normalizedDualPairs x0 := by
  change (uv.2 x0 + -uv.2 x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.1 y + uv.2 x0) x = uv.2 x + -uv.2 x0
    rw [cTransform_add_const uv.1.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.2
    change cTransform uv.1 x = uv.2 x at hh
    change cTransform uv.1 x - uv.2 x0 = uv.2 x + -uv.2 x0
    rw [hh]
    ring
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.2 y + -uv.2 x0) x = uv.1 x + uv.2 x0
    rw [cTransform_add_const uv.2.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.1
    change cTransform uv.2 x = uv.1 x at hh
    change cTransform uv.2 x - -uv.2 x0 = uv.1 x + uv.2 x0
    rw [hh]
    ring

lemma densityDualClass_reverse {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ densityDualClass vol lam cap x0) :
    reverseNormalizedPair x0 uv ∈ densityDualClass vol lam cap x0 := by
  obtain ⟨hnorm, rho0, rho1, hrho0, hrho1, hmin⟩ := huv
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨reverseNormalizedPair_mem hnorm, rho1, rho0, hrho1, hrho0, ?_⟩
  intro a b hab
  have hba : ∀ x y, 0 ≤ contactGap b a x y := by
    intro x y
    have hh := hab y x
    dsimp [contactGap] at hh ⊢
    rw [cost_symm y x] at hh
    linarith
  have hh := hmin b a hba
  rw [reverseNormalizedPair, dualObjective_add_constants]
  dsimp [dualObjective] at hh ⊢
  linarith

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PullbackDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Topology

namespace WeakMTWTransport
section PullbackDet
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterIntrinsicDet
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterIntrinsicDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance oiFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.exists_uniform_outer_normal_det_bound
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0 ≤ cap) :
    ∃K:ℝ,0<K ∧ ∀ (a:M) (r:TangentSpace 𝓘(ℝ,Model n) a) (G:M×M → ℝ) (l:ℝ),
      r∈minimizingVectors a →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (a,riemannianExp a r) →
      (∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 a) → HasDerivAt φ l (uv.1 a) → iteratedDeriv 2 φ (uv.1 a)≤0 →
      ∀H:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] ℝ,
      (∀d e,H d e=H e d) → (∀d,0≤H d d) →
      HasLowerSecondTaylor (fun w=>φ (uv.1 (riemannianExp a w))+
        G (riemannianExp a w,riemannianExp a r)) 0 H →
      ∃V:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=H d d+
          (l*hessianValue a (l⁻¹ • r) d-
            fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp a w,riemannianExp a r))) 0 d d)-
          (iteratedDeriv 2 φ (uv.1 a)/l^2)*(inner ℝ r d)^2) ∧
        expJacobian (n:=n) a (l⁻¹ • r)*V.det≤l^n*K := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_intrinsic_test_det_bound hlam hcap
  refine ⟨K,hK,?_⟩
  intro a r G l hr hG hagree hl x0 uv φ huv hmono hφ hd hconc H hHs hH hjet
  let E:=TangentSpace 𝓘(ℝ,Model n) a
  let c:E → ℝ:=fun w=>G (riemannianExp a w,riemannianExp a r)
  have hlp:0<l:=zero_lt_one.trans hl
  have ht:0<l⁻¹:=inv_pos.mpr hlp
  have ht1:l⁻¹<1:=(inv_lt_one₀ hlp).mpr hl
  have hp:=contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩:=exists_branch_divided_baseline hr ht ht1 hG hagree
  have hCJ:=cost_branch_normal_jets (r:=r) (T:=(1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs=>contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have hc:ContDiffAt ℝ 2 c 0:=by
    have hh:ContDiffAt ℝ ∞ c 0:=by simpa only [c,one_smul] using hCJ.1
    exact hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcD:fderiv ℝ c 0=innerSL ℝ (-r):=by simpa only [c,one_smul] using hCJ.2.1.fderiv
  let I:E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  let R:E →L[ℝ] E →L[ℝ] ℝ:=(innerSL ℝ r).smulRight (innerSL ℝ r)
  let W:E →L[ℝ] E →L[ℝ] ℝ:=H+l • normalHessian a (l⁻¹ • r)-fderiv ℝ (fderiv ℝ c) 0-
    (iteratedDeriv 2 φ (uv.1 a)/l^2) • R
  have hdiag:∀d,W d d=H d d+(l*hessianValue a (l⁻¹ • r) d-
      fderiv ℝ (fderiv ℝ c) 0 d d)-(iteratedDeriv 2 φ (uv.1 a)/l^2)*(inner ℝ r d)^2:=by
    intro d
    simp only [W,R,sub_apply,add_apply,
      smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,
      innerSL_apply_apply,hessianValue_eq_normalHessian hp]
    ring
  have hWs:∀d e,W d e=W e d:=by
    intro d e
    simp only [W,R,sub_apply,add_apply,
      smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,
      innerSL_apply_apply,hHs d e,normalHessian_symm hp d e,
      (hc.isSymmSndFDerivAt (by norm_num)).eq d e]
    ring
  have hbase:∀d,m*‖d‖^2≤W d d:=by
    intro d
    have HB:=Hm d
    change m*‖d‖^2≤hessianValue a (l⁻¹ • r) d/l⁻¹-fderiv ℝ (fderiv ℝ c) 0 d d at HB
    rw [div_inv_eq_mul,mul_comm (hessianValue _ _ _)] at HB
    have hs:0≤-(iteratedDeriv 2 φ (uv.1 a)/l^2)*(inner ℝ r d)^2:=
      mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (sq_nonneg _))) (sq_nonneg _)
    rw [hdiag]
    linarith only [HB,hH d,hs]
  let V:=bilinearOperator W
  have hVs:∀d e,inner ℝ (V d) e=inner ℝ d (V e):=bilinearOperator_symmetric hWs
  have hVp:∀d,d≠0 → 0 < inner ℝ (V d) d:=by
    intro d hd
    rw [show inner ℝ (V d) d=W d d from bilinearOperator_inner W d d]
    exact (mul_pos hm (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le (hbase d)
  refine ⟨V,hVs,hVp,?_,?_⟩
  · intro d
    exact (bilinearOperator_inner W d d).trans (hdiag d)
  have Hbound:∀ε:ℝ,0<ε → ε < m/2 →
      expJacobian (n:=n) a (l⁻¹ • r)* |(bilinearOperator (W-ε • I)).det|≤l^n*K:=by
    intro ε hε hεm
    obtain ⟨q,hq,hq0,hqD,hqlo,hqH⟩:=hjet.exists_smooth_minorant hε
    let F:E → ℝ:=fun w=>q w-c w
    have hF:ContDiffAt ℝ 2 F 0:=hq.sub hc
    have hF0:F 0=φ (uv.1 a):=by
      dsimp only [F,c]
      rw [hq0,riemannianExp_zero]
      ring
    have hFlo:∀ᶠ w in 𝓝 (0:E),F w≤φ (uv.1 (riemannianExp a w)):=by
      filter_upwards [hqlo] with w hw
      change q w≤φ (uv.1 (riemannianExp a w))+c w at hw
      dsimp only [F]
      linarith only [hw]
    have hFD:fderiv ℝ F 0=innerSL ℝ r:=by
      rw [show F=(fun w=>q w-c w) from rfl,
        fderiv_fun_sub (hq.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
        hqD,hcD,map_neg,zero_sub,neg_neg]
    obtain ⟨f,hf,hf0,hflo,hfD,hfH⟩:=scalar_inverse_lower_test
      (v:=fun w:E=>uv.1 (riemannianExp a w)) (x:=0) hmono
      (by simpa only [riemannianExp_zero] using hφ)
      (by simpa only [riemannianExp_zero] using hd) hlp.ne' hF
      (by simpa only [riemannianExp_zero] using hF0) hFlo
    have hfD':fderiv ℝ f 0=innerSL ℝ (l⁻¹ • r):=by rw [hfD,hFD,map_smul]
    let B:=fderiv ℝ (fderiv ℝ f) 0+normalHessian a (l⁻¹ • r)
    have Heq:∀d,l*(B d d)=W d d-ε*‖d‖^2:=by
      intro d
      simp only [B,add_apply]
      rw [hfH,show F=(fun w=>q w-c w) from rfl,second_fderiv_sub hq hc,hqH,hFD,hdiag,
        hessianValue_eq_normalHessian hp]
      simp only [riemannianExp_zero,innerSL_apply_apply]
      field_simp [hlp.ne']
      ring
    have hpos:∀d,(m/2/l)*‖d‖^2≤B d d:=by
      intro d
      apply (mul_le_mul_iff_right₀ hlp).mp
      rw [Heq]
      have he:l*((m/2/l)*‖d‖^2)=(m/2)*‖d‖^2:=by field_simp [hlp.ne']
      rw [he]
      nlinarith only [hbase d,mul_le_mul_of_nonneg_right hεm.le (sq_nonneg ‖d‖)]
    have Htest:=HK x0 a uv (l⁻¹ • r) f huv hp hf hfD'
      (by simpa only [riemannianExp_zero] using hf0.symm) hflo
      ⟨m/2/l,by positivity,by simpa only [B,add_apply,hessianValue_eq_normalHessian hp] using hpos⟩
    have Hop:bilinearOperator (W-ε • I)=l • bilinearOperator B:=by
      have HB:W-ε • I=l • B:=by
        apply symmetric_bilinear_eq_of_diagonal
        · intro d e
          change W d e-ε*inner ℝ d e=W e d-ε*inner ℝ e d
          rw [hWs,real_inner_comm d e]
        · intro d e
          simp only [B,add_apply,smul_apply,
            normalHessian_symm hp d e,(hf.isSymmSndFDerivAt (by norm_num)).eq d e]
        · intro d
          change W d d-ε*inner ℝ d d=l*B d d
          rw [real_inner_self_eq_norm_sq]
          exact (Heq d).symm
      rw [HB]
      ext d
      simp only [bilinearOperator,ContinuousLinearMap.comp_apply,smul_apply,map_smul]
    rw [Hop]
    change expJacobian (n:=n) a (l⁻¹ • r)* |(l • (bilinearOperator B).toLinearMap).det|≤_
    rw [LinearMap.det_smul,show Module.finrank ℝ E=n from tangent_finrank a,abs_mul,abs_of_pos (pow_pos hlp n)]
    nlinarith only [mul_le_mul_of_nonneg_left Htest (pow_pos hlp n).le]
  have hcont:Continuous (fun ε:ℝ=>expJacobian (n:=n) a (l⁻¹ • r)*
      |(bilinearOperator (W-ε • I)).det|):=by
    exact continuous_const.mul (continuous_linearized_det
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap W I)
  have hlim:= (hcont.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hz:W-(0:ℝ) • I=W:=by
    ext d e
    change W d e-0*inner ℝ d e=W d e
    ring
  have H:expJacobian (n:=n) a (l⁻¹ • r)* |V.det|≤l^n*K:=by
    apply le_of_tendsto (show Tendsto (fun ε:ℝ=>expJacobian (n:=n) a (l⁻¹ • r)*
      |(bilinearOperator (W-ε • I)).det|) (𝓝[>] 0) (𝓝 (expJacobian (n:=n) a (l⁻¹ • r)* |V.det|)) from
        by simpa only [hz,V] using hlim)
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ) < m/2 by positivity)).filter_mono nhdsWithin_le_nhds] with ε hε hεm
    exact Hbound ε hε hεm
  rw [abs_of_pos (symmetric_det_pos hVs hVp)] at H
  exact H

end OuterIntrinsicDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterIntrinsicSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterIntrinsicSecond
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance oisFinite_ra515c2_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma WeakMTW.exists_uniform_outer_normal_det_bound_second_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0 ≤ cap) :
    ∃K:ℝ,0<K ∧ ∀ (a:M) (r:TangentSpace 𝓘(ℝ,Model n) a) (G:M×M → ℝ) (l:ℝ),
      r∈minimizingVectors a →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (a,riemannianExp a r) →
      (∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.2 a) → HasDerivAt φ l (uv.2 a) → iteratedDeriv 2 φ (uv.2 a)≤0 →
      ∀H:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] ℝ,
      (∀d e,H d e=H e d) → (∀d,0≤H d d) →
      HasLowerSecondTaylor (fun w=>φ (uv.2 (riemannianExp a w))+
        G (riemannianExp a w,riemannianExp a r)) 0 H →
      ∃V:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=H d d+
          (l*hessianValue a (l⁻¹ • r) d-
            fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp a w,riemannianExp a r))) 0 d d)-
          (iteratedDeriv 2 φ (uv.2 a)/l^2)*(inner ℝ r d)^2) ∧
        expJacobian (n:=n) a (l⁻¹ • r)*V.det≤l^n*K := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_outer_normal_det_bound hlam hcap
  refine ⟨K,hK,?_⟩
  intro a r G l hr hG hagree hl x0 uv φ huv hmono hφ hd hconc H hHs hH hjet
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have heq (y:M):uv.2 x0+vu.1 y=uv.2 y:=by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 a):=
    ((heq a).symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hdψ:HasDerivAt ψ l (vu.1 a):=by
    have hd':HasDerivAt φ l (uv.2 x0+vu.1 a):=(heq a).symm ▸ hd
    simpa only [mul_one,Function.comp_def,ψ] using
      hd'.comp _ ((hasDerivAt_id _).const_add (uv.2 x0))
  have hec:iteratedDeriv 2 ψ (vu.1 a)=iteratedDeriv 2 φ (uv.2 a):=by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [heq]
  have HM:=HK a r G l hr hG hagree hl x0 vu ψ (densityDualClass_reverse hlam huv)
    (fun _ _ h=>hmono (by linarith)) hψ hdψ (by rw [hec]; exact hconc) H hHs hH
    (by simpa only [ψ,heq] using hjet)
  simpa only [hec] using HM
end OuterIntrinsicSecond
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second_oai.{u_1}
