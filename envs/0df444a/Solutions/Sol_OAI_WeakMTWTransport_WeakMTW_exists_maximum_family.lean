-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_maximum_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:53.250976+00:00
-- url     : https://prove2.me/submissions/57c75ef7-76f5-4e9d-be9e-ee9fb16f68cd

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
import Definitions.Def_OAIQ232A030

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberLog
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_⟩
  have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (continuousAt_extChartAt y).eventually
      ((e.open_target.mem_nhds (hep ▸ e.map_source hpe)))
  have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
    (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
  have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
    have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
      rw [hLy]; exact extChartAt_source_mem_nhds y)
    exact H
  filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
  apply d.injOn hzs hsz
  have HR := e.right_inv hzt
  rw [he] at HR
  exact HR

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
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

variable {M : Type*} [MetricSpace M]

lemma cost_nonneg (x y : M) : 0 ≤ cost x y := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

end WeakMTWTransport
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

lemma boundedCTransform_nonexpansive : LipschitzWith 1 (boundedCTransform (M := M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
  intro x
  rw [Real.dist_eq, abs_le]
  have hbound (a b : M →ᵇ ℝ) : cTransform a x - cTransform b x ≤ dist a b := by
    rw [sub_le_iff_le_add, cTransform_le_iff a.continuous]
    intro y
    have hg := cTransform_gap_nonneg b.continuous x y
    have hd := BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) y
    rw [Real.dist_eq, abs_le] at hd
    dsimp [contactGap] at hg
    linarith [hd.1]
  constructor
  · have hh := hbound w v
    rw [dist_comm w v] at hh
    change -dist v w ≤ cTransform v x - cTransform w x
    linarith
  · exact hbound v w

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualParameter
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

namespace ParameterVariation

section
open Set Filter
open scoped Topology BigOperators

lemma abs_le_of_positive_barycentric {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m L : ι → ℝ} {U : ℝ} (hm : ∀ i, 0 < m i)
    (hs : ∑ i, m i = 1) (hcancel : ∑ i, m i * L i = 0)
    (hU : 0 ≤ U) (hupper : ∀ i, L i ≤ U) (i : ι) :
    |L i| ≤ U / m i := by
  have hmi : m i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => (hm j).le) (Finset.mem_univ i)
  have hdef : ∑ j, m j * (U - L j) = U := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, hcancel]
    ring
  have hsingle : m i * (U - L i) ≤ U := by
    exact (Finset.single_le_sum (fun j _ => mul_nonneg (hm j).le (sub_nonneg.mpr (hupper j)))
      (Finset.mem_univ i)).trans_eq hdef
  apply (le_div_iff₀ (hm i)).mpr
  rw [mul_comm, ← abs_of_pos (hm i), ← abs_mul, abs_le]
  constructor
  · nlinarith [mul_nonneg (hm i).le hU]
  · exact (mul_le_mul_of_nonneg_left (hupper i) (hm i).le).trans
      (by nlinarith)

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_span_projection_bound (a : ι → E) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : E, ∀ R : ℝ, 0 ≤ R →
      (∀ i, |inner ℝ (a i) x| ≤ R) →
      ‖(Submodule.span ℝ (range a)).starProjection x‖ ≤ K * R := by
  let S := Submodule.span ℝ (range a)
  let A : S →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i =>
    (innerSL ℝ (a i)).toLinearMap.comp S.subtype
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have horth : ∀ z ∈ S, inner ℝ z (x : E) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨i,rfl⟩ := hz
          exact congrFun hx i
      | zero => simp
      | add x y hx hy hix hiy => simp [inner_add_left, hix, hiy]
      | smul r x hx hix => simp [inner_smul_left, hix]
    apply Subtype.ext
    exact inner_self_eq_zero.mp (horth x x.property)
  obtain ⟨K,hK,hA⟩ := A.injective_iff_antilipschitz.mp hinj
  refine ⟨K,by exact_mod_cast hK,?_⟩
  intro x R hR hx
  have heval (i : ι) : A (S.orthogonalProjectionOnto x) i = inner ℝ (a i) x := by
    change inner ℝ (a i) ((S.orthogonalProjectionOnto x : S) : E) = _
    exact S.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨a i,Submodule.subset_span (mem_range_self i)⟩ x
  have hn : ‖A (S.orthogonalProjectionOnto x)‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    simpa only [heval i, Real.norm_eq_abs] using hx i
  have H := hA.le_mul_dist (S.orthogonalProjectionOnto x) 0
  simp only [map_zero, dist_zero_right] at H
  simpa only [Submodule.norm_coe, Submodule.starProjection_apply] using
    H.trans (mul_le_mul_of_nonneg_left hn K.coe_nonneg)

lemma exists_eventual_active_projection_bound {T : Type*} {l : Filter T}
    (a : ι → E) {m : ι → ℝ} (hm : ∀ i, 0 < m i)
    (hs : ∑ i, m i = 1) (hbar : ∑ i, m i • a i = 0)
    {h : T → ℝ} {d : T → E} {C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ᶠ k in l, 0 ≤ h k)
    (ha : ∀ᶠ k in l, ∀ i, inner ℝ (a i) (d k) ≤ C*h k) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k in l,
      ‖(Submodule.span ℝ (range a)).starProjection (d k)‖ ≤ K*h k := by
  classical
  let R := ∑ i, C/m i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => div_nonneg hC (hm i).le)
  obtain ⟨K,hK,hproj⟩ := exists_span_projection_bound a
  refine ⟨K*R+1,by positivity,?_⟩
  filter_upwards [hh,ha] with k hhk hak
  have hcancel : ∑ i, m i * inner ℝ (a i) (d k) = 0 := by
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using
      congrArg (fun x => inner ℝ x (d k)) hbar
  have hforms : ∀ i, |inner ℝ (a i) (d k)| ≤ R*h k := by
    intro i
    have H := abs_le_of_positive_barycentric hm hs hcancel (mul_nonneg hC hhk) hak i
    calc
      |inner ℝ (a i) (d k)| ≤ C*h k/m i := H
      _ = (C/m i)*h k := by ring
      _ ≤ R*h k := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => div_nonneg hC (hm j).le) (Finset.mem_univ i)) hhk
  calc
    ‖(Submodule.span ℝ (range a)).starProjection (d k)‖ ≤ K*(R*h k) :=
      hproj (d k) (R*h k) (mul_nonneg hR hhk) hforms
    _ ≤ (K*R+1)*h k := by nlinarith only [hhk]

omit [FiniteDimensional ℝ E] in
lemma exists_eventual_active_linear_bound {T : Type*} {l : Filter T}
    (a : ι → E) (B : ι → ℝ) (Q : ι → E →L[ℝ] E →L[ℝ] ℝ)
    {h U : T → ℝ} {d : T → E} {e : ι → T → ℝ} {H K : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hh : ∀ᶠ k in l, 0 < h k)
    (hd : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k)
    (hU : ∀ᶠ k in l, U k ≤ H*h k)
    (he : ∀ i, Tendsto (fun k => e i k/h k) l (𝓝 0))
    (hcontact : ∀ᶠ k in l, ∀ i,
      h k*B i+inner ℝ (a i) (d k)+Q i (d k) (d k)/2+e i k ≤ U k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in l, ∀ i, inner ℝ (a i) (d k) ≤ C*h k := by
  classical
  let X := ∑ i, |B i|
  let Y := ∑ i, ‖Q i‖
  have hX : 0 ≤ X := Finset.sum_nonneg (fun i _ => abs_nonneg (B i))
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => norm_nonneg (Q i))
  refine ⟨H+X+Y*K/2+1,by positivity,?_⟩
  have he' : ∀ᶠ k in l, ∀ i, -1 < e i k/h k :=
    eventually_all.mpr (fun i => (he i).eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0)))
  filter_upwards [hh,hd,hU,he',hcontact] with k hhk hdk hUk hek hck i
  have hiX : |B i| ≤ X := Finset.single_le_sum
    (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)
  have hiY : ‖Q i‖ ≤ Y := Finset.single_le_sum
    (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ i)
  have hBi := mul_le_mul_of_nonneg_left ((neg_le_neg hiX).trans (neg_abs_le (B i))) hhk.le
  have hQi : |Q i (d k) (d k)| ≤ Y*K*h k := by
    calc
      |Q i (d k) (d k)| ≤ ‖Q i‖*‖d k‖*‖d k‖ := (Q i).le_opNorm₂ (d k) (d k)
      _ = ‖Q i‖*‖d k‖^2 := by ring
      _ ≤ ‖Q i‖*(K*h k) := mul_le_mul_of_nonneg_left hdk (norm_nonneg (Q i))
      _ ≤ Y*(K*h k) := mul_le_mul_of_nonneg_right hiY (mul_nonneg hK hhk.le)
      _ = Y*K*h k := by ring
  have hei : -h k ≤ e i k := by
    have HT := (lt_div_iff₀ hhk).mp (hek i)
    linarith only [HT]
  have hQi' := (abs_le.mp hQi).1
  nlinarith only [hck i,hUk,hBi,hQi',hei]

lemma projected_quadratic_lower (S : Submodule ℝ E)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hQ : ∀ v ∈ Sᗮ, 0 ≤ Q v v) (x : E) :
    -‖Q‖ * (2 * ‖S.starProjection x‖ * ‖x‖ + ‖S.starProjection x‖ ^ 2) ≤ Q x x := by
  let e := S.starProjection x
  have hp := hQ (x-e) (S.sub_starProjection_mem_orthogonal x)
  simp only [map_sub, sub_apply] at hp
  have h1 := (abs_le.mp (show |Q x e| ≤ ‖Q‖*‖x‖*‖e‖ from Q.le_opNorm₂ x e)).1
  have h2 := (abs_le.mp (show |Q e x| ≤ ‖Q‖*‖e‖*‖x‖ from Q.le_opNorm₂ e x)).1
  have h3 := (abs_le.mp (show |Q e e| ≤ ‖Q‖*‖e‖*‖e‖ from Q.le_opNorm₂ e e)).2
  change -‖Q‖ * (2*‖e‖*‖x‖+‖e‖^2) ≤ Q x x
  nlinarith only [hp,h1,h2,h3]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_tendsto_zero_of_sq_bound {T : Type*} {l : Filter T}
    {h : T → ℝ} {d : T → E} {K : ℝ}
    (hh : Tendsto h l (𝓝 0))
    (hb : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k) :
    Tendsto (fun k => ‖d k‖) l (𝓝 0) := by
  have H := squeeze_zero' (Eventually.of_forall (fun k => sq_nonneg ‖d k‖)) hb
    (show Tendsto (fun k => K*h k) l (𝓝 0) by simpa using hh.const_mul K)
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using H.sqrt

lemma weighted_parameter_bound {T : Type*} {l : Filter T} [l.NeBot]
    (a : ι → E) (B : ι → ℝ) (Q : ι → E →L[ℝ] E →L[ℝ] ℝ)
    {m : ι → ℝ} (hm : ∀ i, 0 < m i) (hs : ∑ i, m i = 1)
    (hbar : ∑ i, m i • a i = 0)
    {h U e0 : T → ℝ} {d : T → E} {e : ι → T → ℝ} {K D : ℝ}
    (hK : 0 ≤ K) (hh : ∀ᶠ k in l, 0 < h k) (hh0 : Tendsto h l (𝓝 0))
    (hd : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k)
    (he : ∀ i, Tendsto (fun k => e i k/h k) l (𝓝 0))
    (he0 : Tendsto (fun k => e0 k/h k) l (𝓝 0))
    (hupper : ∀ᶠ k in l, U k ≤ h k*D+e0 k)
    (hcontact : ∀ᶠ k in l, ∀ i,
      h k*B i+inner ℝ (a i) (d k)+Q i (d k) (d k)/2+e i k ≤ U k)
    (hQ : ∀ v ∈ (Submodule.span ℝ (range a))ᗮ, 0 ≤ (∑ i, m i • Q i) v v) :
    ∑ i, m i*B i ≤ D := by
  classical
  let S := Submodule.span ℝ (range a)
  let Qt := ∑ i, m i • Q i
  have hU : ∀ᶠ k in l, U k ≤ (|D|+1)*h k := by
    filter_upwards [hh,hupper,he0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
      with k hhk huk hek
    have he' := (div_lt_iff₀ hhk).mp hek
    have hD := mul_le_mul_of_nonneg_left (le_abs_self D) hhk.le
    nlinarith only [huk,he',hD]
  obtain ⟨C,hC,hlinear⟩ := exists_eventual_active_linear_bound a B Q
    (by positivity : 0 ≤ |D|+1) hK hh hd hU he hcontact
  obtain ⟨Kp,hKp,hproj⟩ := exists_eventual_active_projection_bound a hm hs hbar hC
    (hh.mono fun _ hk => hk.le) hlinear
  let δ := fun k => ‖Qt‖*(2*Kp*‖d k‖+Kp^2*h k)
  have hd0 := norm_tendsto_zero_of_sq_bound hh0 hd
  have hδ0 : Tendsto δ l (𝓝 0) := by
    simpa only [mul_zero,add_zero,δ] using
      ((hd0.const_mul (2*Kp)).add (hh0.const_mul (Kp^2))).const_mul ‖Qt‖
  let err := fun k => ∑ i, m i*(e i k/h k)
  have herr0 : Tendsto err l (𝓝 0) := by
    simpa only [mul_zero,Finset.sum_const_zero,err] using
      tendsto_finsetSum Finset.univ (fun i _ => (he i).const_mul (m i))
  have hlim : Tendsto (fun k => D+e0 k/h k-err k+δ k/2) l (𝓝 D) := by
    simpa using ((he0.const_add D).sub herr0).add (hδ0.div_const 2)
  apply ge_of_tendsto hlim
  filter_upwards [hh,hproj,hcontact,hupper] with k hhk hpk hck huk
  have hform : -δ k*h k ≤ Qt (d k) (d k) := by
    have hq := projected_quadratic_lower S Qt hQ (d k)
    have hP : 0 ≤ ‖S.starProjection (d k)‖ := norm_nonneg _
    have hPN : 0 ≤ Kp*h k := mul_nonneg hKp.le hhk.le
    have hPsq := mul_self_le_mul_self hP hpk
    have hcross := mul_le_mul_of_nonneg_right hpk (norm_nonneg (d k))
    have hb : 2*‖S.starProjection (d k)‖*‖d k‖+‖S.starProjection (d k)‖^2 ≤
        (2*Kp*‖d k‖+Kp^2*h k)*h k := by
      change ‖S.starProjection (d k)‖ ≤ Kp*h k at hpk
      nlinarith only [hPsq,hcross]
    have H := neg_le_neg (mul_le_mul_of_nonneg_left hb (norm_nonneg Qt))
    calc
      -δ k*h k = -(‖Qt‖*((2*Kp*‖d k‖+Kp^2*h k)*h k)) := by dsimp [δ] <;> ring
      _ ≤ -‖Qt‖*(2*‖S.starProjection (d k)‖*‖d k‖+‖S.starProjection (d k)‖^2) := by
        simpa only [neg_mul] using H
      _ ≤ Qt (d k) (d k) := hq
  have hcancel : ∑ i, m i*inner ℝ (a i) (d k) = 0 := by
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using
      congrArg (fun x => inner ℝ x (d k)) hbar
  have hQt : Qt (d k) (d k) = ∑ i, m i*Q i (d k) (d k) := by
    simp only [Qt,sum_apply,smul_apply,smul_eq_mul]
  have havg : h k*(∑ i, m i*B i)+Qt (d k) (d k)/2+∑ i, m i*e i k ≤ U k := by
    have H := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (hck i) (hm i).le)
    have heq : (∑ i, m i*(h k*B i+inner ℝ (a i) (d k)+Q i (d k) (d k)/2+e i k)) =
        h k*(∑ i, m i*B i)+Qt (d k) (d k)/2+∑ i, m i*e i k := by
      calc
        _ = ∑ i, (h k*(m i*B i)+m i*inner ℝ (a i) (d k)+
            (m i*Q i (d k) (d k))/2+m i*e i k) := by
          apply Finset.sum_congr rfl; intro i _; ring
        _ = _ := by
          simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,hcancel,add_zero,hQt]
    rw [heq,←Finset.sum_mul,hs,one_mul] at H
    exact H
  have herr : err k*h k = ∑ i, m i*e i k := by
    dsimp only [err]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc,div_mul_cancel₀ _ hhk.ne']
  apply (mul_le_mul_iff_left₀ hhk).mp
  have hrem : h k*(D+e0 k/h k-err k+δ k/2) =
      h k*D+e0 k-∑ i, m i*e i k+δ k*h k/2 := by
    rw [mul_add,mul_sub,mul_add,mul_div_cancel₀ _ hhk.ne',mul_comm (h k) (err k),herr]
    ring
  rw [mul_comm (∑ i, m i * B i) (h k),
    mul_comm (D + e0 k / h k - err k + δ k / 2) (h k), hrem]
  nlinarith only [havg,hform,huk]

end

open Set Filter
open scoped Topology

lemma compact_minimizers_tendsto {M T : Type*} [TopologicalSpace M] [CompactSpace M]
    {l : Filter T} {f : M → ℝ} (hf : Continuous f) {x : M}
    (hmin : ∀ y, f x ≤ f y) (hunique : ∀ y, f y = f x → y = x)
    {u : T → M} (hval : Tendsto (fun k => f (u k)) l (𝓝 (f x))) :
    Tendsto u l (𝓝 x) := by
  rw [tendsto_nhds]
  intro s hs hxs
  by_cases he : sᶜ.Nonempty
  · obtain ⟨y,hy,hym⟩ := hs.isClosed_compl.isCompact.exists_isMinOn he hf.continuousOn
    have hstrict : f x < f y := lt_of_le_of_ne (hmin y) (by
      intro h
      have hyx := hunique y h.symm
      exact hy (hyx ▸ hxs))
    filter_upwards [hval.eventually (gt_mem_nhds hstrict)] with k hk
    by_contra hn
    exact (not_le_of_gt hk) (hym hn)
  · filter_upwards [] with k
    by_contra hn
    exact he ⟨u k,hn⟩

lemma perturbed_compact_minimizers_tendsto {M T : Type*}
    [TopologicalSpace M] [CompactSpace M] {l : Filter T}
    {f : M → ℝ} (hf : Continuous f) {x : M}
    (hmin : ∀ y, f x ≤ f y) (hunique : ∀ y, f y = f x → y = x)
    {u : T → M} {h : T → ℝ} {K : ℝ}
    (hh0 : Tendsto h l (𝓝 0))
    (hbound : ∀ᶠ k in l, f (u k) ≤ f x + K*h k) :
    Tendsto u l (𝓝 x) := by
  apply compact_minimizers_tendsto hf hmin hunique
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hh0))
    (Eventually.of_forall (fun k => hmin (u k))) hbound

lemma affine_minimum_derivative {M T : Type*}
    [TopologicalSpace M] [CompactSpace M] {l : Filter T}
    {f B : M → ℝ} (hf : Continuous f) (hB : Continuous B) {x : M}
    (hmin : ∀ y, f x ≤ f y) (hunique : ∀ y, f y = f x → y = x)
    {u : T → M} {h : T → ℝ}
    (hh : ∀ᶠ k in l, 0 < h k) (hh0 : Tendsto h l (𝓝 0))
    (hu : ∀ᶠ k in l, ∀ y, f (u k)-h k*B (u k) ≤ f y-h k*B y) :
    Tendsto (fun k => (f (u k)-h k*B (u k)-f x)/h k) l (𝓝 (-B x)) := by
  obtain ⟨K,hK⟩ := (isCompact_univ.image hB).bddAbove
  have hbound : ∀ᶠ k in l, f (u k) ≤ f x+(K-B x)*h k := by
    filter_upwards [hh,hu] with k hhk huk
    have HK := hK (mem_image_of_mem B (mem_univ (u k)))
    have H := huk x
    nlinarith only [H,mul_le_mul_of_nonneg_left HK hhk.le]
  have hconv := perturbed_compact_minimizers_tendsto hf hmin hunique hh0 hbound
  have hlim : Tendsto (fun k => -B (u k)) l (𝓝 (-B x)) :=
    (hB.continuousAt.tendsto.comp hconv).neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [hh] with k hhk
    apply (le_div_iff₀ hhk).mpr
    have H := hmin (u k)
    nlinarith only [H]
  · filter_upwards [hh,hu] with k hhk huk
    apply (div_le_iff₀ hhk).mpr
    have H := huk x
    nlinarith only [H]

lemma second_remainder_along_sqrt {E T : Type*} [NormedAddCommGroup E]
    {l : Filter T} {R : E → ℝ} {d : T → E} {h : T → ℝ} {K : ℝ}
    (hR : R =o[𝓝 0] (fun v : E => ‖v‖^2))
    (hd0 : Tendsto d l (𝓝 0)) (hh : ∀ᶠ k in l, 0 ≤ h k)
    (hd : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k) :
    Tendsto (fun k => R (d k)/h k) l (𝓝 0) := by
  have HO : (fun k => ‖d k‖^2) =O[l] h := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨K,?_⟩
    filter_upwards [hh,hd] with k hk hd'
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖d k‖)),abs_of_nonneg hk] using hd'
  exact ((hR.comp_tendsto hd0).trans_isBigO HO).tendsto_div_nhds_zero

end ParameterVariation

open Set Filter Manifold Bundle
open scoped Topology ContDiff

open ParameterVariation

section CompactEnvelopes
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma modified_outer_decrease_bounds {v : M → ℝ} (hv : Continuous v)
    {a D b h H : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (hh : 0 ≤ h) (hbound : ∀ s, 0 ≤ B s ∧ B s ≤ H) (x : M) :
    0 ≤ cTransform (modifiedDatum v a D (b-h) B) x-
      cTransform (modifiedDatum v a D b B) x ∧
    cTransform (modifiedDatum v a D (b-h) B) x-
      cTransform (modifiedDatum v a D b B) x ≤ h*H := by
  have hw := continuous_modifiedDatum hv a D b hB
  have hw' := continuous_modifiedDatum hv a D (b-h) hB
  have H1 := cTransform_antitone hw' hw (fun y => by
    dsimp only [modifiedDatum]
    nlinarith only [mul_nonneg hh (hbound ((v y-a)/D)).1]) x
  have H2 := cTransform_antitone (v := fun y => modifiedDatum v a D b B y + (-h*H))
    (hw.add continuous_const) hw' (fun y => by
    dsimp only [modifiedDatum]
    nlinarith only [mul_le_mul_of_nonneg_left (hbound ((v y-a)/D)).2 hh]) x
  rw [cTransform_add_const hw] at H2
  constructor <;> linarith only [H1,H2]

end CompactEnvelopes

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.hopfLax_minimizer_unique (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {z x y : M}
    (hx : hopfLax t (cTransform v) z=cTransform v x+cost x z/t)
    (hy : hopfLax t (cTransform v) z=cTransform v y+cost y z/t) : x=y := by
  obtain ⟨p,hp,hpz⟩ := exists_minimizing_vector (n := n) x z
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) y z
  have hpx : t⁻¹ • p∈normalSubdifferential (n := n) (cTransform v) x := by
    apply global_min_divided_cost_subgradient hp ht
    intro w
    rw [hpz,←hx]
    exact hopfLax_le (continuous_cTransform hv) t z w
  have hqy : t⁻¹ • q∈normalSubdifferential (n := n) (cTransform v) y := by
    apply global_min_divided_cost_subgradient hq ht
    intro w
    rw [hqz,←hy]
    exact hopfLax_le (continuous_cTransform hv) t z w
  let X : subgradientGraph (n := n) (cTransform v) := ⟨⟨x,t⁻¹ • p⟩,hpx⟩
  let Y : subgradientGraph (n := n) (cTransform v) := ⟨⟨y,t⁻¹ • q⟩,hqy⟩
  have hXY : graphProjection (cTransform v) t X=graphProjection (cTransform v) t Y := by
    dsimp only [graphProjection,X,Y]
    rw [smul_smul,smul_smul,mul_inv_cancel₀ ht.ne',one_smul,one_smul,hpz,hqz]
  exact congrArg (fun w : subgradientGraph (n := n) (cTransform v) => w.1.1)
    (hmtw.injective_graphProjection hv ht ht1 hXY)

lemma modified_active_split_contact {v : M → ℝ} (hv : Continuous v)
    {a D b h t q : ℝ} {B : ℝ → ℝ} (hB : Continuous B) {x z x' : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hact : contactGap (cTransform (modifiedDatum v a D b B))
      (modifiedDatum v a D b B) x (riemannianExp x p)=0)
    (hq : 0<q) (hq1 : q<1) :
    h*B ((v (riemannianExp x p)-a)/D)+
      (cost x' z-cost x z)/t-
      (cost x' (riemannianExp x (q • p))-cost x (riemannianExp x (q • p)))/q ≤
      (cTransform (modifiedDatum v a D (b-h) B) x'+cost x' z/t)-
      (cTransform (modifiedDatum v a D b B) x+cost x z/t) := by
  have Hg := cTransform_gap_nonneg (continuous_modifiedDatum hv a D (b-h) hB)
    x' (riemannianExp x p)
  have Hs := minimizing_split_upper_support hp hq hq1 x'
  have Hx := minimizing_split_contact hp hq hq1
  dsimp only [contactGap,modifiedDatum] at hact Hg
  simp only [sub_div] at hact Hg Hs Hx ⊢
  nlinarith only [Hg,Hs,Hx,hact]

lemma WeakMTW.modified_pole_movement (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b t H : ℝ}
    {B : ℝ → ℝ} (hB : Continuous B) (hbound : ∀ s, 0 ≤ B s ∧ B s ≤ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i=1)
    (hmin : ∀ i, p i∈minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform (modifiedDatum v a D b B))
      (modifiedDatum v a D b B) x (riemannianExp x (p i))=0)
    (ht : 0<t) (ht1 : t<1) :
    let z := riemannianExp x (t • (∑ i, m i • p i))
    hopfLax t (cTransform (modifiedDatum v a D b B)) z =
      cTransform (modifiedDatum v a D b B) x+cost x z/t ∧
    ∃ X : ℝ → M, ∃ d : ℝ → TangentSpace 𝓘(ℝ,Model n) x, ∃ K : ℝ,
      0 ≤ K ∧
      (∀ h, hopfLax t (cTransform (modifiedDatum v a D (b-h) B)) z=
        cTransform (modifiedDatum v a D (b-h) B) (X h)+cost (X h) z/t) ∧
      Tendsto X (𝓝[>] 0) (𝓝 x) ∧ Tendsto d (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ h in 𝓝[>] 0, riemannianExp x (d h)=X h ∧ ‖d h‖^2≤K*h := by
  classical
  dsimp only
  let r := ∑ i, m i • p i
  let z := riemannianExp x (t • r)
  let w := modifiedDatum v a D b B
  let g : ℝ → M → ℝ := fun β => cTransform (modifiedDatum v a D β B)
  have hw : Continuous w := continuous_modifiedDatum hv a D b hB
  have hg : ∀ β, Continuous (g β) := fun β =>
    continuous_cTransform (continuous_modifiedDatum hv a D β hB)
  have hAS : range p ⊆ activeLogs (n := n) w x := by
    rintro _ ⟨i,rfl⟩
    exact ⟨hmin i,hactive i⟩
  have hr : r∈convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hm i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  have hrsub := active_hull_subset_normalSubdifferential hw x ((convexHull_mono hAS) hr)
  let G : subgradientGraph (n := n) (cTransform w) := ⟨⟨x,r⟩,hrsub⟩
  have hval : hopfLax t (g b) z=g b x+cost x z/t := by
    exact hmtw.hopfLax_graph_value hw ht ht1 G
  refine ⟨hval,?_⟩
  have hID : ∀ q∈convexHull ℝ (range p), t • q∈injectivityDomain x :=
    fun q hq => hmtw.active_hull_precut hw ht ht1 x q ((convexHull_mono hAS) hq)
  obtain ⟨β,hβ,hgrowth⟩ := hmtw.active_local_growth hw p m hm hsum hmin hactive ht ht1 hID
  choose X hX hXmin using (fun h : ℝ => exists_hopfLax_minimizer (hg (b-h)) t z)
  let f : M → ℝ := fun y => g b y+cost y z/t
  have hf : Continuous f := (hg b).add ((continuous_cost_left z).div_const t)
  have hfmin : ∀ y, f x ≤ f y := by
    intro y
    have H := hopfLax_le (hg b) t z y
    rwa [hval] at H
  have hfunique : ∀ y, f y=f x → y=x := by
    intro y hy
    exact hmtw.hopfLax_minimizer_unique hw ht ht1 (hval.trans hy.symm) hval
  have hXbound : ∀ᶠ h : ℝ in 𝓝[>] 0, f (X h)≤f x+H*h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have HL := modified_outer_decrease_bounds (a := a) (D := D) (b := b) hv hB (le_of_lt hh) hbound (X h)
    have HR := modified_outer_decrease_bounds (a := a) (D := D) (b := b) hv hB (le_of_lt hh) hbound x
    have HM := hXmin h x
    change g (b-h) (X h)+cost (X h) z/t≤g (b-h) x+cost x z/t at HM
    change 0 ≤ g (b-h) (X h)-g b (X h) ∧ _ at HL
    change 0 ≤ g (b-h) x-g b x ∧ _ at HR
    change g b (X h)+cost (X h) z/t≤g b x+cost x z/t+H*h
    linarith only [HL.1,HR.2,HM]
  have hh0 : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hX0 : Tendsto X (𝓝[>] 0) (𝓝 x) :=
    perturbed_compact_minimizers_tendsto hf hfmin hfunique hh0 hXbound
  obtain ⟨L,hL,hLx,hLi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) x)
  simp only [riemannianExp_zero] at hL hLx hLi
  let d : ℝ → TangentSpace 𝓘(ℝ,Model n) x := fun h => L (X h)
  have hd0 : Tendsto d (𝓝[>] 0) (𝓝 0) := by
    rw [←hLx]
    exact hL.continuousAt.tendsto.comp hX0
  have hdrep : ∀ᶠ h : ℝ in 𝓝[>] 0, riemannianExp x (d h)=X h :=
    hX0.eventually hLi
  have hH : 0 ≤ H := (hbound 0).1.trans (hbound 0).2
  refine ⟨X,d,H/β,div_nonneg hH hβ.le,hX,hX0,hd0,?_⟩
  filter_upwards [hdrep,hd0.eventually hgrowth,hXbound] with h hrep hgr hbo
  refine ⟨hrep,?_⟩
  rw [hrep] at hgr
  change β*‖d h‖^2≤g b (X h)-g b x+(cost (X h) z-cost x z)/t at hgr
  change g b (X h)+cost (X h) z/t≤g b x+cost x z/t+H*h at hbo
  rw [sub_div] at hgr
  apply (mul_le_mul_iff_left₀ hβ).mp
  calc ‖d h‖^2*β ≤ H*h := by nlinarith only [hgr,hbo]
       _ = H/β*h*β := by field_simp

lemma WeakMTW.modified_prefix_weighted_bound (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b t H U : ℝ}
    {B : ℝ → ℝ} (hB : Continuous B) (hbound : ∀ s, 0 ≤ B s ∧ B s ≤ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i=1)
    (hmin : ∀ i, p i∈minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform (modifiedDatum v a D b B))
      (modifiedDatum v a D b B) x (riemannianExp x (p i))=0)
    (ht : 0<t) (ht1 : t<1) {e0 : ℝ → ℝ}
    (he0 : Tendsto (fun h => e0 h/h) (𝓝[>] 0) (𝓝 0))
    (hupper : let z := riemannianExp x (t • (∑ i, m i • p i))
      ∀ᶠ h in 𝓝[>] 0,
        hopfLax t (cTransform (modifiedDatum v a D (b-h) B)) z-
        hopfLax t (cTransform (modifiedDatum v a D b B)) z≤h*U+e0 h) :
    ∑ i, m i*B ((v (riemannianExp x (p i))-a)/D) ≤ U := by
  classical
  let E := TangentSpace 𝓘(ℝ,Model n) x
  let : FiniteDimensional ℝ E := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let r := ∑ i, m i • p i
  let z := riemannianExp x (t • r)
  let w := modifiedDatum v a D b B
  have hw : Continuous w := continuous_modifiedDatum hv a D b hB
  have hAS : range p ⊆ activeLogs (n := n) w x := by
    rintro _ ⟨i,rfl⟩
    exact ⟨hmin i,hactive i⟩
  have hr : r∈convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hm i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  have hID : ∀ q∈convexHull ℝ (range p), t • q∈injectivityDomain x :=
    fun q hq => hmtw.active_hull_precut hw ht ht1 x q ((convexHull_mono hAS) hq)
  have hrt := hID r hr
  obtain ⟨q,htq,hq1⟩ := exists_between ht1
  have hq : 0<q := ht.trans htq
  have hqi : ∀ i, q • p i∈injectivityDomain x :=
    fun i => contracted_minimizer_mem_injectivityDomain (hmin i) hq hq1
  let f : ι → E → ℝ := fun i d =>
    t⁻¹*(normalCost x (t • r) d-normalCost x (t • r) 0)-
    q⁻¹*(normalCost x (q • p i) d-normalCost x (q • p i) 0)
  let A : ι → E := fun i => p i-r
  let Q : ι → E →L[ℝ] E →L[ℝ] ℝ := fun i => fderiv ℝ (fderiv ℝ (f i)) 0
  have hleft : ContDiffAt ℝ 2 (normalCost x (t • r)) 0 :=
    (normalCost_contDiffAt hrt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hright : ∀ i, ContDiffAt ℝ 2 (normalCost x (q • p i)) 0 :=
    fun i => (normalCost_contDiffAt (hqi i)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := fun i =>
    (contDiffAt_const.mul (hleft.sub contDiffAt_const)).sub
      (contDiffAt_const.mul ((hright i).sub contDiffAt_const))
  have hf0 : ∀ i, f i 0=0 := fun i => by simp only [f,sub_self,mul_zero]
  have hfirst : ∀ i, fderiv ℝ (f i) 0=innerSL ℝ (A i) := by
    intro i
    have HD := (((normalCost_hasFDerivAt_zero hrt).sub_const
      (normalCost x (t • r) 0)).const_smul t⁻¹).sub
      (((normalCost_hasFDerivAt_zero (hqi i)).sub_const
        (normalCost x (q • p i) 0)).const_smul q⁻¹)
    have HD' : HasFDerivAt (f i) (innerSL ℝ (A i)) 0 := by
      apply HD.congr_fderiv
      ext v
      simp only [A,sub_apply,smul_apply,innerSL_apply_apply,inner_neg_left,
        real_inner_smul_left,inner_sub_left,smul_eq_mul]
      field_simp [ht.ne',hq.ne']
      ring
    exact HD'.fderiv
  have hsecond : ∀ i v, Q i v v=
      hessianValue x (t • r) v/t-hessianValue x (q • p i) v/q := by
    intro i v
    dsimp only [Q,f]
    rw [second_fderiv_scaled_differences hleft (hright i)]
    rw [hessianValue_eq_normalHessian hrt,hessianValue_eq_normalHessian (hqi i)]
    simp only [normalHessian,div_eq_mul_inv]
    ring
  have hbar : ∑ i, m i • A i=0 := by
    simp only [A,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul,r,sub_self]
  have hQ : ∀ v∈(Submodule.span ℝ (range A))ᗮ, 0 ≤ (∑ i, m i • Q i) v v := by
    intro v hv
    by_cases hv0 : v=0
    · simp [hv0]
    have horth : ∀ i, inner ℝ v (p i-r)=0 := by
      intro i
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp hv (A i)
        (Submodule.subset_span (mem_range_self i))
    have HS := hmtw.finite_transverse_slack_strict p m hm hsum hmin ht htq hq1 hID hv0 horth
    have HQ : (∑ i, m i • Q i) v v=
        hessianValue x (t • r) v/t-∑ i, m i*(hessianValue x (q • p i) v/q) := by
      simp only [sum_apply,smul_apply,smul_eq_mul,hsecond,mul_sub,Finset.sum_sub_distrib,
        ←Finset.sum_mul,hsum,one_mul]
    rw [HQ]
    exact (sub_pos.mpr HS).le
  obtain ⟨hval,X,d,K,hK,hX,hX0,hd0,hd⟩ :=
    hmtw.modified_pole_movement hv hB hbound p m hm hsum hmin hactive ht ht1
  let V : ℝ → ℝ := fun h => hopfLax t (cTransform (modifiedDatum v a D (b-h) B)) z-
    hopfLax t (cTransform (modifiedDatum v a D b B)) z
  let e : ι → ℝ → ℝ := fun i h => f i (d h)-inner ℝ (A i) (d h)-Q i (d h) (d h)/2
  have HE : ∀ i, Tendsto (fun h => e i h/h) (𝓝[>] 0) (𝓝 0) := by
    intro i
    have HR := contDiffAt_second_order_remainder (hf i)
    simp only [hf0,sub_zero,hfirst,innerSL_apply_apply] at HR
    have Hres := second_remainder_along_sqrt (d := d) (h := fun h : ℝ => h) HR hd0
      (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 ≤ h from
        (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin).mono (fun _ h => h.le))
      (hd.mono (fun _ h => h.2))
    exact Hres
  have HC : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i,
      h*B ((v (riemannianExp x (p i))-a)/D)+inner ℝ (A i) (d h)+
        Q i (d h) (d h)/2+e i h≤V h := by
    filter_upwards [hd] with h hdh i
    have HS := modified_active_split_contact hv hB (hmin i) (hactive i)
      hq hq1 (t := t) (h := h) (z := z) (x' := X h)
    rw [←hX h,←hval] at HS
    change h*B ((v (riemannianExp x (p i))-a)/D)+
      (cost (X h) z-cost x z)/t-
      (cost (X h) (riemannianExp x (q • p i))-cost x (riemannianExp x (q • p i)))/q≤V h at HS
    rw [←hdh.1] at HS
    have HF : f i (d h)=(cost (riemannianExp x (d h)) z-cost x z)/t-
        (cost (riemannianExp x (d h)) (riemannianExp x (q • p i))-
          cost x (riemannianExp x (q • p i)))/q := by
      simp only [f,normalCost,riemannianExp_zero,z,div_eq_mul_inv,mul_comm]
    dsimp only [e]
    rw [HF]
    linarith only [HS]
  exact weighted_parameter_bound (l := 𝓝[>] (0 : ℝ)) (h := fun h : ℝ => h) A (fun i => B ((v (riemannianExp x (p i))-a)/D)) Q
    hm hsum hbar hK (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin)
    (tendsto_id.mono_right nhdsWithin_le_nhds) (hd.mono (fun _ h => h.2)) HE he0 hupper HC hQ

lemma WeakMTW.modified_parameter_inequality
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b bplus t H : ℝ}
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo)
    (hbound : ∀ s, 0 ≤ Bo s ∧ Bo s ≤ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] {x y : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i=1)
    (hmin : ∀ i, p i∈minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform (modifiedDatum v a D b Bo))
      (modifiedDatum v a D b Bo) x (riemannianExp x (p i))=0)
    (ht : 0<t) (ht1 : t<1) (hb : 0≤b) (hbp : 0<bplus)
    (hcenter : let z := riemannianExp x (t • (∑ i, m i • p i))
      ∀ w, hopfLax (1-t) (modifiedDatum v a D b Bc) z =
        modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=y)
    (hmax : let z := riemannianExp x (t • (∑ i, m i • p i))
      ∀ᶠ β in 𝓝 b, regularizedComparison v a D bplus t Bc Bo (β,z)≤
        regularizedComparison v a D bplus t Bc Bo (b,z)) :
    1/4096+4*b/bplus ≤ Bc ((v y-a)/D)-∑ i, m i*Bo ((v (riemannianExp x (p i))-a)/D) ∧
      (1:ℝ)/4096 ≤ 1/4096+4*b/bplus := by
  classical
  let z := riemannianExp x (t • (∑ i, m i • p i))
  let C : ℝ → ℝ := fun β => hopfLax (1-t) (modifiedDatum v a D β Bc) z
  let f : M → ℝ := fun w => modifiedDatum v a D b Bc w+cost w z/(1-t)
  let G : M → ℝ := fun w => Bc ((v w-a)/D)
  have hf : Continuous f := (continuous_modifiedDatum hv a D b hc).add
    ((continuous_cost_left z).div_const (1-t))
  have hG : Continuous G := hc.comp ((hv.sub continuous_const).div_const D)
  have hcval : C b=f y := (hcenter y).mpr rfl
  have hfmin : ∀ w, f y≤f w := by
    intro w
    rw [←hcval]
    exact hopfLax_le (continuous_modifiedDatum hv a D b hc) (1-t) z w
  have hfunique : ∀ w, f w=f y → w=y := fun w hw =>
    (hcenter w).mp (hcval.trans hw.symm)
  choose Y hY hYmin using (fun h : ℝ =>
    exists_hopfLax_minimizer (continuous_modifiedDatum hv a D (b-h) hc) (1-t) z)
  have hh : ∀ᶠ h : ℝ in 𝓝[>] 0, 0<h := self_mem_nhdsWithin
  have hh0 : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have HCY : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ w, f (Y h)-h*G (Y h)≤f w-h*G w := by
    apply Eventually.of_forall
    intro h w
    have H := hYmin h w
    dsimp only [f,G,modifiedDatum] at H ⊢
    linarith only [H]
  have HC0 : Tendsto (fun h => (C (b-h)-C b)/h) (𝓝[>] 0) (𝓝 (-G y)) := by
    have H := affine_minimum_derivative hf hG hfmin hfunique hh hh0 HCY
    apply H.congr'
    apply Eventually.of_forall
    intro h
    dsimp only [C]
    rw [hY h,show hopfLax (1-t) (modifiedDatum v a D b Bc) z=f y from hcval]
    dsimp only [f,G,modifiedDatum]
    congr 1
    ring
  let dP := (1:ℝ)/4096+4*b/bplus
  have HP0 : Tendsto (fun h => (parameterPenalty bplus (b-h)-parameterPenalty bplus b)/h)
      (𝓝[>] 0) (𝓝 (-dP)) := by
    have H : Tendsto (fun h : ℝ => 2*h/bplus-dP) (𝓝[>] 0) (𝓝 (-dP)) := by
      simpa using ((tendsto_const_nhds.mul hh0).div_const bplus).sub tendsto_const_nhds
    apply H.congr'
    filter_upwards [hh] with h hpos
    dsimp only [parameterPenalty,dP]
    field_simp [hpos.ne',hbp.ne']
    ring
  let U := G y-dP
  let e0 : ℝ → ℝ := fun h => parameterPenalty bplus (b-h)-parameterPenalty bplus b-
    (C (b-h)-C b)-h*U
  have HE0 : Tendsto (fun h => e0 h/h) (𝓝[>] 0) (𝓝 0) := by
    have H := (HP0.sub HC0).sub (tendsto_const_nhds (x := U))
    have H' : Tendsto (fun h =>
        (parameterPenalty bplus (b-h)-parameterPenalty bplus b)/h-
        (C (b-h)-C b)/h-U) (𝓝[>] 0) (𝓝 0) := by
      have hlimit : -dP - -G y - U = 0 := by dsimp only [U] <;> ring
      simpa only [hlimit] using H
    apply H'.congr'
    filter_upwards [hh] with h hpos
    dsimp only [e0]
    field_simp [hpos.ne']
  have hb0 : Tendsto (fun h : ℝ => b-h) (𝓝[>] 0) (𝓝 b) := by
    simpa using tendsto_const_nhds.sub hh0
  have HU : ∀ᶠ h : ℝ in 𝓝[>] 0,
      hopfLax t (cTransform (modifiedDatum v a D (b-h) Bo)) z-
        hopfLax t (cTransform (modifiedDatum v a D b Bo)) z≤h*U+e0 h := by
    filter_upwards [hb0.eventually hmax] with h hmh
    dsimp only [regularizedComparison] at hmh
    dsimp only [e0,C]
    linarith only [hmh]
  have Hlow := hmtw.modified_prefix_weighted_bound hv ho hbound p m hm hsum hmin hactive ht ht1 HE0 HU
  constructor
  · change dP≤G y-_
    change _≤G y-dP at Hlow
    linarith only [Hlow]
  · have Hpos : 0≤4*b/bplus := div_nonneg (mul_nonneg (by norm_num) hb) hbp.le
    linarith only [Hpos]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_HopfApproximation
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
open scoped Topology NNReal

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma hopfLax_le_self {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z : M) :
    hopfLax t u z ≤ u z := by
  simpa only [cost,dist_self,zero_pow (by norm_num : 2≠0),zero_div,add_zero] using hopfLax_le hu t z z

lemma hopfLax_short_approx {u : M → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {t : ℝ} (ht : 0<t) (z : M) :
    u z-(L:ℝ)^2*t/2 ≤ hopfLax t u z ∧ hopfLax t u z ≤ u z := by
  refine ⟨?_,hopfLax_le_self hu.continuous t z⟩
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer hu.continuous t z
  have H := hu.dist_le_mul x z
  rw [Real.dist_eq] at H
  have H1 := (abs_le.mp H).1
  rw [hx,cost]
  apply (mul_le_mul_iff_left₀ ht).mp
  have he : (u x+dist x z^2/2/t)*t=u x*t+dist x z^2/2 := by field_simp
  rw [he]
  have H2 := mul_le_mul_of_nonneg_right H1 ht.le
  nlinarith only [H2,sq_nonneg (dist x z-(L:ℝ)*t)]

lemma hopfLax_time_comparison {u : M → ℝ} (hu : Continuous u) {H : ℝ}
    (hH : ∀ x y : M, cost x y ≤ H) (t s : ℝ) (z : M) :
    |hopfLax t u z-hopfLax s u z| ≤ H*|1/t-1/s| := by
  have hbound : ∀ x : M, |cost x z/t-cost x z/s| ≤ H*|1/t-1/s| := by
    intro x
    calc
      _=|cost x z*(1/t-1/s)| := by congr 1; ring
      _=cost x z*|1/t-1/s| := by rw [abs_mul,abs_of_nonneg (cost_nonneg x z)]
      _≤H*|1/t-1/s| := mul_le_mul_of_nonneg_right (hH x z) (abs_nonneg _)
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer hu t z
  obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hu s z
  have Hx := hopfLax_le hu s z x
  have Hy := hopfLax_le hu t z y
  have Bx := (abs_le.mp (hbound x)).1
  have By := (abs_le.mp (hbound y)).2
  rw [abs_le]
  constructor <;> linarith only [hx,hy,Hx,Hy,Bx,By]

lemma hopfLax_one (u : M → ℝ) (hu : Continuous u) :
    hopfLax 1 u=fun z => -cTransform u z := by
  funext z
  simpa only [one_mul,div_one] using hopfLax_eq_neg_transform hu (by norm_num : (0:ℝ)<1) z

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_Alignment
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
lemma hopfLax_derivative_of_scaled_minimizer {u : M → ℝ} (hu : Continuous u)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (hp : t • p∈minimizingVectors x)
    (heq : hopfLax t u (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 =
      u x+cost x (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) := by
  let w : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let z := sprayFlow t w
  obtain ⟨ε,hε,hεt,_,_,Hε⟩ := exists_two_short_legs x p ht
    (show t<t+1 by linarith) zero_lt_one
  have hshort := (Filter.Eventually.self_of_nhds Hε).2.2.2
  let a := (sprayFlow (t-ε) w).1
  let G : M → ℝ := fun y => u x+cost x a/(t-ε)+cost a y/ε
  have hG : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) G z.1 (innerSL ℝ z.2) := by
    have H := (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ))
      (u x+cost x a/(t-ε)) z.1).add (hshort.const_smul ε⁻¹)
    have heD : 0+ε⁻¹ • innerSL ℝ (ε • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) =
        innerSL ℝ z.2 := by
      ext v
      simp only [zero_add,_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,
        real_inner_smul_left]
      dsimp [z,w]
      field_simp
    replace H := H.congr_mfderiv heD
    have heG : G = ((fun _ => u x+cost x a/(t-ε)) +
        ε⁻¹ • fun y => dist (sprayFlow (t-ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 y^2/2) := by
      funext y
      dsimp [G,cost,a,w]
      ring
    rw [heG]
    exact H
  have hmin : dist x z.1=t*‖p‖ := by
    dsimp [z,w]
    rw [←riemannianExp_smul,hp,norm_smul,
      Real.norm_eq_abs,abs_of_pos ht]
  have hleft : dist x a=(t-ε)*‖p‖ :=
    sprayFlow_minimizing_prefix w (sub_pos.mpr hεt).le (by linarith) hmin
  have hright : dist a z.1=ε*‖p‖ := by
    have H := sprayFlow_minimizing_subinterval w (sub_pos.mpr hεt).le (by linarith) hmin
    simpa only [sub_sub_cancel] using H
  have hcontact : hopfLax t u z.1=G z.1 := by
    rw [heq]
    dsimp [G,cost]
    rw [hmin,hleft,hright]
    field_simp
    ring
  have hle : ∀ y, hopfLax t u y≤G y := by
    intro y
    have H := cost_divided_triangle_two_times x a y (sub_pos.mpr hεt) hε
    rw [sub_add_cancel] at H
    exact (hopfLax_le hu t y x).trans (by dsimp [G] <;> linarith)
  exact hd.hasMFDerivAt.congr_mfderiv
    ((upper_contact_mfderiv hd hG.mdifferentiableAt (Filter.Eventually.of_forall hle) hcontact).trans hG.mfderiv)

lemma hopfLax_backward_minimizer {u : M → ℝ} (hu : Continuous u)
    {t : ℝ} (ht : 0<t) {x z : M}
    (hval : hopfLax t u z=u x+cost x z/t)
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) z) :
    (sprayFlow (-t) (⟨z,riemannianGradient (hopfLax t u) z⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)).1=x := by
  obtain ⟨p,hp,hpz⟩ := exists_minimizing_vector (n := n) x z
  let q := t⁻¹ • p
  have hq : t • q∈minimizingVectors x := by
    simpa only [q,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hp
  have hz : (sprayFlow t (⟨x,q⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rw [←riemannianExp_smul]
    simpa only [q,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hpz
  have H := hopfLax_derivative_of_scaled_minimizer hu ht hq (hz ▸ hval) (hz ▸ hd)
  have HG := riemannianGradient_eq_of_derivative H
  have HB : (⟨z,riemannianGradient (hopfLax t u) z⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      sprayFlow t (⟨x,q⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    rw [←hz,HG]
  rw [HB,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma gradients_cancel_at_local_max {f g : M → ℝ} {z : M}
    (hf : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z)
    (hg : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) g z)
    (hmax : ∀ᶠ a in 𝓝 z,f a+g a≤f z+g z) :
    riemannianGradient g z= -riemannianGradient (n := n) f z := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) z) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  have H := upper_contact_mfderiv (hf.add hg)
    (mdifferentiableAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ))) hmax rfl
  rw [(hasMFDerivAt_riemannianGradient hf).add
    (hasMFDerivAt_riemannianGradient hg) |>.mfderiv,
    (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ)) (f z+g z) z).mfderiv] at H
  have HE : riemannianGradient (n := n) f z+riemannianGradient (n := n) g z=0 := by
    apply ext_inner_right ℝ
    intro u
    have H0 := congrArg (fun L => L u) H
    change inner ℝ (riemannianGradient f z) u+inner ℝ (riemannianGradient g z) u=0 at H0
    simpa only [inner_add_left,inner_zero_left] using H0
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using HE)

lemma WeakMTW.hopf_maximum_aligned (hmtw : WeakMTW (n := n) (M := M))
    {w v : M → ℝ} (hw : Continuous w) (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x y z : M}
    (hx : hopfLax t (cTransform w) z=cTransform w x+cost x z/t)
    (hy : hopfLax (1-t) v z=v y+cost y z/(1-t))
    (hdy : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax (1-t) v) z)
    (hmax : ∀ᶠ a in 𝓝 z,hopfLax t (cTransform w) a+hopfLax (1-t) v a≤
      hopfLax t (cTransform w) z+hopfLax (1-t) v z) :
    ∃ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈normalSubdifferential (cTransform w) x ∧ p∈minimizingVectors x ∧
      z=riemannianExp x (t • p) ∧ y=riemannianExp x p ∧
      hopfLax t (cTransform w) z+hopfLax (1-t) v z=v y-cTransform (cTransform w) y := by
  let g := cTransform w
  have hg : Continuous g := continuous_cTransform hw
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) x z
  let p := t⁻¹ • q
  have hps : p∈normalSubdifferential g x := by
    apply global_min_divided_cost_subgradient hq ht
    intro a
    rw [hqz,←hx]
    exact hopfLax_le hg t z a
  obtain ⟨hp,hfull⟩ := hmtw.global_support hw hps
  have hpz : riemannianExp x (t • p)=z := by
    simpa only [p,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hqz
  have hPz : (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rwa [←riemannianExp_smul]
  have hdg := hmtw.mdifferentiable_hopfLax hg (continuous_cTransform hg)
    (show IsCostDualPair g (cTransform g) from ⟨(cTransform_triple hw).symm,rfl⟩) ht ht1 z
  have hneg := gradients_cancel_at_local_max hdg hdy hmax
  have hder := hopfLax_derivative_of_minimizer hg hp ht ht1.le (hPz ▸ hx) (hPz ▸ hdg)
  have HG := riemannianGradient_eq_of_derivative hder
  have HU : (⟨z,riemannianGradient (hopfLax t g) z⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    rw [←hPz,HG]
  have HV : (⟨z,riemannianGradient (hopfLax (1-t) v) z⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      tangentScale (-1) (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) := by
    rw [←HU]
    simp only [tangentScale,neg_one_smul,hneg]
  have hback := hopfLax_backward_minimizer hv (sub_pos.mpr ht1) hy hdy
  rw [HV,sprayFlow_scale] at hback
  change (sprayFlow ((-1)*(-(1-t))) (sprayFlow t
    (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))).1=y at hback
  rw [←sprayFlow_add,show (-1)*(-(1-t))+t=1 by ring,←riemannianExp_eq_sprayFlow] at hback
  have hpy : y=riemannianExp x p := hback.symm
  refine ⟨p,hps,hp,hpz.symm,hpy,?_⟩
  have hright : dist z y=(1-t)*‖p‖ := by
    rw [←hpz,hpy,riemannianExp_smul,riemannianExp_eq_sprayFlow]
    exact sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      ht.le ht1.le (by rw [one_mul,←riemannianExp_eq_sprayFlow]; exact hp)
  have hcost : cost y z/(1-t)=(1-t)*‖p‖^2/2 := by
    rw [cost,dist_comm,hright]
    field_simp
  have hsum := minimizing_split_contact hp ht ht1
  rw [hpz,←hpy] at hsum
  have hval1 : -cTransform g y=g x+cost x y := by
    have H := hopfLax_eq_of_min hg 1 y x (by simpa only [hpy,div_one] using hfull)
    simpa only [hopfLax_one _ hg,div_one] using H
  rw [hx,hy,hcost]
  change g x+cost x z/t+(v y+(1-t)*‖p‖^2/2)=v y-cTransform g y
  linarith only [hsum,hval1]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_InteriorMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
lemma continuous_boundedModifiedDatum (v : M → ℝ) (hv : Continuous v) (a D : ℝ)
    (B : ℝ → ℝ) (hB : Continuous B) : Continuous (boundedModifiedDatum v hv a D B hB) :=
  continuous_const.add (continuous_id.smul continuous_const)

lemma continuous_cTransform_family {X : Type*} [TopologicalSpace X]
    {U : X → M →ᵇ ℝ} (hU : Continuous U) :
    Continuous (fun q : X×M => cTransform (U q.1) q.2) := by
  exact continuous_eval.comp ((boundedCTransform_nonexpansive.continuous.comp
    (hU.comp continuous_fst)).prodMk continuous_snd)

lemma continuous_hopfLax_family {X : Type*} [TopologicalSpace X]
    {U : X → M →ᵇ ℝ} (hU : Continuous U) {t : ℝ} (ht : 0<t) :
    Continuous (fun q : X×M => hopfLax t (U q.1) q.2) := by
  have H := (continuous_cTransform_family ((continuous_const : Continuous (fun _ : X => t)).smul hU)).neg.div_const t
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  exact hopfLax_eq_neg_transform (U q.1).continuous ht q.2

lemma continuous_regularizedComparison {v : M → ℝ} (hv : Continuous v)
    (a D bplus : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo) :
    Continuous (regularizedComparison v a D bplus t Bc Bo) := by
  have H1 := continuous_hopfLax_family
    (boundedCTransform_nonexpansive.continuous.comp
      (continuous_boundedModifiedDatum v hv a D Bo ho)) ht
  have H2 := continuous_hopfLax_family
    (continuous_boundedModifiedDatum v hv a D Bc hc) (sub_pos.mpr ht1)
  have HP : Continuous (fun q : ℝ×M => parameterPenalty bplus q.1) := by
    unfold parameterPenalty
    fun_prop
  exact (H1.add H2).sub HP

lemma regularizedComparison_error {v : M → ℝ} (hv : Continuous v)
    {a D bplus t b H : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    {L : ℝ≥0} (hc : LipschitzWith L (modifiedDatum v a D b Bc))
    (hH : ∀ x y : M,cost x y≤H) (_ : 0<t) (ht1 : t<1) (z : M) :
    |regularizedComparison v a D bplus t Bc Bo (b,z)-
      (modifiedExcess v a D b Bc Bo z-parameterPenalty bplus b)|≤
        H*|1/t-1|+(L:ℝ)^2*(1-t)/2 := by
  have Hg := continuous_cTransform (continuous_modifiedDatum hv a D b ho)
  have H1 := hopfLax_time_comparison Hg hH t 1 z
  rw [one_div_one,hopfLax_one _ Hg] at H1
  have H2 := hopfLax_short_approx hc (sub_pos.mpr ht1) z
  have H3 := abs_le.mp H1
  rw [abs_le]
  dsimp only [regularizedComparison,modifiedExcess]
  constructor <;> linarith only [H3.1,H3.2,H2.1,H2.2,
    mul_nonneg (sq_nonneg (L:ℝ)) (sub_nonneg.mpr ht1.le)]

lemma regularized_interior_maximum {v : M → ℝ} (hv : Continuous v)
    {a D bplus bminus t err : ℝ} {Bc Bo : ℝ → ℝ}
    (hc : Continuous Bc) (ho : Continuous Bo) (ht : 0<t) (ht1 : t<1)
    (hp : 0<bplus) (hm : 0≤bminus)
    (hsmall : bminus≤bplus/(64*1024^2))
    (herr : err≤bplus/(128*1024^2))
    (hupper : ∀ b∈Icc bminus bplus,∀ z, modifiedExcess v a D b Bc Bo z≤b)
    (hlower : ∃ y, bplus/(8*1024^2)≤ modifiedExcess v a D (bplus/(8*1024)) Bc Bo y)
    (he : ∀ b∈Icc bminus bplus,∀ z,
      |regularizedComparison v a D bplus t Bc Bo (b,z)-
        (modifiedExcess v a D b Bc Bo z-parameterPenalty bplus b)|≤err) :
    ∃ q : ℝ×M, q.1∈Ioo bminus bplus ∧
      0 < regularizedComparison v a D bplus t Bc Bo q ∧
      ∀ w : ℝ×M,w.1∈Icc bminus bplus →
        regularizedComparison v a D bplus t Bc Bo w ≤ regularizedComparison v a D bplus t Bc Bo q := by
  let bs := bplus/(8*1024)
  have hbs : bs∈Icc bminus bplus := by dsimp [bs]; constructor <;> linarith only [hsmall,hp]
  have hmp : bminus≤bplus := hbs.1.trans hbs.2
  obtain ⟨y,hy⟩ := hlower
  change bplus/(8*1024^2)≤ modifiedExcess v a D bs Bc Bo y at hy
  let F := regularizedComparison v a D bplus t Bc Bo
  have hPstar : parameterPenalty bplus bs=bplus/(16*1024^2) := by
    dsimp [parameterPenalty,bs]
    field_simp [hp.ne']
    ring
  have Hstar := (abs_le.mp (he bs hbs y)).1
  rw [hPstar] at Hstar
  have hstar : bplus/(16*1024^2)-err≤F (bs,y) := by
    change _ ≤ regularizedComparison v a D bplus t Bc Bo (bs,y)
    linarith only [Hstar,hy]
  have HS : IsCompact (Icc bminus bplus×ˢ(univ : Set M)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨q,hq,hqmax⟩ := HS.exists_isMaxOn ⟨(bs,y),hbs,mem_univ y⟩
    (continuous_regularizedComparison hv a D bplus ht ht1 hc ho).continuousOn
  have hmax : F (bs,y)≤F q := hqmax ⟨hbs,mem_univ y⟩
  have hpos : 0<F q := by linarith only [hmax,hstar,herr,hp]
  have hminus : q.1≠bminus := by
    intro h
    have H := (abs_le.mp (he q.1 hq.1 q.2)).2
    have U := hupper q.1 hq.1 q.2
    have hP : 0≤parameterPenalty bplus bminus := by dsimp [parameterPenalty] <;> positivity
    change F q-(modifiedExcess v a D q.1 Bc Bo q.2-parameterPenalty bplus q.1)≤err at H
    rw [h] at H U
    linarith only [H,U,hP,hmax,hstar,hsmall,herr,hp]
  have hplus : q.1≠bplus := by
    intro h
    have H := (abs_le.mp (he q.1 hq.1 q.2)).2
    have U := hupper q.1 hq.1 q.2
    have hP : parameterPenalty bplus bplus=bplus/4096+2*bplus := by
      dsimp [parameterPenalty]
      field_simp [hp.ne']
    change F q-(modifiedExcess v a D q.1 Bc Bo q.2-parameterPenalty bplus q.1)≤err at H
    rw [h,hP] at H
    rw [h] at U
    linarith only [H,U,hpos,herr,hp]
  exact ⟨q,⟨lt_of_le_of_ne hq.1.1 hminus.symm,lt_of_le_of_ne hq.1.2 hplus⟩,
    hpos,fun w hw => hqmax ⟨hw,mem_univ _⟩⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.modified_maximum_configuration
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b bplus t H : ℝ} {z : M}
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo)
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H)
    (ht : 0<t) (ht1 : t<1) (hb : 0≤b) (hbp : 0<bplus)
    (hdy : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (hopfLax (1-t) (modifiedDatum v a D b Bc)) z)
    (hmax : ∀ᶠ q in 𝓝 (b,z),regularizedComparison v a D bplus t Bc Bo q≤
      regularizedComparison v a D bplus t Bc Bo (b,z)) :
    ∃ x y : M,∃ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) x) ∧
      p∈minimizingVectors x ∧ z=riemannianExp x (t • p) ∧ y=riemannianExp x p ∧
      hopfLax t (cTransform (modifiedDatum v a D b Bo)) z=
        cTransform (modifiedDatum v a D b Bo) x+cost x z/t ∧
      (∀ w,hopfLax (1-t) (modifiedDatum v a D b Bc) z=
        modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=y) ∧
      regularizedComparison v a D bplus t Bc Bo (b,z)=
        modifiedExcess v a D b Bc Bo y-parameterPenalty bplus b ∧
      ∀ (ι : Type) [Fintype ι] [Nonempty ι]
        (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (weights : ι → ℝ),
        (∀ i,(0:ℝ)<weights i) → (∑ i,weights i=1) → (∑ i,weights i • pj i=p) →
        (∀ i,pj i∈activeLogs (modifiedDatum v a D b Bo) x) →
        1/4096+4*b/bplus ≤ Bc ((v y-a)/D)-∑ i,weights i*Bo ((v (riemannianExp x (pj i))-a)/D) := by
  have hc' := continuous_modifiedDatum hv a D b hc
  have ho' := continuous_modifiedDatum hv a D b ho
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer (continuous_cTransform ho') t z
  obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hc' (1-t) z
  have hmaxz : ∀ᶠ w in 𝓝 z,
      hopfLax t (cTransform (modifiedDatum v a D b Bo)) w+
        hopfLax (1-t) (modifiedDatum v a D b Bc) w≤
      hopfLax t (cTransform (modifiedDatum v a D b Bo)) z+
        hopfLax (1-t) (modifiedDatum v a D b Bc) z := by
    have hh := (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually hmax
    filter_upwards [hh] with w hw
    dsimp only [regularizedComparison,id_eq] at hw
    linarith only [hw]
  obtain ⟨p,hps,hp,hpz,hpy,hsum⟩ :=
    hmtw.hopf_maximum_aligned ho' hc' ht ht1 hx hy hdy hmaxz
  have hcenter : ∀ w,hopfLax (1-t) (modifiedDatum v a D b Bc) z=
      modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=y := by
    intro w
    constructor
    · intro hw
      exact (hopfLax_backward_minimizer hc' (sub_pos.mpr ht1) hw hdy).symm.trans
        (hopfLax_backward_minimizer hc' (sub_pos.mpr ht1) hy hdy)
    · rintro rfl
      exact hy
  have hbar : p∈convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) x) :=
    normalSubdifferential_subset_active_hull ho' x hps
  refine ⟨x,y,p,hbar,hp,hpz,hpy,hx,hcenter,?_,?_⟩
  · dsimp only [regularizedComparison,modifiedExcess]
    rw [hsum]
  · intro ι _ _ pj m hm hm1 hmp hactive
    apply (hmtw.modified_parameter_inequality hv hc ho hbound pj m hm hm1
      (fun i=>(hactive i).1) (fun i=>(hactive i).2) ht ht1 hb hbp ?_ ?_).1
    · dsimp only
      rw [hmp,←hpz]
      exact hcenter
    · dsimp only
      rw [hmp,←hpz]
      exact (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hmax

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.exists_maximum_row (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b bplus t H : ℝ} {z : M}
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo)
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H) (ht : 0<t) (ht1 : t<1) (hb : 0≤b) (hbp : 0<bplus)
    (hdy : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (hopfLax (1-t) (modifiedDatum v a D b Bc)) z)
    (hmax : ∀ᶠ q in 𝓝 (b,z),regularizedComparison v a D bplus t Bc Bo q≤
      regularizedComparison v a D bplus t Bc Bo (b,z)) :
    Nonempty (MaximumRow (n := n) v a D b bplus t Bc Bo z) := by
  obtain ⟨x,y,p,hact,hmin,hz,hy,hpole,hcenter,hvalue,hparameter⟩ :=
    hmtw.modified_maximum_configuration hv hc ho hbound ht ht1 hb hbp hdy hmax
  let q : subgradientGraph (n := n) (cTransform (modifiedDatum v a D b Bo)) :=
    ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential (continuous_modifiedDatum hv a D b ho) x hact⟩
  refine ⟨⟨q,hmin,hz.symm,hact,?_,?_,?_⟩⟩
  · simpa only [hy] using hcenter
  · simpa only [hy] using hvalue
  · simpa only [hy] using hparameter

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumFamily
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.exists_maximum_family_oai (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (hc : Continuous Bc) (ho : Continuous Bo) {H : ℝ}
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H) (hp : 0<bplus) (hm : 0≤bminus)
    (hsmall : bminus≤bplus/(64*1024^2))
    (hupper : ∀ b∈Icc bminus bplus,∀ z,modifiedExcess v α D b Bc Bo z≤b)
    (hlower : ∃ y,bplus/(8*1024^2)≤ modifiedExcess v α D (bplus/(8*1024)) Bc Bo y)
    {L : ℝ≥0} (hLip : ∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc))
    {δ : ℝ} (hδ : 0<δ)
    (hreg : ∀ b∈Icc bminus bplus,∀ τ:ℝ,0<τ → τ<δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (modifiedDatum v α D b Bc))) :
    Nonempty (MaximumFamily (n := n) v α D bminus bplus Bc Bo) := by
  let r : ℕ → ℝ := fun k=>1/((k:ℝ)+2)
  let t : ℕ → ℝ := fun k=>1-r k
  have hr : Tendsto r atTop (𝓝 0) := by
    have Hr : Tendsto (fun k:ℕ=>(1:ℝ)/((k:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have H := Hr.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun k:ℕ=>(1:ℝ)/(((k+1:ℕ):ℝ)+1)) atTop (𝓝 0) at H
    simpa only [r,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using H
  have ht : Tendsto t atTop (𝓝 1) := by simpa only [sub_zero] using tendsto_const_nhds.sub hr
  have ht01 : ∀ k,0<t k ∧ t k<1 := by
    intro k
    have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
    have hden : 0<(k:ℝ)+2 := by linarith
    have hp' : 0 < r k := one_div_pos.mpr hden
    have hlt : r k<1 := (div_lt_one hden).mpr (by linarith)
    exact ⟨by dsimp [t] <;> linarith,by dsimp [t] <;> linarith⟩
  let C := (Metric.diam (univ:Set M))^2/2
  have hC : ∀ x y:M,cost x y≤C := by
    intro x y
    have Hd := Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
    have Hsq := sq_le_sq₀ dist_nonneg Metric.diam_nonneg |>.mpr Hd
    exact div_le_div_of_nonneg_right Hsq (by norm_num)
  let err : ℕ → ℝ := fun k=>C*|1/t k-1|+(L:ℝ)^2*(1-t k)/2
  have he : Tendsto err atTop (𝓝 0) := by
    have h1 : Tendsto (fun k=>(1:ℝ)/t k-1) atTop (𝓝 (1/1-1)) :=
      (tendsto_const_nhds.div ht (by norm_num : (1:ℝ)≠0)).sub tendsto_const_nhds
    have h2 : Tendsto err atTop (𝓝 (C*|1/1-1|+(L:ℝ)^2*(1-1)/2)) :=
      (tendsto_const_nhds.mul h1.abs).add
        ((tendsto_const_nhds.mul (tendsto_const_nhds.sub ht)).div_const 2)
    simpa only [one_div_one,sub_self,abs_zero,mul_zero,zero_div,add_zero] using h2
  have hε : 0<bplus/(128*1024^2) := by positivity
  have hevent : ∀ᶠ k in atTop,err k≤bplus/(128*1024^2) ∧ 1-t k<δ :=
    ((he.eventually (gt_mem_nhds hε)).mono (fun k hk=>hk.le)).and
      (((tendsto_const_nhds.sub ht : Tendsto (fun k=>1-t k) atTop (𝓝 (1-1))).eventually
        (by simpa using (gt_mem_nhds hδ : Iio δ∈𝓝 (0:ℝ)))))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  have Hmax : ∀ k,∃ q:ℝ×M,q.1∈Ioo bminus bplus ∧
      0 < regularizedComparison v α D bplus (t (k+N)) Bc Bo q ∧
      ∀ w:ℝ×M,w.1∈Icc bminus bplus →
        regularizedComparison v α D bplus (t (k+N)) Bc Bo w≤
          regularizedComparison v α D bplus (t (k+N)) Bc Bo q := by
    intro k
    apply regularized_interior_maximum hv hc ho (ht01 _).1 (ht01 _).2 hp hm hsmall
      (hN (k+N) (Nat.le_add_left _ _)).1 hupper hlower
    intro b hb z
    exact regularizedComparison_error hv ho (hLip b hb) hC (ht01 _).1 (ht01 _).2 z
  choose q hq hpq hmax using Hmax
  have Hrow : ∀ k,Nonempty (MaximumRow (n := n) v α D (q k).1 bplus (t (k+N)) Bc Bo (q k).2) := by
    intro k
    apply hmtw.exists_maximum_row hv hc ho hbound (ht01 _).1 (ht01 _).2
      (hm.trans (hq k).1.le) hp (hreg (q k).1 (Ioo_subset_Icc_self (hq k)) (1-t (k+N))
        (sub_pos.mpr (ht01 _).2) (hN (k+N) (Nat.le_add_left _ _)).2 (q k).2)
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (hq k).1 (hq k).2)] with w hw
    exact hmax k w (Ioo_subset_Icc_self hw)
  let R := fun k=>Classical.choice (Hrow k)
  exact ⟨⟨fun k=>t (k+N),fun k=>(q k).1,fun k=>(q k).2,fun k=>ht01 _,hq,
    ht.comp (tendsto_add_atTop_nat N),hpq,hmax,R⟩⟩
end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_maximum_family_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_maximum_family_oai.{u_1}
