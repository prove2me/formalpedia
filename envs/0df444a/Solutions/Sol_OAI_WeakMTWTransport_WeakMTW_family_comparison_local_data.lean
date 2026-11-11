-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:19.819318+00:00
-- url     : https://prove2.me/submissions/2dfb7c3e-ff3d-4026-a3ed-8033d8fe4c1d

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
import Definitions.Def_OAIQ232A031

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Calculus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma convexOn_of_affine_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S, f x+L (y-x)≤f y) :
    ConvexOn ℝ S f := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x+b • y
  obtain ⟨L,hL⟩ := hs z (hS hx hy ha hb hab)
  have hx' := mul_le_mul_of_nonneg_left (hL x hx) ha
  have hy' := mul_le_mul_of_nonneg_left (hL y hy) hb
  have hzero : a*L (x-z)+b*L (y-z)=0 := by
    rw [←smul_eq_mul a,←smul_eq_mul b,←map_smul,←map_smul,←map_add]
    have he : a • (x-z)+b • (y-z)=0 := by
      rw [smul_sub,smul_sub,←add_sub_add_comm,←add_smul,hab,one_smul]
      exact sub_self z
    rw [he,map_zero]
  change f z≤a*f x+b*f y
  have hc : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  nlinarith [hc]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Inner
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_of_quadratic_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (B : ℝ)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-B*‖y-x‖^2≤f y) :
    ConvexOn ℝ S (fun x => f x+B*‖x‖^2) := by
  apply convexOn_of_affine_lower_supports hS
  intro x hx
  obtain ⟨L,hL⟩ := hs x hx
  refine ⟨L+(2*B) • innerSL ℝ x,?_⟩
  intro y hy
  have H := hL y hy
  simp only [_root_.add_apply,_root_.smul_apply,innerSL_apply_apply,inner_sub_right,
    smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real] at H
  have hi : inner ℝ y x=inner ℝ x y := real_inner_comm _ _
  rw [hi] at H
  nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ParametricSemiconvex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma scalar_family_uniform_semiconvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    (a b K : ℝ) (hK : 0≤K) (L : ℝ≥0) :
    ∃ C>0,∀ p∈Kp,∀ S : Set E,Convex ℝ S → ∀ f:E → ℝ,
      LipschitzOnWith L f S → (∀ x∈S,f x∈Icc a b) →
      (∀ x∈S,∃ l:E →L[ℝ] ℝ,∀ y∈S,f x+l (y-x)-K*‖y-x‖^2≤f y) →
      ConvexOn ℝ S (fun x=>Φ (p,f x)+C/2*‖x‖^2) := by
  let dd := fun q:P×ℝ=>fderiv ℝ (fun s=>Φ (q.1,s)) q.2
  let hh := fun q:P×ℝ=>fderiv ℝ (fderiv ℝ (fun s=>Φ (q.1,s))) q.2
  have hdd : Continuous dd := continuous_iff_continuousAt.mpr (fun q=>
    (ContDiffAt.partial_snd_fderiv (f := fun p s=>Φ (p,s)) (hΦ.contDiffAt (x := q))).continuousAt)
  have hhh : Continuous hh := continuous_iff_continuousAt.mpr (fun q=>
    (ContDiffAt.partial_snd_fderiv_two (f := fun p s=>Φ (p,s)) (hΦ.contDiffAt (x := q))).continuousAt)
  obtain ⟨A0,hA0⟩ := (hKp.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn (f := dd) hdd.continuousOn
  obtain ⟨B0,hB0⟩ := (hKp.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn (f := hh) hhh.continuousOn
  let A := max A0 0
  let B := max B0 0
  have hA : 0≤A := le_max_right _ _
  have hB : 0≤B := le_max_right _ _
  let C := 2*(A*K+B*(L:ℝ)^2+1)
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro p hp S hS f hlip hrange hs
  let φ := fun s=>Φ (p,s)
  have hφ : ContDiff ℝ 2 φ := (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply convexOn_of_quadratic_lower_supports hS (C/2)
  intro x hx
  obtain ⟨l,hl⟩ := hs x hx
  refine ⟨deriv φ (f x) • l,?_⟩
  intro y hy
  have H := first_order_remainder_le_of_hessian_bound (convex_Icc a b) hB
    (fun z hz=>hφ.contDiffAt) (fun z hz=>by exact (hB0 (p,z) ⟨hp,hz⟩).trans (le_max_left _ _))
    (hrange x hx) (hrange y hy)
  rw [fderiv_eq_deriv_mul] at H
  have Hlow := (abs_le.mp H).1
  have Hf := mul_le_mul_of_nonneg_left (hl y hy) ((hmono p hp).deriv_nonneg (x := f x))
  have Hlip := hlip.dist_le_mul y hy x hx
  rw [dist_eq_norm,dist_eq_norm] at Hlip
  have Hsq := sq_le_sq₀ (norm_nonneg (f y-f x)) (by positivity : 0≤(L:ℝ)*‖y-x‖) |>.mpr Hlip
  have HB := mul_le_mul_of_nonneg_left Hsq hB
  have HA : deriv φ (f x)≤A := by
    have hh0 := hA0 (p,f x) ⟨hp,hrange x hx⟩
    have hh1 : |deriv φ (f x)|≤A0 := by
      simpa only [dd,←norm_deriv_eq_norm_fderiv,Real.norm_eq_abs] using hh0
    exact (le_abs_self _).trans (hh1.trans (le_max_left _ _))
  have HK := mul_le_mul_of_nonneg_right HA (mul_nonneg hK (sq_nonneg ‖y-x‖))
  simp only [_root_.smul_apply,smul_eq_mul]
  dsimp only [C]
  nlinarith [sq_nonneg ‖y-x‖]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ShortLocalMinimum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

omit [Nonempty M] in
lemma chartCost_pair_contDiffAt_diagonal {a : M} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×Model n =>
      chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2) (x,x) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm x :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hx)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm x,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    (zero_mem_injectivityDomain (n := n) (χ.symm x))
  simp only [riemannianExp_zero] at hc
  exact (hc.comp (x,x) ((hi.comp (x,x) contDiffAt_snd.contMDiffAt).prodMk
    (hi.comp (x,x) contDiffAt_fst.contMDiffAt))).contDiffAt
end WeakMTWTransport

end

end OAI
end

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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_chart_fiber_log {x a : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x)
    (ha : riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let ψ := extChartAt 𝓘(ℝ,Model n) a
    let u := ψ (riemannianExp x p)
    ∃ e : Model n → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ e u ∧ e u=p ∧
      (∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w) ∧
      Function.Injective (fderiv ℝ e u) := by
  let ψ := extChartAt 𝓘(ℝ,Model n) a
  let u := ψ (riemannianExp x p)
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hu : u∈ψ.target := ψ.map_source ha
  have hui : ψ.symm u=riemannianExp x p := ψ.left_inv ha
  obtain ⟨L,hL,hLp,hLi⟩ := exists_smooth_fiber_log hp
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ ψ.symm u :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hu)
  let e := fun w : Model n => L (ψ.symm w)
  have he : ContDiffAt ℝ ∞ e u :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L (ψ.symm u) from by
      simpa only [hui] using hL).comp u hi).contDiffAt
  have heu : e u=p := by dsimp [e]; rw [hui]; exact hLp
  have hei : ∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w :=
    hi.continuousAt.eventually (by simpa only [hui] using hLi)
  refine ⟨e,he,heu,hei,?_⟩
  let c : V → Model n := fun v => ψ (riemannianExp x v)
  have hc : ContDiffAt ℝ ∞ c p :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by
      simpa only [extChartAt_source] using ha)).comp p
        (contMDiff_riemannianExp_fiber x p)).contDiffAt
  have hid : (fun w => c (e w)) =ᶠ[𝓝 u] (fun w => w) := by
    filter_upwards [hei,(isOpen_extChartAt_target a).mem_nhds hu] with w hw hwt
    dsimp [c]
    rw [hw,ψ.right_inv hwt]
  have HD := hid.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp u (by simpa only [heu] using hc.differentiableAt (by simp))
    (he.differentiableAt (by simp)),fderiv_fun_id] at HD
  intro v w hvw
  change fderiv ℝ e u v=fderiv ℝ e u w at hvw
  have H := congrArg (fun C : Model n →L[ℝ] Model n => C v-C w) HD
  apply sub_eq_zero.mp
  simpa only [ContinuousLinearMap.comp_apply,hvw,sub_self,ContinuousLinearMap.id_apply] using H.symm

end WeakMTWTransport

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

lemma second_fderiv_comp_stationary {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hzero : fderiv ℝ f (g x)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,hzero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_comp,zero_apply,
    zero_add,add_zero,add_apply] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalMetricCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal NNReal ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]
local notation "𝒥" => 𝓘(ℝ,E)

lemma exists_lipschitzOn_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ball (extChartAt 𝓘(ℝ,E) x x) r ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,E) x).symm
        (ball (extChartAt 𝓘(ℝ,E) x x) r) := by
  let (y : E) : ENorm (TangentSpace 𝒥 y →L[ℝ]
      TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)) :=
    inferInstanceAs (ENorm (E →L[ℝ] TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝒥 x
  obtain ⟨r,hrpos,hr⟩ : ∃ r > 0,
      ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} := by
    have hh := inter_mem (extChartAt_target_mem_nhdsWithin (I := 𝒥) x) hC
    have hh' : (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} ∈
        𝓝 (extChartAt 𝒥 x x) := by
      simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at hh ⊢
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    exact Metric.mem_nhds_iff.mp hh'
  refine ⟨C,r,hrpos,fun y hy => (hr hy).1,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := (extChartAt 𝒥 x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝒥 x).target ∩
      {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)}) := by
    simp only [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap,η]
    exact ((convex_ball _ _).segment_subset hu hv).trans hr
  simp only [preimage_inter,subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hh : riemannianEDist 𝒥 ((extChartAt 𝒥 x).symm u) ((extChartAt 𝒥 x).symm v) ≤
      pathELength 𝒥 γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := 𝒥)]
  apply hh.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hd : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hd1 : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hd 1)
  rw [hd1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ManifoldLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [MetricSpace M] [ChartedSpace F M]
  [IsManifold 𝓘(ℝ,F) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,F) x)]
  [IsContinuousRiemannianBundle F (fun x : M => TangentSpace 𝓘(ℝ,F) x)]
  [IsRiemannianManifold 𝓘(ℝ,F) M]

lemma contMDiffAt_exists_lipschitzOn {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith C f U := by
  let χ := extChartAt 𝓘(ℝ,F) (f x)
  have hχ : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) 1 χ (f x) :=
    contMDiffAt_extChartAt
  obtain ⟨D,V,hV,hD⟩ := (((hχ.comp x hf).contDiffAt)).exists_lipschitzOnWith
  obtain ⟨C,r,hr,hsub,hC⟩ := exists_lipschitzOn_inverse_chart (E := F) (f x)
  let U := V ∩ f ⁻¹' (χ.source ∩ χ ⁻¹' ball (χ (f x)) r)
  have hU : U ∈ 𝓝 x := by
    apply inter_mem hV
    apply hf.continuousAt.preimage_mem_nhds
    exact inter_mem (extChartAt_source_mem_nhds (f x))
      (hχ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr))
  refine ⟨C*D,U,hU,?_⟩
  have hmaps : MapsTo (χ ∘ f) U (ball (χ (f x)) r) := fun _ hy => hy.2.2
  have hcomp := hC.comp (hD.mono inter_subset_left) hmaps
  intro y hy z hz
  have hh := hcomp hy hz
  change edist (χ.symm (χ (f y))) (χ.symm (χ (f z))) ≤ _ at hh
  rwa [χ.left_inv hy.2.1,χ.left_inv hz.2.1] at hh

lemma contMDiffOn_exists_lipschitzOn_compact {f : E → M} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x∈K, ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ∃ C : ℝ≥0, LipschitzOnWith C f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨C,U,hU,hC⟩ := contMDiffAt_exists_lipschitzOn (hf x hx)
  exact ⟨C,U,mem_nhdsWithin_of_mem_nhds hU,hC⟩

end

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

lemma exists_norm_sq_lower_of_injective (L : E →L[ℝ] F) (hL : Function.Injective L) :
    ∃ c>0, ∀ v:E, c*‖v‖^2 ≤ ‖L v‖^2 := by
  obtain ⟨K,hK,HK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hKr),?_⟩
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz L HK v
  have H2 := (sq_le_sq₀ (norm_nonneg v) (mul_nonneg K.coe_nonneg (norm_nonneg (L v)))).mpr H
  rw [mul_pow] at H2
  have HH : ‖v‖^2/(K:ℝ)^2 ≤ ‖L v‖^2 :=
    (div_le_iff₀ (sq_pos_of_pos hKr)).mpr (by simpa only [mul_comm] using H2)
  simpa only [div_eq_mul_inv,mul_comm] using HH

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_DiagonalCostConvexity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartCost_diagonal_coercive {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0, ∀ d : Model n, m*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z))) z d d := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let x := χ.symm z
  have hx : x∈χ.source := χ.map_target hz
  have hxz : χ x=z := χ.right_inv hz
  change extChartAt 𝓘(ℝ,Model n) a x=z at hxz
  have hp := zero_mem_injectivityDomain (n := n) x
  obtain ⟨e,he,he0,hei,hinj⟩ := exists_smooth_chart_fiber_log hp
    (show riemannianExp x 0∈χ.source from by rwa [riemannianExp_zero])
  simp only [riemannianExp_zero,hxz] at he he0 hei hinj
  obtain ⟨m,hm,hbound⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hinj
  refine ⟨m,hm,fun d => ?_⟩
  have hC : ContDiffAt ℝ 2 (normalCost (n := n) x 0) 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hzero : fderiv ℝ (normalCost (n := n) x 0) 0=0 := by
    rw [(normalCost_hasFDerivAt_zero hp).fderiv]
    simp only [neg_zero,map_zero]
  have heq : chartCost a x =ᶠ[𝓝 z] (fun w => normalCost (n := n) x 0 (e w)) := by
    filter_upwards [hei] with w hw
    simp only [normalCost,riemannianExp_zero,hw,chartCost]
  rw [heq.fderiv.fderiv_eq]
  have H := second_fderiv_comp_stationary (f := normalCost (n := n) x 0) (g := e)
    (he0.symm ▸ hC) (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (by rwa [he0]) d d
  rw [H,he0]
  change m*‖d‖^2 ≤ normalHessian x 0 (fderiv ℝ e z d) (fderiv ℝ e z d)
  rw [←hessianValue_eq_normalHessian hp,hessianValue_zero]
  exact hbound d

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LocalMountains
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
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y]

lemma lower_support_of_nonnegative_hessian {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S, ∀ d : E, 0 ≤ fderiv ℝ (fderiv ℝ f) z d d)
    {x y : E} (hx : x∈S) (hy : y∈S) :
    f x+fderiv ℝ f x (y-x) ≤ f y := by
  let d := y-x
  let l : ℝ → E := fun t => x+t • d
  let g : ℝ → ℝ := fun t => f (l t)
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (l t) d
  let g'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (l t) d d
  have hl : ∀ t∈Icc (0:ℝ) 1, l t∈S := by
    intro t ht
    have H := hS hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [l,d]
    module
  have hld (t : ℝ) : HasDerivAt l d t := by
    simpa only [l,id_eq,one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t :=
    ((hf (l t) (hl t ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
  have hg' (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g' (g'' t) t := by
    have H := (((hf (l t) (hl t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
    simpa only [g',g'',Function.comp_apply,map_zero,add_zero] using H.clm_apply (hasDerivAt_const t d)
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hH _ (hl t (interior_subset ht)) d)
  have H := hconv.deriv_le_slope (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_lt_one (hg 0 (by constructor <;> norm_num)).differentiableAt
  rw [(hg 0 (by constructor <;> norm_num)).deriv] at H
  simp only [g,g',l,d,zero_smul,add_zero,one_smul,add_sub_cancel,slope,
    sub_zero,inv_one,one_smul,vsub_eq_sub] at H
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_OuterDisplacementJetBound
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma convexOn_of_nonnegative_hessian {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ z∈S,ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S,∀ d:E,0≤fderiv ℝ (fderiv ℝ f) z d d) : ConvexOn ℝ S f := by
  apply convexOn_of_affine_lower_supports hS
  intro x hx
  exact ⟨fderiv ℝ f x,fun y hy => lower_support_of_nonnegative_hessian hS hf hH hx hy⟩

lemma strongConvexOn_of_hessian_lower {f : E → ℝ} {S : Set E} {m : ℝ}
    (hS : Convex ℝ S) (hf : ∀ z∈S,ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S,∀ d:E,m*‖d‖^2≤fderiv ℝ (fderiv ℝ f) z d d) :
    StrongConvexOn S m f := by
  rw [strongConvexOn_iff_convex]
  have hN (z:E) : ContDiffAt ℝ 2 (fun w:E => ‖w‖^2/2) z :=
    (half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have he : (fun z => f z-m/2*‖z‖^2)=(fun z => f z-m*(‖z‖^2/2)) := by
    ext z; ring
  rw [he]
  apply convexOn_of_nonnegative_hessian hS
    (fun z hz => (hf z hz).sub (contDiffAt_const.mul (hN z)))
  intro z hz d
  rw [second_fderiv_sub (hf z hz) (contDiffAt_const.mul (hN z)),
    second_fderiv_const_mul,half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (hH z hz d)

lemma StrongConvexOn.quadratic_growth_half {f : E → ℝ} {S : Set E} {m : ℝ}
    (hf : StrongConvexOn S m f) {x y:E} (hx:x∈S) (hy:y∈S)
    (hmin : IsMinOn f S x) : f x+(m/4)*‖y-x‖^2≤f y := by
  have H := hf.2 hx hy (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  have HM := hmin (hf.1 hx hy (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1))
  change f ((1/2:ℝ) • x+(1/2:ℝ) • y)≤
    (1/2:ℝ)*f x+(1/2:ℝ)*f y-(1/2:ℝ)*(1/2:ℝ)*(m/2*‖x-y‖^2) at H
  rw [norm_sub_rev] at H
  change f x≤f ((1/2:ℝ) • x+(1/2:ℝ) • y) at HM
  linarith only [H,HM]

lemma strongConvexOn_add_semiconvex {f g : E → ℝ} {S : Set E} {m K t : ℝ}
    (hf : StrongConvexOn S m f) (hg : ConvexOn ℝ S (fun x => g x+K/2*‖x‖^2))
    (ht : 0≤t) : StrongConvexOn S (m-t*K) (fun x => f x+t*g x) := by
  rw [strongConvexOn_iff_convex] at hf ⊢
  have HF : ConvexOn ℝ S (fun x => (f x-m/2*‖x‖^2)+t*(g x+K/2*‖x‖^2)) :=
    hf.add (hg.smul ht)
  convert HF using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_StrongCostConvexity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance strongCostDualGroup_r10b64b_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.WeakMTWTransport.strongCostDualSpace
local instance strongCostBilinearGroup_r10b64b_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance strongCostBilinearSpace_r10b64b_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma chartCost_uniform_strongConvex {a : M} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0,∃ r>0,∃ V∈𝓝 x,∀ z∈V,
      StrongConvexOn (Metric.closedBall x r) m
        (chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z)) := by
  let F : Model n → Model n → ℝ := fun z =>
    chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z)
  have hc : ContDiffAt ℝ ∞ (Function.uncurry F) (x,x) :=
    chartCost_pair_contDiffAt_diagonal hx
  have hH : ContinuousAt (fun q : Model n×Model n =>
      fderiv ℝ (fderiv ℝ (F q.1)) q.2) (x,x) :=
    (ContDiffAt.partial_snd_fderiv_two hc).continuousAt
  obtain ⟨k,hk,hpos⟩ := chartCost_diagonal_coercive hx
  have H := @ContinuousAt.norm (Model n×Model n) (Model n →L[ℝ] Model n →L[ℝ] ℝ) _ _ _ _
    (hH.sub (continuousAt_const (y := fderiv ℝ (fderiv ℝ (F x)) x)))
  have hn : ∀ᶠ q : Model n×Model n in 𝓝 (x,x),
      ‖fderiv ℝ (fderiv ℝ (F q.1)) q.2-fderiv ℝ (fderiv ℝ (F x)) x‖<k/2 := by
    apply H.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero]
      using (half_pos hk)
  have hd : ∀ᶠ q : Model n×Model n in 𝓝 (x,x),ContDiffAt ℝ 2 (F q.1) q.2 := by
    filter_upwards [(hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)] with q hq
    exact hq.comp (f := fun z:Model n => (q.1,z)) q.2 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨V,hV,U,hU,hVU⟩ := mem_nhds_prod_iff.mp (hn.and hd)
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨k/2,half_pos hk,r,hr,V,hV,?_⟩
  intro z hz
  apply strongConvexOn_of_hessian_lower (convex_closedBall x r)
    (fun w hw => (hVU (a := (z,w)) ⟨hz,hrU hw⟩).2)
  intro w hw d
  have hn' := (hVU (a := (z,w)) ⟨hz,hrU hw⟩).1
  have hb := (fderiv ℝ (fderiv ℝ (F z)) w-fderiv ℝ (fderiv ℝ (F x)) x).le_opNorm₂ d d
  have hh := hpos d
  have hm := mul_le_mul_of_nonneg_right hn'.le (sq_nonneg ‖d‖)
  have ha := neg_le_abs (fderiv ℝ (fderiv ℝ (F z)) w d d-
    fderiv ℝ (fderiv ℝ (F x)) x d d)
  simp only [sub_apply,Real.norm_eq_abs] at hb
  dsimp only [F] at hb ha hm
  nlinarith only [hb,ha,hh,hm]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_FamilySemiconvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma uniform_family_chart_semiconvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ K>0,∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ p∈Kp,∀ u : M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ConvexOn ℝ (ball (extChartAt 𝓘(ℝ,Model n) a a) r)
        (fun z => Φ (p,cTransform u ((extChartAt 𝓘(ℝ,Model n) a).symm z))+K/2*‖z‖^2) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨K0,hK0,r0,hr0,hr0T,hSup⟩ := uniform_cTransform_chart_lower (n := n) a
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨L,r1,hr1,hr1T,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  obtain ⟨K,hK,H⟩ := scalar_family_uniform_semiconvex (E := Model n) hΦ hKp hmono A B K0 hK0.le (D*L)
  let r := min r0 r1
  have hr : 0 < r := lt_min hr0 hr1
  have hsub0 : ball (χ a) r⊆ball (χ a) r0 := ball_subset_ball (min_le_left _ _)
  have hsub1 : ball (χ a) r⊆ball (χ a) r1 := ball_subset_ball (min_le_right _ _)
  refine ⟨K,hK,r,hr,fun z hz => hr0T (hsub0 hz),?_⟩
  intro p hp u hu hb
  apply H p hp _ (convex_ball _ _) _
  · exact (cTransform_lipschitz hu (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))).comp_lipschitzOnWith (hL.mono hsub1)
  · exact fun z hz => hb _
  · intro z hz
    obtain ⟨l,hl⟩ := hSup u hu z (hsub0 hz)
    exact ⟨l,fun y hy => hl y (hsub0 hy)⟩

lemma uniform_family_short_action_strongConvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ m>0,∃ r>0,∃ V∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a),∃ δ>0,
      closedBall (extChartAt 𝓘(ℝ,Model n) a a) r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ p∈Kp,∀ u : M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ t : ℝ,0<t → t<δ → ∀ z∈V,
      StrongConvexOn (closedBall (extChartAt 𝓘(ℝ,Model n) a a) r) m
        (fun y => t*Φ (p,cTransform u ((extChartAt 𝓘(ℝ,Model n) a).symm y))+
          chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z) y) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨K,hK,R,hR,hRT,hsemi⟩ := uniform_family_chart_semiconvex (n := n) hΦ hKp hmono A B a
  obtain ⟨m,hm,r0,hr0,V,hV,hstrong⟩ := chartCost_uniform_strongConvex
    (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)
  let r := min r0 (R/2)
  have hr : 0 < r := lt_min hr0 (half_pos hR)
  have hsub0 : closedBall (χ a) r⊆closedBall (χ a) r0 := closedBall_subset_closedBall (min_le_left _ _)
  have hsubR : closedBall (χ a) r⊆ball (χ a) R := closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hR))
  refine ⟨m / 2,half_pos hm,r,hr,V,hV,m / (2*K),by positivity,fun z hz => hRT (hsubR hz),?_⟩
  intro p hp u hu hb t ht htδ z hz
  have hs : StrongConvexOn (closedBall (χ a) r) m (chartCost a (χ.symm z)) :=
    ⟨convex_closedBall _ _,fun {x} hx {y} hy {p} {q} hp hq hsum => (hstrong z hz).2 (hsub0 hx) (hsub0 hy) hp hq hsum⟩
  have hh := strongConvexOn_add_semiconvex hs
    ((hsemi p hp u hu hb).subset hsubR (convex_closedBall _ _)) ht.le
  have htK : t*K< m / 2 := by
    apply (lt_div_iff₀ hK).mp
    simpa only [div_div] using htδ
  have hle : m / 2 ≤ m-t*K := by linarith
  have H := _root_.StrongConvexOn.mono hle hh
  simpa only [add_comm] using H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_StrongEnvelope
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S T : Set E} {w F : E → ℝ} {C : E → E → ℝ} {Y : E → E}
  {m K B : ℝ}

lemma strongly_convex_minimizer_unique {f : E → ℝ} {x y:E}
    (hm : 0 < m) (hf : StrongConvexOn S m f) (hx : x∈S) (hy : y∈S)
    (hmin : IsMinOn f S x) (heq : f x=f y) : x=y := by
  have H := StrongConvexOn.quadratic_growth_half hf hx hy hmin
  rw [heq] at H
  have hnonneg := sq_nonneg ‖y-x‖
  have hs : ‖y-x‖^2=0 := by nlinarith only [H,hm,hnonneg]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))).symm

lemma strong_envelope_minimizer_lipschitz (hm :  0 < m) (hK :  0 ≤ K)
    (hY : ∀ z∈T,Y z∈S)
    (hval : ∀ z∈T,F z=w (Y z)+C (Y z) z)
    (hmin : ∀ z∈T,∀ y∈S,F z≤w y+C y z)
    (hstrong : ∀ z∈T,StrongConvexOn S m (fun y => w y+C y z))
    (hcross : ∀ y∈S,∀ y'∈S,∀ z∈T,∀ z'∈T,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖) :
    LipschitzOnWith (Real.toNNReal (2*K/m)) Y T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz z' hz'
  have hy := hY z hz
  have hy' := hY z' hz'
  have HM : IsMinOn (fun y => w y+C y z) S (Y z) := by
    intro y hy
    change w (Y z)+C (Y z) z≤w y+C y z
    rw [←hval z hz]
    exact hmin z hz y hy
  have HM' : IsMinOn (fun y => w y+C y z') S (Y z') := by
    intro y hy
    change w (Y z')+C (Y z') z'≤w y+C y z'
    rw [←hval z' hz']
    exact hmin z' hz' y hy
  have HG := StrongConvexOn.quadratic_growth_half (hstrong z hz) hy hy' HM
  have HG' := StrongConvexOn.quadratic_growth_half (hstrong z' hz') hy' hy HM'
  have HC := (abs_le.mp (hcross (Y z) hy (Y z') hy' z hz z' hz')).1
  rw [norm_sub_rev (Y z) (Y z')] at HG'
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ (div_nonneg (by positivity) hm.le)]
  rw [norm_sub_rev (Y z) (Y z'),norm_sub_rev z z']
  by_cases hd : ‖Y z'-Y z‖=0
  · rw [hd]; positivity
  have hp : 0<‖Y z'-Y z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
  have H : m/2*‖Y z'-Y z‖^2≤K*‖Y z'-Y z‖*‖z'-z‖ := by linarith only [HG,HG',HC]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).mpr
  change ‖Y z'-Y z‖*m≤2*K*‖z'-z‖
  nlinarith only [H,hp,hm]

lemma strong_envelope_quadratic_remainder (hm :  0 < m)
    (hY : ∀ z∈T,Y z∈S)
    (hval : ∀ z∈T,F z=w (Y z)+C (Y z) z)
    (hmin : ∀ z∈T,∀ y∈S,F z≤w y+C y z)
    (hstrong : ∀ z∈T,StrongConvexOn S m (fun y => w y+C y z))
    (hcross : ∀ y∈S,∀ y'∈S,∀ z∈T,∀ z'∈T,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖)
    {l:E → E →L[ℝ] ℝ}
    (hrem : ∀ z∈T,∀ z'∈T,
      |C (Y z) z'-C (Y z) z-l z (z'-z)|≤B*‖z'-z‖^2) :
    ∀ z∈T,∀ z'∈T,
      |F z'-F z-l z (z'-z)|≤(B+K^2/m)*‖z'-z‖^2 := by
  intro z hz z' hz'
  have hy := hY z hz
  have hy' := hY z' hz'
  have HM : IsMinOn (fun y => w y+C y z) S (Y z) := by
    intro y hy
    change w (Y z)+C (Y z) z≤w y+C y z
    rw [←hval z hz]
    exact hmin z hz y hy
  have HG := StrongConvexOn.quadratic_growth_half (hstrong z hz) hy hy' HM
  have HC := (abs_le.mp (hcross (Y z) hy (Y z') hy' z hz z' hz')).1
  have HR := abs_le.mp (hrem z hz z' hz')
  have HU := hmin z' hz' (Y z) hy
  have hYz := hval z hz
  have hYz' := hval z' hz'
  have hsquare := sq_nonneg (m*‖Y z'-Y z‖-2*K*‖z'-z‖)
  have hdiv : (K^2/m)*m=K^2 := div_mul_cancel₀ _ hm.ne'
  have Hcomplete : -(K^2/m)*‖z'-z‖^2≤
      m/4*‖Y z'-Y z‖^2-K*‖Y z'-Y z‖*‖z'-z‖ := by
    nlinarith only [hsquare,hdiv,hm]
  apply abs_le.mpr
  constructor
  · nlinarith only [HG,HC,HR.1,hYz,hYz',Hcomplete]
  · have hn : 0 ≤ K^2/m*‖z'-z‖^2 := by positivity
    nlinarith only [HU,hYz,HR.2,hn]

lemma strong_envelope_C11 {a:E} {r:ℝ} (hr :  0 < r) (hm :  0 < m) (hK :  0 ≤ K) (hB :  0 ≤ B)
    (hY : ∀ z∈ball a r,Y z∈S)
    (hval : ∀ z∈ball a r,F z=w (Y z)+C (Y z) z)
    (hmin : ∀ z∈ball a r,∀ y∈S,F z≤w y+C y z)
    (hstrong : ∀ z∈ball a r,StrongConvexOn S m (fun y => w y+C y z))
    (hcross : ∀ y∈S,∀ y'∈S,∀ z∈ball a r,∀ z'∈ball a r,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖)
    {l:E → E →L[ℝ] ℝ}
    (hrem : ∀ z∈ball a r,∀ z'∈ball a r,
      |C (Y z) z'-C (Y z) z-l z (z'-z)|≤B*‖z'-z‖^2) :
    (∀ z∈ball a r,HasFDerivAt F (l z) z) ∧
      LipschitzOnWith (Real.toNNReal (6*(B+K^2/m))) (fderiv ℝ F) (ball a (r/4)) := by
  have H := strong_envelope_quadratic_remainder hm hY hval hmin hstrong hcross hrem
  have hconst : 0 ≤ B+K^2/m := add_nonneg hB (div_nonneg (pow_nonneg hK 2) hm.le)
  have hd : ∀ z∈ball a r,HasFDerivAt F (l z) z := by
    intro z hz
    exact hasFDerivAt_of_quadratic_remainder hconst
      (by filter_upwards [isOpen_ball.mem_nhds hz] with z' hz'; exact H z hz z' hz')
  refine ⟨hd,?_⟩
  rw [Real.toNNReal_of_nonneg (show 0≤6*(B+K^2/m) from by positivity)]
  exact derivative_lipschitz_of_quadratic_remainder hr hconst
    (fun z hz z' hz' => by rw [(hd z hz).fderiv]; exact H z hz z' hz')
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

lemma hopfLax_minimizer_distance {u : M → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {t : ℝ} (ht : 0<t) {z x : M}
    (hx : hopfLax t u z=u x+cost x z/t) : dist x z ≤ 2*(L:ℝ)*t := by
  have H := hopfLax_le_self hu.continuous t z
  rw [hx,cost] at H
  have Hl := (abs_le.mp (show |u x-u z| ≤ (L:ℝ)*dist x z by
    simpa only [Real.dist_eq] using hu.dist_le_mul x z)).1
  have HH : dist x z^2/2 ≤ (u z-u x)*t := by
    apply (div_le_iff₀ ht).mp
    linarith only [H]
  by_contra h
  have hq : 0 < dist x z := (by positivity : 0 ≤ 2*(L:ℝ)*t).trans_lt (lt_of_not_ge h)
  have Hl' := mul_le_mul_of_nonneg_right (show u z-u x ≤ (L:ℝ)*dist x z by linarith only [Hl]) ht.le
  nlinarith only [HH,Hl',mul_pos hq (sub_pos.mpr (lt_of_not_ge h))]

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma uniform_hopfLax_minimizers_eventually_in (L : ℝ≥0) {x : M} {V : Set M}
    (hV : V∈𝓝 x) :
    ∀ᶠ q : ℝ×M in 𝓝 ((0:ℝ),x), 0<q.1 → ∀ f : M → ℝ, LipschitzWith L f →
      ∀ y : M, hopfLax q.1 f q.2=f y+cost y q.2/q.1 → y∈V := by
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hc : ContinuousAt (fun q : ℝ×M => 2*(L:ℝ)*q.1+dist q.2 x) (0,x) := by fun_prop
  have he : ∀ᶠ q : ℝ×M in 𝓝 ((0:ℝ),x),2*(L:ℝ)*q.1+dist q.2 x < r :=
    hc.eventually_lt continuousAt_const (by simpa only [mul_zero,dist_self,zero_add] using hr)
  filter_upwards [he] with q hq
  intro ht f hf y hy
  apply hrV
  change dist y x < r
  have hd := hopfLax_minimizer_distance hf ht hy
  have htri := dist_triangle y q.2 x
  linarith only [hd,htri,hq]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartHopfLocalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma uniform_hopfLax_chart_localization (L : ℝ≥0) (a : M) {R:ℝ} (hR : 0<R) :
    ∃ δ>0,∃ V∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a),
      ∀ t:ℝ,0<t → t<δ → ∀ z∈V,∀ w:M → ℝ,LipschitzWith L w →
      ∀ y:M,hopfLax t w ((extChartAt 𝓘(ℝ,Model n) a).symm z)=
        w y+cost y ((extChartAt 𝓘(ℝ,Model n) a).symm z)/t →
        y∈(extChartAt 𝓘(ℝ,Model n) a).source ∧
        extChartAt 𝓘(ℝ,Model n) a y∈ball (extChartAt 𝓘(ℝ,Model n) a a) R := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hsrc : χ.source∩χ⁻¹'ball (χ a) R∈𝓝 a :=
    inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a)
      ((continuousAt_extChartAt (I := 𝓘(ℝ,Model n)) a).preimage_mem_nhds (ball_mem_nhds _ hR))
  have H := uniform_hopfLax_minimizers_eventually_in L hsrc
  have hT : χ a∈χ.target := mem_extChartAt_target a
  have hi : ContinuousAt χ.symm (χ a) :=
    (continuousOn_extChartAt_symm a (χ a) hT).continuousAt ((isOpen_extChartAt_target a).mem_nhds hT)
  have he : χ.symm (χ a)=a := χ.left_inv (mem_extChartAt_source a)
  have hq : Tendsto (fun q:ℝ×Model n => (q.1,χ.symm q.2)) (𝓝 (0,χ a)) (𝓝 (0,a)) := by
    simpa only [Function.comp_apply,Prod.snd,he] using (continuousAt_fst.prodMk (hi.comp (x := ((0:ℝ),χ a)) continuousAt_snd)).tendsto
  have HH := hq.eventually H
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp HH
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ,hδ,V,hV,?_⟩
  intro t ht htδ z hz w hw y hy
  have htU : t∈U := hδU (by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htδ)
  exact hUV (a := (t,z)) ⟨htU,hz⟩ ht w hw y hy
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_KernelBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma kernel_rectangle_of_partial_lipschitz {C : E → E → ℝ} {S T : Set E}
    {K : ℝ≥0} (hT : Convex ℝ T)
    (hd : ∀ y∈S,∀ z∈T,DifferentiableAt ℝ (C y) z)
    (hLip : LipschitzOnWith K (fun q : E×E => fderiv ℝ (C q.1) q.2) (S×ˢT)) :
    ∀ y∈S,∀ y'∈S,∀ z∈T,∀ z'∈T,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖ := by
  intro y hy y' hy' z hz z' hz'
  have HH := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun q => C y' q-C y q)
    (f' := fun q => fderiv ℝ (C y') q-fderiv ℝ (C y) q)
    (fun q hq => ((hd y' hy' q hq).hasFDerivAt.sub (hd y hy q hq).hasFDerivAt).hasFDerivWithinAt)
    (C := (K:ℝ)*‖y'-y‖) (by
      intro q hq
      have H := hLip.dist_le_mul (y',q) ⟨hy',hq⟩ (y,q) ⟨hy,hq⟩
      simpa only [dist_eq_norm,Prod.dist_eq,dist_self,max_eq_left (dist_nonneg),←dist_eq_norm] using H)
    hT hz hz'
  rw [Real.norm_eq_abs] at HH
  convert HH using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)

lemma smooth_kernel_second_locally_bounded {C : E → E → ℝ} {a:E}
    (hc : ContDiffAt ℝ ∞ (Function.uncurry C) (a,a)) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ q:E×E in 𝓝 (a,a),
      ‖fderiv ℝ (fderiv ℝ (C q.1)) q.2‖≤B := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hh : ContinuousAt (fun q:E×E => fderiv ℝ (fderiv ℝ (C q.1)) q.2) (a,a) :=
    (ContDiffAt.partial_snd_fderiv_two hc).continuousAt
  let B := ‖fderiv ℝ (fderiv ℝ (C a)) a‖+1
  refine ⟨B,by dsimp [B] <;> positivity,?_⟩
  have HH := (Metric.tendsto_nhds (β := E×E)
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hh (1:ℝ) zero_lt_one
  filter_upwards [HH] with q hq
  have hd : ‖fderiv ℝ (fderiv ℝ (C q.1)) q.2-fderiv ℝ (fderiv ℝ (C a)) a‖<1 := by
    simpa only [dist_eq_norm] using hq
  have hn := norm_le_norm_sub_add (fderiv ℝ (fderiv ℝ (C q.1)) q.2)
    (fderiv ℝ (fderiv ℝ (C a)) a)
  dsimp only [B]
  linarith only [hd,hn]

lemma smooth_kernel_local_data {C : E → E → ℝ} {a:E}
    (hc : ContDiffAt ℝ ∞ (Function.uncurry C) (a,a)) :
    ∃ K : ℝ≥0, ∃ B : ℝ,0≤B ∧ ∃ r>0,
      (∀ y∈ball a r,∀ z∈ball a r,ContDiffAt ℝ 2 (C y) z) ∧
      (∀ y∈ball a r,∀ z∈ball a r,‖fderiv ℝ (fderiv ℝ (C y)) z‖≤B) ∧
      LipschitzOnWith K (fun q : E×E => fderiv ℝ (C q.1) q.2)
        (ball a r×ˢball a r) := by
  have hd := ContDiffAt.partial_snd_fderiv hc
  obtain ⟨K,U,hU,hK⟩ := (hd.of_le (by norm_num : (1:WithTop ℕ∞)≤∞)).exists_lipschitzOnWith
  obtain ⟨B,hB,hH⟩ := smooth_kernel_second_locally_bounded hc
  have hs : ∀ᶠ q:E×E in 𝓝 (a,a),ContDiffAt ℝ 2 (C q.1) q.2 := by
    filter_upwards [(hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)] with q hq
    exact hq.comp (f := fun z:E => (q.1,z)) q.2 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (hH.and hs))
  have H (y z:E) (hy:y∈ball a r) (hz:z∈ball a r) :=
    hrU (show (y,z)∈ball (a,a) r from by rw [←ball_prod_same]; exact ⟨hy,hz⟩)
  refine ⟨K,B,hB,r,hr,?_,?_,?_⟩
  · exact fun y hy z hz => (H y z hy hz).2.2
  · exact fun y hy z hz => (H y z hy hz).2.1
  · exact hK.mono (fun q hq => (H q.1 q.2 hq.1 hq.2).1)

lemma smooth_kernel_local_bounds {C : E → E → ℝ} {a:E}
    (hc : ContDiffAt ℝ ∞ (Function.uncurry C) (a,a)) :
    ∃ K B : ℝ,0≤K ∧ 0≤B ∧ ∃ r>0,
      (∀ y∈ball a r,∀ z∈ball a r,ContDiffAt ℝ 2 (C y) z) ∧
      (∀ y∈ball a r,∀ z∈ball a r,∀ z'∈ball a r,
        |C y z'-C y z-fderiv ℝ (C y) z (z'-z)|≤B*‖z'-z‖^2) ∧
      (∀ y∈ball a r,∀ y'∈ball a r,∀ z∈ball a r,∀ z'∈ball a r,
        |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖) := by
  obtain ⟨K,B,hB,r,hr,hs,hH,hK⟩ := smooth_kernel_local_data hc
  refine ⟨K,B,K.coe_nonneg,hB,r,hr,hs,?_,?_⟩
  · intro y hy z hz z' hz'
    exact first_order_remainder_le_of_hessian_bound (f := C y) (convex_ball a r) hB
      (hs y hy) (hH y hy) hz hz'
  · exact kernel_rectangle_of_partial_lipschitz (convex_ball a r)
      (fun y hy z hz => (hs y hy z hz).differentiableAt (by norm_num)) hK
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_FamilyShortEnvelope
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma uniform_family_short_envelope_data {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    {Lφ : ℝ≥0} (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s)))
    (A B : ℝ) (a : M) :
    ∃ J JY : ℝ≥0,∃ r>0,∃ δ>0,∀ p∈Kp,∀ u : M → ℝ,Continuous u →
      (∀ y,cTransform u y∈Icc A B) → ∀ t : ℝ,0<t → t<δ →
      let F := fun z : Model n => t*hopfLax t (fun y => Φ (p,cTransform u y))
        ((extChartAt 𝓘(ℝ,Model n) a).symm z)
      (∀ z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,DifferentiableAt ℝ F z) ∧
      LipschitzOnWith J (fderiv ℝ F) (ball (extChartAt 𝓘(ℝ,Model n) a a) (r/4)) ∧
      ∃ Y0 : Model n → M,
        LipschitzOnWith JY (fun z => extChartAt 𝓘(ℝ,Model n) a (Y0 z))
          (ball (extChartAt 𝓘(ℝ,Model n) a a) r) ∧
        ∀ z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          Y0 z∈(extChartAt 𝓘(ℝ,Model n) a).source ∧
          ∀ y:M,hopfLax t (fun y => Φ (p,cTransform u y))
            ((extChartAt 𝓘(ℝ,Model n) a).symm z)=
            Φ (p,cTransform u y)+cost y ((extChartAt 𝓘(ℝ,Model n) a).symm z)/t ↔ y=Y0 z := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let C : Model n → Model n → ℝ := fun y z => chartCost a (χ.symm z) y
  have hc : ContDiffAt ℝ ∞ (Function.uncurry C) (χ a,χ a) :=
    (chartCost_pair_contDiffAt_diagonal (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)).comp
      (χ a,χ a) (contDiffAt_snd.prodMk contDiffAt_fst)
  obtain ⟨K,H,hK,hH,Rk,hRk,hCs,hrem,hcross⟩ := smooth_kernel_local_bounds hc
  obtain ⟨m,hm,R0,hR0,V0,hV0,δ0,hδ0,hR0T,hs⟩ :=
    uniform_family_short_action_strongConvex (n := n) hΦ hKp hmono A B a
  let R := min R0 (Rk/2)
  have hR : 0<R := lt_min hR0 (half_pos hRk)
  have hS0 : closedBall (χ a) R⊆closedBall (χ a) R0 :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hSk : closedBall (χ a) R⊆ball (χ a) Rk :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hRk))
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  obtain ⟨δ1,hδ1,V1,hV1,hlocal⟩ := uniform_hopfLax_chart_localization (n := n) (Lφ*D) a hR
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hV0 (inter_mem hV1 (ball_mem_nhds (χ a) hRk)))
  refine ⟨Real.toNNReal (6*(H+K^2/m)),Real.toNNReal (2*K/m),r,hr,min δ0 δ1,lt_min hδ0 hδ1,?_⟩
  intro p hp u hu hb t ht htδ
  let w : M → ℝ := fun y => Φ (p,cTransform u y)
  have hw : LipschitzWith (Lφ*D) w := (hφL p hp).comp
    (cTransform_lipschitz hu (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)))
  let F : Model n → ℝ := fun z => t*hopfLax t w (χ.symm z)
  let W : Model n → ℝ := fun y => t*w (χ.symm y)
  choose Y0 hY0 hmin0 using (fun z : Model n => exists_hopfLax_minimizer hw.continuous t (χ.symm z))
  let Y : Model n → Model n := fun z => χ (Y0 z)
  have hycoord (z:Model n) (hz:z∈ball (χ a) r) :
      Y0 z∈χ.source ∧ Y z∈ball (χ a) R :=
    hlocal t ht (lt_of_lt_of_le htδ (min_le_right _ _)) z (hrV hz).2.1 w hw (Y0 z) (hY0 z)
  have hY : ∀ z∈ball (χ a) r,Y z∈closedBall (χ a) R :=
    fun z hz => ball_subset_closedBall ((hycoord z hz).2)
  have hval : ∀ z∈ball (χ a) r,F z=W (Y z)+C (Y z) z := by
    intro z hz
    dsimp only [F,W,C,chartCost,Y]
    rw [χ.left_inv (hycoord z hz).1,hY0 z]
    field_simp
  have hmin : ∀ z∈ball (χ a) r,∀ y∈closedBall (χ a) R,F z≤W y+C y z := by
    intro z hz y hy
    have HH := mul_le_mul_of_nonneg_left (hopfLax_le hw.continuous t (χ.symm z) (χ.symm y)) ht.le
    dsimp only [F,W,C,chartCost]
    simpa only [mul_add,←mul_div_assoc,mul_div_cancel_left₀ _ ht.ne'] using HH
  have hstrong : ∀ z∈ball (χ a) r,
      StrongConvexOn (closedBall (χ a) R) m (fun y => W y+C y z) := by
    intro z hz
    have HH := hs p hp u hu hb t ht (lt_of_lt_of_le htδ (min_le_left _ _)) z (hrV hz).1
    exact ⟨convex_closedBall _ _,fun {x} hx {y} hy {p} {q} hp hq hsum =>
      HH.2 (hS0 hx) (hS0 hy) hp hq hsum⟩
  have HC : ∀ y∈closedBall (χ a) R,∀ y'∈closedBall (χ a) R,
      ∀ z∈ball (χ a) r,∀ z'∈ball (χ a) r,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖ :=
    fun y hy y' hy' z hz z' hz' => hcross y (hSk hy) y' (hSk hy')
      z (hrV hz).2.2 z' (hrV hz').2.2
  have HR : ∀ z∈ball (χ a) r,∀ z'∈ball (χ a) r,
      |C (Y z) z'-C (Y z) z-fderiv ℝ (C (Y z)) z (z'-z)|≤H*‖z'-z‖^2 :=
    fun z hz z' hz' => hrem (Y z) (hSk (hY z hz)) z (hrV hz).2.2 z' (hrV hz').2.2
  obtain ⟨hd,hLip⟩ := strong_envelope_C11 hr hm hK hH hY hval hmin hstrong HC HR
  refine ⟨fun z hz => (hd z hz).differentiableAt,hLip,Y0,
    strong_envelope_minimizer_lipschitz hm hK hY hval hmin hstrong HC,?_⟩
  intro z hz
  refine ⟨(hycoord z hz).1,?_⟩
  intro y
  constructor
  · intro hy
    have hym := hlocal t ht (lt_of_lt_of_le htδ (min_le_right _ _))
      z (hrV hz).2.1 w hw y hy
    have hyeq : F z=W (χ y)+C (χ y) z := by
      dsimp only [F,W,C,chartCost]
      rw [χ.left_inv hym.1,hy]
      field_simp
      rfl
    have he := strongly_convex_minimizer_unique hm (hstrong z hz) (hY z hz)
      (ball_subset_closedBall hym.2)
      (show IsMinOn (fun y => W y+C y z) (closedBall (χ a) R) (Y z) from by
        intro y' hy'
        change W (Y z)+C (Y z) z≤W y'+C y' z
        rw [←hval z hz]
        exact hmin z hz y' hy') ((hval z hz).symm.trans hyeq)
    exact χ.injOn hym.1 (hycoord z hz).1 he.symm
  · rintro rfl
    exact hY0 z

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ModifiedEnvelopeRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma differentiableAt_of_const_mul {f : E → ℝ} {t : ℝ} (ht : t≠0) {x:E}
    (hd : DifferentiableAt ℝ (fun z => t*f z) x) :
    HasFDerivAt f (t⁻¹ • fderiv ℝ (fun z => t*f z) x) x := by
  have H := hd.hasFDerivAt.const_mul t⁻¹
  simpa only [←mul_assoc,inv_mul_cancel₀ ht,one_mul] using H

lemma C11_const_mul_cancel {f : E → ℝ} {S : Set E} {t : ℝ} {K : ℝ≥0}
    (ht : t≠0) (hd : ∀ x∈S,DifferentiableAt ℝ (fun z => t*f z) x)
    (hLip : LipschitzOnWith K (fderiv ℝ (fun z => t*f z)) S) :
    (∀ x∈S,DifferentiableAt ℝ f x) ∧
      LipschitzOnWith (‖t⁻¹‖₊*K) (fderiv ℝ f) S := by
  have H (x:E) (hx:x∈S) := differentiableAt_of_const_mul ht (hd x hx)
  refine ⟨fun x hx => (H x hx).differentiableAt,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [(H x hx).fderiv,(H y hy).fderiv,dist_eq_norm,←smul_sub,norm_smul]
  have HH := mul_le_mul_of_nonneg_left (hLip.dist_le_mul x hx y hy) (norm_nonneg t⁻¹)
  simpa only [dist_eq_norm,NNReal.coe_mul,coe_nnnorm,mul_assoc] using HH

end

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hopfLax_lipschitz {u : M → ℝ} (hu : Continuous u) {D : ℝ≥0}
    (hD : ∀ x y : M, dist x y≤D) {t : ℝ} (ht : 0<t) :
    LipschitzWith (D/Real.toNNReal t) (hopfLax t u) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [hopfLax_eq_neg_transform hu ht,hopfLax_eq_neg_transform hu ht,
    Real.dist_eq,←sub_div,abs_div,neg_sub_neg,abs_sub_comm,abs_of_pos ht]
  have H := (cTransform_lipschitz (v := fun x => t*u x) (continuous_const.mul hu) hD).dist_le_mul x y
  rw [Real.dist_eq] at H
  calc
    _ ≤ (D:ℝ)*dist x y/t := div_le_div_of_nonneg_right H ht.le
    _ = _ := by rw [NNReal.coe_div,Real.coe_toNNReal _ ht.le]; ring

omit [Nonempty M] in
lemma coordinateBackward_contMDiffAt {a : M} {q : ℝ × Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.2.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,ℝ × Model n × (Model n →L[ℝ] ℝ)) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.2.1 hg
  have hz : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.2) q :=
    contDiffAt_snd.comp q contDiffAt_snd
  have hv := (contDiffAt_fst.neg.smul ((hi.comp q hz).clm_apply hl))
  exact (movingNormal_contMDiffAt hq).comp q (hz.prodMk hv).contMDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPole
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

lemma WeakMTW.hopfPole_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    hopfLax t u z=u (hopfPole (n := n) t u z)+cost (hopfPole (n := n) t u z) z/t := by
  rw [hdual.1] at hu ⊢
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  have He : hopfPole (n := n) t (cTransform v) z=q.1.1 := by
    change hopfPole (n := n) t (cTransform v) (graphProjection (cTransform v) t q)=q.1.1 at H
    rwa [hq] at H
  rw [He,←hq]
  exact hmtw.hopfLax_graph_value hv ht ht1 q

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_PoleLipschitz
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.uniform_hopfPole_lipschitz (hmtw : WeakMTW (n := n) (M := M)) (a : M) :
    ∃ C>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ t : ℝ, 1/2≤t → t<1 → ∀ u v : M → ℝ, Continuous u → Continuous v →
        IsCostDualPair u v →
        LipschitzOnWith (Real.toNNReal (C/(1-t)))
          (fun z => hopfPole (n := n) t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
          (ball (extChartAt 𝓘(ℝ,Model n) a a) r) := by
  let : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hB,r₁,hr₁,hT₁,H⟩ := hmtw.uniform_hopfLax_C11 a
  let D : ℝ≥0 := Real.toNNReal (Metric.diam (univ : Set M))
  have hD : ∀ x y : M, dist x y≤D := by
    intro x y
    rw [Real.coe_toNNReal _ Metric.diam_nonneg]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  obtain ⟨L,r₂,hr₂,hT₂,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let r := min (r₁/8) (r₂/2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hr₁' : r < r₁/4 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr₂' : r < r₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hT : closedBall (χ a) r ⊆ χ.target := fun z hz =>
    hT₁ ((closedBall_subset_ball (by linarith : r < r₁)) hz)
  let K : Set (ℝ × Model n × (Model n →L[ℝ] ℝ)) :=
    Icc (1/2) 1 ×ˢ (closedBall (χ a) r ×ˢ closedBall 0 (2*(D:ℝ)*L))
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨A,hA⟩ := contMDiffOn_exists_lipschitzOn_compact hK
    (f := coordinateBackward (n := n) a)
    (fun q hq => (coordinateBackward_contMDiffAt (hT hq.2.1)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let C : ℝ := (A:ℝ)*(1+12*B)+1
  have hC : 0<C := by dsimp [C] <;> positivity
  refine ⟨C,hC,r,hr,fun z hz => hT (ball_subset_closedBall hz),?_⟩
  intro t ht ht1 u v hu hv hdual
  have ht0 : 0<t := by linarith
  have hs : 0<1-t := sub_pos.mpr ht1
  let f : Model n → ℝ := fun z => hopfLax t u (χ.symm z)
  have hf := (hopfLax_lipschitz hu hD ht0).comp_lipschitzOnWith hL
  have hd_bound : ∀ z∈ball (χ a) r, ‖fderiv ℝ f z‖≤2*(D:ℝ)*L := by
    intro z hz
    have hz₂ : z∈ball (χ a) r₂ := ball_subset_ball hr₂'.le hz
    have hn := norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz₂) hf
    have hdiv : (D:ℝ)/t≤2*D := (div_le_iff₀ ht0).mpr (by nlinarith [D.coe_nonneg])
    calc
      _≤↑((D/Real.toNNReal t)*L : ℝ≥0) := hn
      _=(D:ℝ)/t*L := by rw [NNReal.coe_mul,NNReal.coe_div,Real.coe_toNNReal _ ht0.le]
      _≤_ := mul_le_mul_of_nonneg_right hdiv L.coe_nonneg
  have hd_lip := (H t ht0 ht1 u v hu hv hdual).2
  have hcoef : 6*(B/t+B/(1-t)) ≤ (12*B)/(1-t) := by
    have hdualT : B/t≤B/(1-t) := div_le_div_of_nonneg_left hB.le hs (by linarith)
    calc
      _ ≤ 6*(B/(1-t)+B/(1-t)) := by linarith
      _ = _ := by ring
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro z hz w hw
  have hzK : (t,z,fderiv ℝ f z)∈K :=
    ⟨⟨ht,ht1.le⟩,ball_subset_closedBall hz,by simpa only [mem_closedBall,dist_zero_right] using hd_bound z hz⟩
  have hwK : (t,w,fderiv ℝ f w)∈K :=
    ⟨⟨ht,ht1.le⟩,ball_subset_closedBall hw,by simpa only [mem_closedBall,dist_zero_right] using hd_bound w hw⟩
  have Hz := hmtw.coordinateBackward_eq_pole hu hv hdual ht0 ht1 (hT (ball_subset_closedBall hz))
  have Hw := hmtw.coordinateBackward_eq_pole hu hv hdual ht0 ht1 (hT (ball_subset_closedBall hw))
  change dist (hopfPole (n := n) t u (χ.symm z)) (hopfPole (n := n) t u (χ.symm w))≤_
  rw [←Hz,←Hw]
  have hder := hd_lip.dist_le_mul z (ball_subset_ball hr₁'.le hz)
    w (ball_subset_ball hr₁'.le hw)
  rw [Real.coe_toNNReal _ (by positivity)] at hder
  have hd : dist (t,z,fderiv ℝ f z) (t,w,fderiv ℝ f w)≤
      ((1+12*B)/(1-t))*dist z w := by
    rw [Prod.dist_eq,dist_self,Prod.dist_eq,max_eq_right (le_max_of_le_left dist_nonneg)]
    apply max_le
    · have h1 : 1≤(1+12*B)/(1-t) := (le_div_iff₀ hs).mpr (by nlinarith)
      simpa using mul_le_mul_of_nonneg_right h1 (dist_nonneg (x := z) (y := w))
    · calc
        _≤6*(B/t+B/(1-t))*dist z w := hder
        _≤((12*B)/(1-t))*dist z w := mul_le_mul_of_nonneg_right hcoef dist_nonneg
        _≤((1+12*B)/(1-t))*dist z w := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hs.le) dist_nonneg
  calc
    _≤(A:ℝ)*dist (t,z,fderiv ℝ f z) (t,w,fderiv ℝ f w) := hA.dist_le_mul _ hzK _ hwK
    _≤(A:ℝ)*(((1+12*B)/(1-t))*dist z w) := mul_le_mul_of_nonneg_left hd A.coe_nonneg
    _≤(C/(1-t))*dist z w := by
      have hc : (A:ℝ)*((1+12*B)/(1-t))≤C/(1-t) := by
        rw [←mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hs.le
        dsimp [C] <;> linarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (dist_nonneg (x := z) (y := w))
    _=_ := by rw [Real.coe_toNNReal _ (div_nonneg hC.le hs.le)]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ChartLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

lemma chart_spray_hasDerivAt (a : M) (z : TangentBundle 𝓘(ℝ,Model n) M) {t : ℝ}
    (ht : (sprayFlow t z).1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    HasDerivAt (fun s => extChartAt 𝓘(ℝ,Model n) a (sprayFlow s z).1)
      (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a)
        (sprayFlow t z).1 (sprayFlow t z).2) t := by
  have hsrc : (sprayFlow t z).1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using ht
  have projectedDeriv :=
    (ContinuousLinearMap.fst ℝ (Model n) (Model n)).hasFDerivAt.comp_hasDerivAt t
      (sprayFlow_chart_hasDerivAt (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z ht)
  change HasDerivAt (fun s => extChartAt 𝓘(ℝ,Model n) a (sprayFlow s z).1)
    (tangentCoordChange 𝓘(ℝ,Model n) (sprayFlow t z).1 a
      (sprayFlow t z).1 (sprayFlow t z).2) t at projectedDeriv
  apply projectedDeriv.congr_deriv
  symm
  change (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (chartAt (Model n) a)
    (sprayFlow t z).1) (sprayFlow t z).2 = _
  rw [mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

variable [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_lipschitzOn_chart (a : M) :
    ∃ C : ℝ≥0, ∃ r>0, ball a r⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) (ball a r) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hC,H⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,Model n) a
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) H)
  let Cnn : ℝ≥0 := ⟨C,hC.le⟩
  refine ⟨Cnn,R/3,by positivity,?_,?_⟩
  · exact fun x hx => (hsub ((ball_subset_ball (by linarith : R/3≤R)) hx)).1
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) x y
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hpN : ‖p‖=dist x y := by rw [←he]; exact hp.symm
  have hpath : ∀ t∈Icc (0:ℝ) 1, (sprayFlow t z).1∈ball a R := by
    intro t ht
    have hD := dist_sprayFlow_le z 0 t
    simp only [sprayFlow_zero,zero_sub,abs_neg,abs_of_nonneg ht.1] at hD
    change dist x (sprayFlow t z).1≤t*‖p‖ at hD
    have hD' : dist x (sprayFlow t z).1≤dist x y :=
      hD.trans (by rw [←hpN]; exact mul_le_of_le_one_left (norm_nonneg _) ht.2)
    have hxy := dist_triangle x a y
    have hax : dist x a<R/3 := hx
    have hay : dist y a<R/3 := hy
    have htri := dist_triangle (sprayFlow t z).1 x a
    rw [dist_comm (sprayFlow t z).1 x] at htri
    rw [dist_comm a y] at hxy
    change dist (sprayFlow t z).1 a<R
    linarith
  let γ := fun t : ℝ => extChartAt 𝓘(ℝ,Model n) a (sprayFlow t z).1
  let dγ : ℝ → Model n := fun t => mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n)
    (extChartAt 𝓘(ℝ,Model n) a) (sprayFlow t z).1 (sprayFlow t z).2
  have hd : ∀ t∈Icc (0:ℝ) 1, HasDerivWithinAt γ (dγ t) (Icc 0 1) t := by
    intro t ht
    exact (chart_spray_hasDerivAt a z (hsub (hpath t ht)).1).hasDerivWithinAt
  have hb : ∀ t∈Icc (0:ℝ) 1, ‖dγ t‖≤C*‖p‖ := by
    intro t ht
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    rw [sprayFlow_speed]
    exact mul_le_mul_of_nonneg_right (hsub (hpath t ht)).2.le (norm_nonneg _)
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hd (fun t ht => hb t ⟨ht.1,ht.2.le⟩)
  have he1 : (sprayFlow 1 z).1=y := by
    simpa only [z,←riemannianExp_eq_sprayFlow] using he
  have he0 : (sprayFlow 0 z).1=x := by rw [sprayFlow_zero]
  change dist (extChartAt 𝓘(ℝ,Model n) a x) (extChartAt 𝓘(ℝ,Model n) a y)≤C*dist x y
  simpa only [γ,he1,he0,←dist_eq_norm,dist_comm,hpN] using hfin

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FamilyComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma WeakMTW.family_comparison_local_data_oai (hmtw : WeakMTW (n := n) (M := M))
    {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {Kp : Set P} (hKp : IsCompact Kp)
    (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) {Lφ : ℝ≥0}
    (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ R>0,∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ ψ:ℝ → ℝ,Continuous ψ → ∀ τ:ℝ,0<τ → τ<1/2 → τ<δ →
      ∀ c:M,extChartAt 𝓘(ℝ,Model n) a c∈ball (extChartAt 𝓘(ℝ,Model n) a a) R →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let w := fun y=>ψ (cTransform u y)
      let g := fun y=>Φ (p,cTransform u y)
      let F := chartOuterEnvelope w (1-τ) a
      let G := chartCenterEnvelope g (1-τ) a
      let pole : Model n → M := chartActualPole w (1-τ) a
      let χP := extChartAt 𝓘(ℝ,Model n) (pole (χ c))
      ∃ r>0,∃ JF JG JY JP:ℝ≥0,∃ Y:Model n → M,
        (∀ z∈ball (χ c) r,DifferentiableAt ℝ F z) ∧
        (∀ z∈ball (χ c) r,DifferentiableAt ℝ G z) ∧
        LipschitzOnWith JF (fderiv ℝ F) (ball (χ c) r) ∧
        LipschitzOnWith JG (fderiv ℝ G) (ball (χ c) r) ∧
        LipschitzOnWith JY (fun z=>χ (Y z)) (ball (χ c) r) ∧
        LipschitzOnWith JP (fun z=>χP (pole z)) (ball (χ c) r) ∧
        ∀ z∈ball (χ c) r,
          Y z∈χ.source ∧ pole z∈χP.source ∧
          (∀ y:M,G z=g y+cost y (χ.symm z)/(1-(1-τ)) ↔ y=Y z) ∧
          F z=cTransform w (pole z)+cost (pole z) (χ.symm z)/(1-τ) := by
  obtain ⟨J,JY,Rg,hRg,δ,hδ,HG⟩ :=
    uniform_family_short_envelope_data (n := n) hΦ hKp hmono hφL A B a
  obtain ⟨BF,hBF,Rf,hRf,hTf,HF⟩ := hmtw.uniform_hopfLax_C11 a
  obtain ⟨CP,hCP,Rp,hRp,hTp,HP⟩ := hmtw.uniform_hopfPole_lipschitz a
  let R := min (Rg/8) (min (Rf/8) (Rp/2))
  have hR : 0<R := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨R,hR,δ,hδ,?_⟩
  intro p hp u hu hb ψ hψ τ hτ hτhalf hτδ c hc
  dsimp only
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let w : M → ℝ := fun y=>ψ (cTransform u y)
  have hw : Continuous w := hψ.comp (continuous_cTransform hu)
  have hdual : IsCostDualPair (cTransform w) (cTransform (cTransform w)) :=
    ⟨(cTransform_triple hw).symm,rfl⟩
  have ht : 0<1-τ := by linarith
  have ht1 : 1-τ<1 := by linarith
  obtain ⟨hgdiff,hgl,Y,hY,hy⟩ := HG p hp u hu hb τ hτ hτδ
  let G : Model n → ℝ := fun z=>hopfLax τ (fun y=>Φ (p,cTransform u y)) (χ.symm z)
  have hsmall : ball (χ a) (Rg/4)⊆ball (χ a) Rg := ball_subset_ball (by linarith)
  obtain ⟨hgD,hgL⟩ := C11_const_mul_cancel (f := G) hτ.ne'
    (fun z hz=>hgdiff z (hsmall hz)) hgl
  obtain ⟨hfD,hfL⟩ := HF (1-τ) ht ht1 (cTransform w) (cTransform (cTransform w))
    (continuous_cTransform hw) (continuous_cTransform (continuous_cTransform hw)) hdual
  let pole : Model n → M := chartActualPole w (1-τ) a
  have hpL : LipschitzOnWith (Real.toNNReal (CP/(1-(1-τ)))) pole (ball (χ a) Rp) :=
    HP (1-τ) (by linarith) ht1 (cTransform w) (cTransform (cTransform w))
      (continuous_cTransform hw) (continuous_cTransform (continuous_cTransform hw)) hdual
  have hrg : R≤Rg/8 := min_le_left _ _
  have hrf : R≤Rf/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrp : R≤Rp/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hcRp : χ c∈ball (χ a) Rp := (ball_subset_ball (by linarith : R≤Rp)) hc
  have hpC : ContinuousAt pole (χ c) := hpL.continuousOn.continuousAt (isOpen_ball.mem_nhds hcRp)
  obtain ⟨AP,rP,hrP,hpsrc,hpchart⟩ := exists_lipschitzOn_chart (n := n) (pole (χ c))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (isOpen_ball.mem_nhds hc) (hpC.preimage_mem_nhds (ball_mem_nhds (pole (χ c)) hrP)))
  have hsub : ball (χ c) r⊆ball (χ a) R := fun z hz=>(hrsub hz).1
  have himage : ∀ z∈ball (χ c) r,pole z∈ball (pole (χ c)) rP := fun z hz=>(hrsub hz).2
  have hrg4 : ball (χ c) r⊆ball (χ a) (Rg/4) := hsub.trans (ball_subset_ball (by linarith))
  have hrf4 : ball (χ c) r⊆ball (χ a) (Rf/4) := hsub.trans (ball_subset_ball (by linarith))
  have hrp' : ball (χ c) r⊆ball (χ a) Rp := hsub.trans (ball_subset_ball (by linarith))
  have htau : 1-(1-τ)=τ := by ring
  have heq : chartCenterEnvelope (n := n) (fun y=>Φ (p,cTransform u y)) (1-τ) a=G := by
    funext z
    change hopfLax (1-(1-τ)) _ _=hopfLax τ _ _
    rw [htau]
  refine ⟨r,hr,Real.toNNReal (6*(BF/(1-τ)+BF/(1-(1-τ)))),‖τ⁻¹‖₊*J,JY,
    AP*Real.toNNReal (CP/(1-(1-τ))),Y,?_,?_,hfL.mono hrf4,?_,
    hY.mono (hrg4.trans hsmall),hpchart.comp (hpL.mono hrp') himage,?_⟩
  · exact fun z hz=>hfD z ((hsub.trans (ball_subset_ball (by linarith : R≤Rf))) hz)
  · rw [heq]
    exact fun z hz=>hgD z (hrg4 hz)
  · rw [heq]
    exact hgL.mono hrg4
  · intro z hz
    have hyz := hy z (hsmall (hrg4 hz))
    refine ⟨hyz.1,hpsrc (himage z hz),?_,hmtw.hopfPole_minimizer
      (continuous_cTransform hw) (continuous_cTransform (continuous_cTransform hw)) hdual ht ht1 _⟩
    simpa only [chartCenterEnvelope,htau,G,χ] using hyz.2
end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data_oai.{u_1, u_2} := @OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data_oai.{u_1, u_2}
