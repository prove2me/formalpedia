-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:57.683416+00:00
-- url     : https://prove2.me/submissions/f131f27e-bd92-4ce1-a7e9-003623454e9e

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
import Definitions.Def_OAIQ232A026
import Theorems.Thm_OAI_WeakMTWTransport_contact_selection_chart_differential_full

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Subgradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open MeasureTheory

lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {s : Set X} {P : X → Prop}
    (hloc : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∀ᵐ z ∂μ, z ∈ U → P z)) :
    ∀ᵐ z ∂μ, z ∈ s → P z := by
  classical
  choose U hUo hxU hUae using fun x : s => hloc x x.2
  have hcov : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨c,hc,hcover⟩ := (IsLindelof.of_coe (s := s)).elim_countable_subcover U hUo hcov
  have hnull : μ (⋃ i ∈ c, {z | z ∈ U i ∧ ¬P z}) = 0 := by
    apply (measure_biUnion_null_iff hc).mpr
    intro i _
    simpa only [Classical.not_imp] using (ae_iff.mp (hUae i))
  apply ae_iff.mpr
  apply measure_mono_null _ hnull
  intro z hz
  have hz' : z ∈ s ∧ ¬P z := by simpa only [mem_ofPred_eq,Classical.not_imp] using hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hcover hz'.1)
  exact mem_iUnion₂.mpr ⟨i,hi,hzi,hz'.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_AEContacts
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
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AEContacts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma active_log_derivative {v : M → ℝ} (hv : Continuous v) {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈activeLogs (n := n) v x) :
    HasFDerivAt (fun h => cTransform v (riemannianExp x h)) (innerSL ℝ p) 0 := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    (-2:ℝ)*(normalCost x ((1/2:ℝ) • p) h-normalCost x ((1/2:ℝ) • p) 0)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hID).sub_const
      (normalCost x ((1/2:ℝ) • p) 0)).const_smul (-2:ℝ)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    ring
  have hU : DifferentiableAt ℝ (fun h : TangentSpace 𝓘(ℝ,Model n) x => cTransform v (riemannianExp x h)) 0 := by
    have hf : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp (n := n) x 0) := by simpa only [riemannianExp_zero] using hDiff
    exact (hf.comp 0 ((contMDiff_riemannianExp_fiber x).contMDiffAt.mdifferentiableAt
      (by simp))).differentiableAt
  have hMin : IsLocalMin (fun h => cTransform v (riemannianExp x h)-f h) 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hs := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    have he : f h = -(cost (riemannianExp x h) (riemannianExp x ((1/2:ℝ) • p)) -
        cost x (riemannianExp x ((1/2:ℝ) • p))) / (1/2:ℝ) := by
      dsimp [f,normalCost]
      rw [riemannianExp_zero]
      ring
    change cTransform v (riemannianExp x 0)-f 0≤
      cTransform v (riemannianExp x h)-f h
    simp only [riemannianExp_zero,show f 0=0 by simp [f],sub_zero,he]
    linarith only [hs]
  have he := sub_eq_zero.mp (hMin.hasFDerivAt_eq_zero (hU.hasFDerivAt.sub hD))
  rw [←he]
  exact hU.hasFDerivAt

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_unique_of_mdifferentiable {v : M → ℝ} (hv : Continuous v) {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {y z : M} (hy : contactGap (cTransform v) v x y=0)
    (hz : contactGap (cTransform v) v x z=0) : y=z := by
  obtain ⟨p,hp,hep⟩ := exists_minimizing_vector (n := n) x y
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x z
  have hpA : p∈activeLogs (n := n) v x := ⟨hp,by simpa only [hep] using hy⟩
  have hqA : q∈activeLogs (n := n) v x := ⟨hq,by simpa only [heq] using hz⟩
  have H := (active_log_derivative hv hDiff hpA).unique (active_log_derivative hv hDiff hqA)
  have hpq : p=q := by
    apply ext_inner_right ℝ
    intro h
    exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) H
  rw [←hep,←heq,hpq]

end AEContacts
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Inner
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasQuadraticExpansion_iff_isLittleO {f : E → ℝ} {p : E} {A : E →L[ℝ] E} :
    HasQuadraticExpansion f p A ↔
      (fun h => f h - quadraticTaylor (f 0) p A h) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro H c hc
    obtain ⟨d,hd,hbound⟩ := H c hc
    filter_upwards [Metric.ball_mem_nhds (0:E) hd] with h hh
    simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      hbound h (by simpa only [Metric.mem_ball,dist_zero_right] using hh)
  · intro H c hc
    obtain ⟨d,hd,hbound⟩ := Metric.mem_nhds_iff.mp (H hc)
    refine ⟨d,hd,?_⟩
    intro h hh
    simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      hbound (show h ∈ Metric.ball (0:E) d by simpa only [Metric.mem_ball,dist_zero_right] using hh)
end Inner
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactSelection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ContactSelection
variable {M : Type*} [MetricSpace M] [CompactSpace M]

lemma contact_selection_continuousAt {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    {T : M → M} (hT : ∀ z, contactGap u v z (T z)=0) {x : M}
    (hx : ∀ y, contactGap u v x y=0 → y=T x) : ContinuousAt T x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A := {z : M×M | contactGap u v z.1 z.2=0 ∧ z.2∉ball (T x) ε}
  have hg : Continuous (fun z : M×M => contactGap u v z.1 z.2) :=
    ((hu.comp continuous_fst).add
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).add
      (hv.comp continuous_snd)
  have hA : IsClosed A := (isClosed_eq hg continuous_const).inter
    (isOpen_ball.preimage continuous_snd).isClosed_compl
  have hB : IsClosed (Prod.fst '' A) := isClosedMap_fst_of_compactSpace A hA
  have hxB : x∉Prod.fst '' A := by
    rintro ⟨⟨z,y⟩,⟨hzy,hy⟩,rfl⟩
    exact hy ((hx y hzy) ▸ mem_ball_self hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hxB)
  refine ⟨δ,hδ,fun {z} hz => ?_⟩
  by_contra hbad
  exact hball hz ⟨(z,T z),⟨hT z,hbad⟩,rfl⟩

variable [Nonempty M]

lemma contactSelection_mem {v : M → ℝ} (hv : Continuous v) (x : M) :
    contactGap (cTransform v) v x (contactSelection hv x)=0 :=
  (cTransform_gap_zero hv x).choose_spec

end ContactSelection

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section RegularContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteRegularContact_rf75f80_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [MeasurableSpace M] [BorelSpace M] in
lemma contactSelection_continuousAt_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) :
    ContinuousAt (contactSelection hv) x := by
  apply contact_selection_continuousAt (continuous_cTransform hv) hv (contactSelection_mem hv)
  exact fun y hy => contact_unique_of_mdifferentiable hv hD hy (contactSelection_mem hv x)

end RegularContact
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Add
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma HasQuadraticExpansion.add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → ℝ} {p q : E} {H K : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p H) (hg : HasQuadraticExpansion g q K) :
    HasQuadraticExpansion (fun d => f d+g d) (p+q) (H+K) := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf hg ⊢
  convert! hf.add hg using 1
  all_goals try with_reducible_and_instances rfl
  funext d
  simp only [quadraticTaylor,inner_add_left,add_apply]
  ring

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Taylor
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

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.hessian_le_of_upper_support {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hexp : HasQuadraticExpansion f p A) {eta R : ℝ}
    (hR : 0 < R)
    (hu : ∀ h : E, ‖h‖ < R →
      f h ≤ f 0+inner ℝ p h+eta/2*‖h‖^2) :
    ∀ e : E, inner ℝ (A e) e ≤ eta*‖e‖^2 := by
  intro e
  have hbound (eps : ℝ) (heps : 0 < eps) :
      inner ℝ (A e) e ≤ (eta+2*eps)*‖e‖^2 := by
    obtain ⟨d,hd,hrem⟩ := hexp eps heps
    let t : ℝ := min R d / (2*(‖e‖+1))
    have ht : 0 < t := by dsimp [t] <;> positivity
    have hteq : t*(2*(‖e‖+1)) = min R d :=
      div_mul_cancel₀ _ (by positivity)
    have htn : t*‖e‖ < min R d := by nlinarith [norm_nonneg e]
    have hnorm : ‖t • e‖ = t*‖e‖ := norm_smul_of_nonneg ht.le _
    have hi := hu (t • e) (by rw [hnorm]; exact lt_of_lt_of_le htn (min_le_left _ _))
    have hr := (abs_le.mp (hrem (t • e) (by
      rw [hnorm]; exact lt_of_lt_of_le htn (min_le_right _ _)))).1
    simp only [quadraticTaylor,map_smul,real_inner_smul_left,real_inner_smul_right,hnorm] at hr hi
    have hscale : t^2 * inner ℝ (A e) e ≤ t^2 * ((eta+2*eps)*‖e‖^2) := by
      nlinarith
    nlinarith [sq_pos_of_pos ht]
  have hcl : (0:ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨le_rfl,zero_le_one⟩
  have hc : Continuous (fun eps : ℝ => (eta+2*eps)*‖e‖^2) := by fun_prop
  have hh := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := inner ℝ (A e) e)) hc.continuousWithinAt
    (fun eps heps => hbound eps heps.1)
  simpa only [mul_zero,add_zero] using hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Stationary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section MintySign
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.neg {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p A) : HasQuadraticExpansion (fun q => -f q) (-p) (-A) := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf ⊢
  convert! hf.const_mul_left (-1:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  simp only [quadraticTaylor,neg_apply,inner_neg_left]
  ring

lemma HasQuadraticExpansion.nonneg_of_localMin {f : E → ℝ} {A : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f 0 A) (hmin : IsLocalMin f 0) (e : E) :
    0 ≤ inner ℝ (A e) e := by
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhds_iff.mp hmin
  have H := hf.neg.hessian_le_of_upper_support (eta := 0) hr (by
    intro q hq
    have hq' := hh (show q∈Metric.ball (0:E) r by simpa only [Metric.mem_ball,dist_zero_right] using hq)
    simpa only [neg_zero,inner_zero_left,add_zero,zero_div,zero_mul] using neg_le_neg hq') e
  simpa only [neg_apply,inner_neg_left,zero_mul,neg_nonpos] using H
end MintySign
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section ContactDifferential
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf
omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_normalHessianOperator (x : M) (p u v : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (normalHessianOperator x p u) v=normalHessian x p u v := by
  exact InnerProductSpace.toDual_symm_apply

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactPSD
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section ContactPSD
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_1_rf75f80_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normalCost_quadraticExpansion {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    HasQuadraticExpansion (normalCost x p) (-p) (normalHessianOperator x p) := by
  rw [hasQuadraticExpansion_iff_isLittleO]
  have H := contDiffAt_second_order_remainder ((normalCost_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  rw [(normalCost_hasFDerivAt_zero hp).fderiv]
  simp only [quadraticTaylor,innerSL_apply_apply,inner_normalHessianOperator,normalHessian]
  ring

omit [MeasurableSpace M] [BorelSpace M] in
lemma normal_contact_hessian_posSemidef
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈activeLogs (n := n) v x) (hpI : p∈injectivityDomain x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    (e : TangentSpace 𝓘(ℝ,Model n) x) :
    0 ≤ inner ℝ ((normalHessianOperator x p+A) e) e := by
  have H := (normalCost_quadraticExpansion hpI).add hexp
  rw [neg_add_cancel] at H
  apply H.nonneg_of_localMin _ e
  apply Filter.Eventually.of_forall
  intro h
  have hgap := cTransform_gap_nonneg hv (riemannianExp x h) (riemannianExp x p)
  have heq := hp.2
  simp only [contactGap,normalCost,riemannianExp_zero] at heq ⊢ hgap
  linarith

end ContactPSD
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_ForwardChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner _root_.OAI.WeakMTWTransport.riemannianExp_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma metricVolume_model (n : ℕ) : metricVolume (M := Model n) n=volume := by
  let μ : Measure (Model n) := Measure.hausdorffMeasure (n:ℝ)
  have hdim : Module.finrank ℝ (Model n)=n := by simp [Model]
  have : μ.IsAddHaarMeasure := by
    dsimp only [μ]
    rw [←hdim]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  change _ • μ=volume
  exact (measure_eq_sub_vadd volume μ
    (measure_ball_pos μ (0:Model n) zero_lt_one).ne' measure_ball_lt_top.ne).symm

lemma metricVolume_lipschitz_image_le {n : ℕ} {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] {f : X → Y} {s : Set X} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^(n:ℝ)*metricVolume n s := by
  have H := hf.hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
  change euclideanVolumeFactor n*(Measure.hausdorffMeasure (n:ℝ) (f '' s))≤
    (C:ℝ≥0∞)^(n:ℝ)*(euclideanVolumeFactor n*(Measure.hausdorffMeasure (n:ℝ) s))
  calc
    _ ≤ euclideanVolumeFactor n*((C:ℝ≥0∞)^(n:ℝ)*(Measure.hausdorffMeasure (n:ℝ) s)) := mul_le_mul_right H _
    _ = _ := by ac_rfl

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_LocalCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakMTWTransport
section Area
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_jacobian_bounds_of_image_mass {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {a b : ℝ≥0∞}
    (hmass : ∀ A : Set E, MeasurableSet A → A⊆s →
      a*μ A≤μ (f '' A) ∧ μ (f '' A)≤b*μ A) :
    ∀ᵐ x ∂μ.restrict s, a≤ENNReal.ofReal |(f' x).det| ∧
      ENNReal.ofReal |(f' x).det|≤b := by
  have hJ := aemeasurable_ofReal_abs_det_fderivWithin μ hs hf'
  have harea (A : Set E) (hA : MeasurableSet A) :
      (∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ.restrict s)=μ (f '' (A∩s)) := by
    rw [Measure.restrict_restrict hA]
    exact lintegral_abs_det_fderiv_eq_addHaar_image μ (hA.inter hs)
      (fun x hx => (hf' x hx.2).mono inter_subset_right) (hi.mono inter_subset_right)
  have hlo : ∀ᵐ x ∂μ.restrict s, a≤ENNReal.ofReal |(f' x).det| := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ aemeasurable_const
    intro A hA _
    rw [harea A hA,lintegral_const,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Measure.restrict_apply hA]
    exact (hmass (A∩s) (hA.inter hs) inter_subset_right).1
  have hup : ∀ᵐ x ∂μ.restrict s, ENNReal.ofReal |(f' x).det|≤b := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hJ
    intro A hA _
    rw [harea A hA,lintegral_const,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Measure.restrict_apply hA]
    exact (hmass (A∩s) (hA.inter hs) inter_subset_right).2
  exact hlo.and hup

end Area
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold Metric
open scoped ENNReal NNReal Topology

namespace WeakMTWTransport

lemma metricVolume_lipschitz_image_le_nat {n : ℕ} {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] {f : X → Y} {s : Set X} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^n*metricVolume n s := by
  simpa only [ENNReal.rpow_natCast] using metricVolume_lipschitz_image_le (n := n) hf

lemma image_mass_in_bilipschitz_coordinates {n : ℕ} {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (d e : PartialEquiv M (Model n)) {G : Set M} {T : M → M}
    (hGs : G⊆d.source) (hTs : T '' G⊆e.source)
    {C D H K : ℝ≥0} (hC : 0<C) (hK : 0<K)
    (hd : LipschitzOnWith C d G) (hdi : LipschitzOnWith D d.symm (d '' G))
    (he : LipschitzOnWith H e (T '' G)) (hei : LipschitzOnWith K e.symm (e '' (T '' G)))
    {a b : ℝ≥0∞}
    (hmass : ∀ B : Set M, MeasurableSet B → B⊆G →
      a*metricVolume n B≤ metricVolume n (T '' B) ∧
      metricVolume n (T '' B)≤b*metricVolume n B)
    {A : Set (Model n)} (hA : MeasurableSet A) (hAs : A⊆d '' G) :
    (a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n))*volume A ≤
        volume ((e ∘ T ∘ d.symm) '' A) ∧
      volume ((e ∘ T ∘ d.symm) '' A) ≤
        ((H:ℝ≥0∞)^n*b*(D:ℝ≥0∞)^n)*volume A := by
  let B := d.symm '' A
  have hAt : A⊆d.target := by
    rintro z hz
    obtain ⟨x,hx,rfl⟩ := hAs hz
    exact d.map_source (hGs hx)
  have hBG : B⊆G := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hAs hz
    simpa only [d.left_inv (hGs hx)] using hx
  have hBm : MeasurableSet B := hA.image_of_continuousOn_injOn
    (hdi.mono hAs).continuousOn (d.symm.injOn.mono hAt)
  have hdB : d '' B=A := by
    ext z
    constructor
    · rintro ⟨x,⟨w,hw,rfl⟩,rfl⟩
      simpa only [d.right_inv (hAt hw)] using hw
    · intro hz
      exact ⟨d.symm z,⟨z,hz,rfl⟩,d.right_inv (hAt hz)⟩
  have heB : e '' (T '' B)=(e ∘ T ∘ d.symm) '' A := by
    rw [image_image,image_image]
    rfl
  have hTsB : T '' B⊆T '' G := image_mono hBG
  have H1 := metricVolume_lipschitz_image_le_nat (n := n) (hd.mono hBG)
  rw [hdB,metricVolume_model] at H1
  have H2 := metricVolume_lipschitz_image_le_nat (n := n) (hdi.mono hAs)
  rw [metricVolume_model] at H2
  have H3 := metricVolume_lipschitz_image_le_nat (n := n) (he.mono hTsB)
  rw [heB,metricVolume_model] at H3
  have H4 := metricVolume_lipschitz_image_le_nat (n := n) (hei.mono (image_mono hTsB))
  have hiB : e.symm '' (e '' (T '' B))=T '' B := by
    ext x
    constructor
    · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
      simpa only [e.left_inv (hTs (hTsB hy))] using hy
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.left_inv (hTs (hTsB hx))⟩
  rw [hiB,heB,metricVolume_model] at H4
  obtain ⟨hlo,hup⟩ := hmass B hBm hBG
  constructor
  · rw [show a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)*volume A=
        (a*volume A)/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n) by
      simp only [div_eq_mul_inv,mul_right_comm]]
    rw [ENNReal.div_le_iff' (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hC.ne'))
      (pow_ne_zero _ (by exact_mod_cast hK.ne')))
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top))]
    calc
      _ ≤ a*((C:ℝ≥0∞)^n*metricVolume n B) := mul_le_mul_right H1 _
      _ = (C:ℝ≥0∞)^n*(a*metricVolume n B) := by ac_rfl
      _ ≤ (C:ℝ≥0∞)^n*metricVolume n (T '' B) := mul_le_mul_right hlo _
      _ ≤ (C:ℝ≥0∞)^n*((K:ℝ≥0∞)^n*volume ((e ∘ T ∘ d.symm) '' A)) := mul_le_mul_right H4 _
      _ = _ := by ac_rfl
  · calc
      _ ≤ (H:ℝ≥0∞)^n*metricVolume n (T '' B) := H3
      _ ≤ (H:ℝ≥0∞)^n*(b*metricVolume n B) := mul_le_mul_right hup _
      _ ≤ (H:ℝ≥0∞)^n*(b*((D:ℝ≥0∞)^n*volume A)) :=
        mul_le_mul_right (mul_le_mul_right H2 _) _
      _ = _ := by ac_rfl

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_AePullbackLipschitzChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric
open scoped ENNReal NNReal Topology

namespace WeakMTWTransport

lemma ae_pullback_of_lipschitz_chart_inverse {n : ℕ} {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (d : PartialEquiv M (Model n)) {G : Set M} (hGm : MeasurableSet G)
    (hGs : G⊆d.source) (hIm : MeasurableSet (d '' G))
    {D : ℝ≥0} (hdi : LipschitzOnWith D d.symm (d '' G))
    {P : Model n → Prop} (hP : ∀ᵐ z ∂volume.restrict (d '' G), P z) :
    ∀ᵐ x ∂(metricVolume n).restrict G, P (d x) := by
  let N := {z | z∈d '' G ∧ ¬P z}
  have hN : volume N=0 := by
    have H := ae_iff.mp ((ae_restrict_iff' hIm).mp hP)
    apply measure_mono_null _ H
    exact fun z hz h => hz.2 (h hz.1)
  have hNsub : N⊆d '' G := fun z hz => hz.1
  have hNi : metricVolume n (d.symm '' N)=0 := by
    apply le_antisymm _ (show (0:ℝ≥0∞)≤_ from zero_le)
    have H := metricVolume_lipschitz_image_le_nat (n := n) (hdi.mono hNsub)
    rw [metricVolume_model,hN,mul_zero] at H
    exact H
  rw [ae_restrict_iff' hGm]
  apply ae_iff.mpr
  apply measure_mono_null _ hNi
  intro x hx
  have hxG : x∈G := by by_contra h; exact hx (fun hh => False.elim (h hh))
  have hn : ¬P (d x) := fun h => hx (fun _ => h)
  exact ⟨d x,⟨⟨x,hxG,rfl⟩,hn⟩,d.left_inv (hGs hxG)⟩

lemma ae_chart_jacobian_bounds {n : ℕ} {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (d e : PartialEquiv M (Model n)) {G : Set M} {T : M → M}
    (hGm : MeasurableSet G) (hIm : MeasurableSet (d '' G))
    (hGs : G⊆d.source) (hTs : T '' G⊆e.source) (hTi : InjOn T G)
    {C D H K : ℝ≥0} (hC : 0<C) (hK : 0<K)
    (hd : LipschitzOnWith C d G) (hdi : LipschitzOnWith D d.symm (d '' G))
    (he : LipschitzOnWith H e (T '' G)) (hei : LipschitzOnWith K e.symm (e '' (T '' G)))
    {a b : ℝ≥0∞}
    (hmass : ∀ B : Set M, MeasurableSet B → B⊆G →
      a*metricVolume n B≤ metricVolume n (T '' B) ∧
      metricVolume n (T '' B)≤b*metricVolume n B)
    {f' : Model n → Model n →L[ℝ] Model n}
    (hf' : ∀ z∈d '' G, HasFDerivWithinAt (e ∘ T ∘ d.symm) (f' z) (d '' G) z) :
    ∀ᵐ x ∂(metricVolume n).restrict G,
      a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)≤ENNReal.ofReal |(f' (d x)).det| ∧
      ENNReal.ofReal |(f' (d x)).det|≤(H:ℝ≥0∞)^n*b*(D:ℝ≥0∞)^n := by
  apply ae_pullback_of_lipschitz_chart_inverse d hGm hGs hIm hdi
    (P := fun z => a/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)≤ENNReal.ofReal |(f' z).det| ∧
      ENNReal.ofReal |(f' z).det|≤(H:ℝ≥0∞)^n*b*(D:ℝ≥0∞)^n)
  apply ae_jacobian_bounds_of_image_mass volume hIm hf'
  · rintro z ⟨x,hx,rfl⟩ w ⟨y,hy,rfl⟩ heq
    simp only [Function.comp_apply,d.left_inv (hGs hx),d.left_inv (hGs hy)] at heq
    have hTxs : T x∈e.source := hTs ⟨x,hx,rfl⟩
    have hTys : T y∈e.source := hTs ⟨y,hy,rfl⟩
    exact congrArg d (hTi hx hy (e.injOn hTxs hTys heq))
  · exact fun A hA hAs => image_mass_in_bilipschitz_coordinates d e hGs hTs
      hC hK hd hdi he hei hmass hA hAs

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PosSemidefApplyInner
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport

lemma posSemidef_apply_eq_zero_of_inner_eq_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} (hAs : ∀ u v, inner ℝ (A u) v=inner ℝ u (A v))
    (hA : ∀ v, 0 ≤ inner ℝ (A v) v) {v : E} (hv : inner ℝ (A v) v=0) : A v=0 := by
  have hquad (t : ℝ) :
      0 ≤ inner ℝ (A (A v)) (A v)*(t*t)+(2*inner ℝ (A v) (A v))*t+0 := by
    have H := hA (v+t • A v)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,hv] at H
    rw [hAs (A v) v] at H
    nlinarith
  have hd := discrim_le_zero hquad
  simp only [discrim,mul_zero,sub_zero] at hd
  have hs : inner ℝ (A v) (A v)=0 := by nlinarith [sq_nonneg (inner ℝ (A v) (A v))]
  exact (inner_self_eq_zero).mp hs

lemma posDef_of_posSemidef_injective {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} (hAs : ∀ u v, inner ℝ (A u) v=inner ℝ u (A v))
    (hA : ∀ v, 0 ≤ inner ℝ (A v) v) (hAi : Function.Injective A) :
    ∀ v, v≠0 → 0 < inner ℝ (A v) v := by
  intro v hv
  apply lt_of_le_of_ne (hA v)
  intro he
  have hz := posSemidef_apply_eq_zero_of_inner_eq_zero hAs hA he.symm
  exact hv (hAi (by simpa only [map_zero] using hz))

lemma injective_middle_of_det_comp_ne_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E=Module.finrank ℝ F)
    (R : E →L[ℝ] F) (S : F →L[ℝ] E) (W : F →L[ℝ] F)
    (hdet : (S.comp (W.comp R)).det≠0) : Function.Injective W := by
  have hFi : Function.Injective (S.comp (W.comp R)) := by
    apply LinearMap.ker_eq_bot.mp
    exact not_not.mp (LinearMap.det_eq_zero_iff_ker_ne_bot.not.mp hdet)
  have hRi : Function.Injective R := by
    intro u v huv
    apply hFi
    simp only [ContinuousLinearMap.comp_apply,huv]
  have hRs : Function.Surjective R :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hRi
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  obtain ⟨u,rfl⟩ := hRs v
  change W (R u)=0 at hv
  have hu : u=0 := hFi (by
    change S (W (R u))=S (W (R 0))
    simp only [hv,map_zero])
  simp only [hu,map_zero]

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MatrixNormDetFactorial
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
open Module Set
open scoped BigOperators

namespace WeakMTWTransport

lemma matrix_norm_det_le_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {R : ℝ} (hR : 0≤R) (hA : ∀ i j, ‖A i j‖≤R) :
    ‖A.det‖≤(Fintype.card ι).factorial*R^(Fintype.card ι) := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, R^(Fintype.card ι) := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_units_zsmul,norm_prod]
      calc
        _ ≤ ∏ _i : ι, |R| := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun index _ => (hA (σ index) index).trans (le_abs_self R))
        _ = _ := by simp [abs_of_nonneg hR]
    _ = _ := by simp [Fintype.card_perm]

lemma normDet_le_factorial_opNorm {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (F : U →L[ℝ] V) (hd : Module.finrank ℝ U=Module.finrank ℝ V) :
    F.toLinearMap.normDet≤(Module.finrank ℝ U).factorial*‖F‖^(Module.finrank ℝ U) := by
  classical
  let b := stdOrthonormalBasis ℝ U
  let d : OrthonormalBasis (Fin (finrank ℝ U)) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr hd).symm
  rw [LinearMap.normDet_eq_norm_det_toMatrix F.toLinearMap b d]
  have hA : ∀ i j, ‖(F.toLinearMap.toMatrix b.toBasis d.toBasis) i j‖≤‖F‖ := by
    intro i j
    rw [LinearMap.toMatrix_apply,d.coe_toBasis_repr_apply]
    change ‖d.repr (F (b j)) i‖≤‖F‖
    rw [d.repr_apply_apply]
    calc
      _ ≤ ‖d i‖*‖F (b j)‖ := norm_inner_le_norm _ _
      _ = ‖F (b j)‖ := by rw [d.orthonormal.norm_eq_one i,one_mul]
      _ ≤ ‖F‖*‖b j‖ := F.le_opNorm _
      _ = ‖F‖ := by rw [b.orthonormal.norm_eq_one,mul_one]
  simpa only [Fintype.card_fin] using matrix_norm_det_le_factorial
    (F.toLinearMap.toMatrix b.toBasis d.toBasis) (norm_nonneg F) hA

lemma normDet_comp_three {U V W Z : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (R : U →L[ℝ] V) (A : V →L[ℝ] W) (S : W →L[ℝ] Z)
    (hUV : finrank ℝ U=finrank ℝ V) (hVW : finrank ℝ V=finrank ℝ W) :
    (S.comp (A.comp R)).toLinearMap.normDet=
      S.toLinearMap.normDet*A.toLinearMap.normDet*R.toLinearMap.normDet := by
  change (S.toLinearMap ∘ₗ (A.toLinearMap ∘ₗ R.toLinearMap)).normDet=_
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ (hUV.trans hVW),
    LinearMap.normDet_comp_of_finrank_eq _ _ hUV,mul_assoc]

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ExponentialJacobian
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
section ExponentialJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteExponentialJacobian (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma expJacobian_zero (x : M) : expJacobian (n := n) x 0=1 := by
  let F : TangentSpace 𝓘(ℝ,Model n) x →ₗ[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x 0) := (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0).toLinearMap
  let e : TangentSpace 𝓘(ℝ,Model n) x →ₗᵢ[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x 0) :=
    { toLinearMap := F, norm_map' := mfderiv_exp_zero_norm x }
  exact e.normDet_eq_one

end ExponentialJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_IntrinsicJacobian
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
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section IntrinsicJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteIntrinsicJacobian
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_nonneg (a x : M) : 0 ≤ chartJacobian (n := n) a x :=
  LinearMap.normDet_nonneg _

lemma normDet_chart_exp (a x : M) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (hp : riemannianExp (n := n) x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) p).toLinearMap.normDet=
      chartJacobian (n := n) a (riemannianExp (n := n) x p)*expJacobian (n := n) x p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let E : V →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) :=
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) p
  let C : TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a) (riemannianExp (n := n) x p)
  have hd := mfderiv_comp p (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hp))
    ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) p=C.comp E at hd
  rw [hd]
  exact LinearMap.normDet_comp_of_finrank_eq E.toLinearMap C.toLinearMap rfl

lemma normDet_chart_exp_zero (a x : M)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap.normDet=
      chartJacobian (n := n) a x := by
  have h := normDet_chart_exp a x 0 (by simpa only [riemannianExp_zero] using hx)
  rw [expJacobian_zero,mul_one] at h
  simpa only [riemannianExp_zero] using h

lemma intrinsic_contact_det {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (a b : M) (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp : riemannianExp (n := n) x p∈(extChartAt 𝓘(ℝ,Model n) b).source)
    (W : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (hR : (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).comp R=
      ContinuousLinearMap.id ℝ (Model n)) :
    |((fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n := n) x) p).comp (W.comp R)).det| *
      chartJacobian (n := n) a x=
      chartJacobian (n := n) b (riemannianExp (n := n) x p)*expJacobian (n := n) x p*|W.det| := by
  have hprod : chartJacobian (n := n) a x*R.toLinearMap.normDet=1 := by
    have h := congrArg (fun F : Model n →L[ℝ] Model n => F.toLinearMap.normDet) hR
    rw [show (ContinuousLinearMap.id ℝ (Model n)).toLinearMap=LinearMap.id by rfl,
      LinearMap.normDet_id] at h
    change ((fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap ∘ₗ
      R.toLinearMap).normDet=1 at h
    erw [LinearMap.normDet_comp_of_finrank_eq R.toLinearMap
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap rfl] at h
    rw [normDet_chart_exp_zero a x hx] at h
    exact h
  rw [←LinearMap.normDet_eq_abs_det]
  rw [normDet_comp_three R W _ rfl rfl,normDet_chart_exp b x p hp,
    LinearMap.normDet_eq_abs_det]
  calc
    _ = (chartJacobian (n := n) b (riemannianExp (n := n) x p)*expJacobian (n := n) x p*|W.det|)*
      (chartJacobian (n := n) a x*R.toLinearMap.normDet) := by ring
    _ = _ := by rw [hprod,mul_one]

end IntrinsicJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_LocalCEMS2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section LocalCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_2
lemma local_contact_cems_full {v : M → ℝ} (hv : Continuous v)
    {G : Set M} (hGm : MeasurableSet G)
    (hGD : ∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    (hGi : InjOn (contactSelection hv) G)
    (hReg : ∀ x∈G, ∃ p A, NormalAlexandrovContact (n := n) v x p A)
    (a b : M) (hGs : G⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hTs : contactSelection hv '' G⊆(extChartAt 𝓘(ℝ,Model n) b).source)
    {C D H K : ℝ≥0} (hC : 0<C) (hK : 0<K)
    (hd : LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) G)
    (hdi : LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
      ((extChartAt 𝓘(ℝ,Model n) a) '' G))
    (he : LipschitzOnWith H (extChartAt 𝓘(ℝ,Model n) b) (contactSelection hv '' G))
    (hei : LipschitzOnWith K (extChartAt 𝓘(ℝ,Model n) b).symm
      ((extChartAt 𝓘(ℝ,Model n) b) '' (contactSelection hv '' G)))
    {l u : ℝ≥0∞} (hl : 0<l)
    (hmass : ∀ B : Set M, MeasurableSet B → B⊆G →
      l*metricVolume n B≤ metricVolume n (contactSelection hv '' B) ∧
      metricVolume n (contactSelection hv '' B)≤u*metricVolume n B) :
    ∀ᵐ x ∂(metricVolume n).restrict G, ∃ p A,
      NormalAlexandrovContact (n := n) v x p A ∧
      (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
      ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
        l/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n)≤
          ENNReal.ofReal |(S.comp ((normalHessianOperator x p+A).comp R)).det| ∧
        ENNReal.ofReal |(S.comp ((normalHessianOperator x p+A).comp R)).det|≤
          (H:ℝ≥0∞)^n*u*(D:ℝ≥0∞)^n ∧
        |(S.comp ((normalHessianOperator x p+A).comp R)).det| *chartJacobian (n := n) a x=
          chartJacobian (n := n) b (contactSelection hv x)*expJacobian (n := n) x p*
            |(normalHessianOperator x p+A).det| := by
  classical
  let d := extChartAt 𝓘(ℝ,Model n) a
  let e := extChartAt 𝓘(ℝ,Model n) b
  let T := contactSelection hv
  have hIm : MeasurableSet (d '' G) := hGm.image_of_continuousOn_injOn hd.continuousOn
    (d.injOn.mono hGs)
  have hEx (z : Model n) (hz : z∈d '' G) :
      ∃ F : Model n →L[ℝ] Model n,
        HasFDerivWithinAt (e ∘ T ∘ d.symm) F (d '' G) z ∧
        ∃ x∈G, d x=z ∧ ∃ p A, NormalAlexandrovContact (n := n) v x p A ∧
          ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
          ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
            F=S.comp ((normalHessianOperator x p+A).comp R) ∧
            S=fderiv ℝ (e ∘ riemannianExp (n := n) x) p ∧
            (fderiv ℝ (d ∘ riemannianExp (n := n) x) 0).comp R=
              ContinuousLinearMap.id ℝ (Model n) := by
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨p,A,hp⟩ := hReg x hx
    obtain ⟨R,S,hF,hS,hR⟩ := contact_selection_chart_differential_full hv (contactSelection_mem hv)
      hGD hx hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 a b hGs (hTs ⟨x,hx,rfl⟩)
    exact ⟨_,hF,x,hx,rfl,p,A,hp,R,S,rfl,hS,hR⟩
  let F : Model n → Model n →L[ℝ] Model n := fun z =>
    if hz : z∈d '' G then (hEx z hz).choose else 0
  have hF (z : Model n) (hz : z∈d '' G) :
      HasFDerivWithinAt (e ∘ T ∘ d.symm) (F z) (d '' G) z := by
    simpa only [F,dite_eq_left hz] using (hEx z hz).choose_spec.1
  have hJac := ae_chart_jacobian_bounds d e hGm hIm hGs hTs hGi
    hC hK hd hdi he hei hmass hF
  filter_upwards [hJac,ae_restrict_mem hGm] with x hx hxG
  have hxI : d x∈d '' G := ⟨x,hxG,rfl⟩
  have hFspec := (hEx (d x) hxI).choose_spec.2
  obtain ⟨y,hy,hyx,p,A,hp,R,S,hEq,hS,hR⟩ := hFspec
  have hyx' : y=x := d.injOn (hGs hy) (hGs hxG) hyx
  subst y
  have hEq' : F (d x)=S.comp ((normalHessianOperator x p+A).comp R) := by
    simpa only [F,dite_eq_left hxI] using hEq
  rw [hEq'] at hx
  refine ⟨p,A,hp,?_,R,S,hx.1,hx.2,?_⟩
  · apply posDef_of_posSemidef_injective
    · intro w z
      simp only [add_apply,inner_add_left,inner_add_right,
        inner_normalHessianOperator,hp.2.2.1]
      rw [← real_inner_comm w (normalHessianOperator x p z),inner_normalHessianOperator,
        normalHessian_symm hp.2.1 w z]
    · exact normal_contact_hessian_posSemidef hv hp.1 hp.2.1 hp.2.2.2
    · apply injective_middle_of_det_comp_ne_zero (by rfl) R S
      intro hh
      have hpos : 0<l/((C:ℝ≥0∞)^n*(K:ℝ≥0∞)^n) := ENNReal.div_pos hl.ne'
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
          (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      rw [hh,abs_zero,ENNReal.ofReal_zero] at hx
      exact (not_le_of_gt hpos) hx.1
  · have hTx : T x=riemannianExp x p := contact_unique_of_mdifferentiable hv (hGD x hxG)
      (contactSelection_mem hv x) hp.1.2
    change contactSelection hv x=riemannianExp x p at hTx
    rw [hS,hTx]
    exact intrinsic_contact_det a b (hGs hxG) (hTx ▸ hTs ⟨x,hxG,rfl⟩)
      (normalHessianOperator x p+A) R hR

end LocalCEMS
end WeakMTWTransport

end

end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Charts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric Bundle
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section Charts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_bilipschitz_chart (a : M) :
    ∃ C D : ℝ≥0, ∃ r>0, ball a r⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) (ball a r) ∧
      LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
        (extChartAt 𝓘(ℝ,Model n) a '' ball a r) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,r,hr,hs,hC⟩ := exists_lipschitzOn_chart (n := n) a
  obtain ⟨D,s,hspos,_,hD⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  obtain ⟨t,ht,htsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (ball_mem_nhds a hr) ((continuousAt_extChartAt (I := 𝓘(ℝ,Model n)) a).preimage_mem_nhds
      (ball_mem_nhds _ hspos)))
  refine ⟨C,D,t,ht,fun x hx => hs (htsub hx).1,hC.mono (fun x hx => (htsub hx).1),?_⟩
  apply hD.mono
  rintro z ⟨x,hx,rfl⟩
  exact (htsub hx).2

end Charts
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ChartJacobianBounds
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
section ChartJacobianBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteChartJacobianBounds (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance inverseChartNormedAddCommGroup_rf75f80_1 (y : Model n) (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance inverseChartNormedSpace_rf75f80_1 (y : Model n) (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedSpace
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_inverse_product (a : M) {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    chartJacobian (n := n) a ((extChartAt 𝓘(ℝ,Model n) a).symm z)*
      inverseChartJacobian (n := n) a z=1 := by
  let d := extChartAt 𝓘(ℝ,Model n) a
  let F : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (d.symm z) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm z
  let G : TangentSpace 𝓘(ℝ,Model n) (d.symm z) →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d (d.symm z)
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
  simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  change G.comp F=ContinuousLinearMap.id ℝ (Model n) at h
  have hn := congrArg (fun L : Model n →L[ℝ] Model n => L.toLinearMap.normDet) h
  change (G.toLinearMap ∘ₗ F.toLinearMap).normDet=(LinearMap.id : Model n →ₗ[ℝ] Model n).normDet at hn
  rw [LinearMap.normDet_comp_of_finrank_eq F.toLinearMap G.toLinearMap rfl,LinearMap.normDet_id] at hn
  exact hn

omit [CompactSpace M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma eventually_chartJacobian_bounds (a : M) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ᶠ x in 𝓝 a,
      l ≤ chartJacobian (n := n) a x ∧ chartJacobian (n := n) a x≤u := by
  let d := extChartAt 𝓘(ℝ,Model n) a
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hC,hCd⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,Model n) a
  obtain ⟨D,hD,hDi⟩ := eventually_norm_mfderivWithin_symm_extChartAt_comp_lt 𝓘(ℝ,Model n) a
  let N := Module.finrank ℝ (Model n)
  let U : ℝ := N.factorial * C ^ N
  let Q : ℝ := N.factorial * D ^ N
  have hU : 0<U := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hC _)
  have hQ : 0<Q := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hD _)
  refine ⟨Q⁻¹,U,inv_pos.mpr hQ,hU,?_⟩
  filter_upwards [hCd,hDi,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a] with x hxC hxD hxs
  let F : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d x
  let G : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (d.symm (d x)) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm (d x)
  have hF : ‖F‖≤C := hxC.le
  have hG : ‖G‖≤D := by
    simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hxD
    exact hxD.le
  have hFU : F.toLinearMap.normDet≤U :=
    (normDet_le_factorial_opNorm F rfl).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hF _) (Nat.cast_nonneg _))
  have hGQ : G.toLinearMap.normDet≤Q :=
    (normDet_le_factorial_opNorm G rfl).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hG _) (Nat.cast_nonneg _))
  have hp := chartJacobian_inverse_product a (d.map_source hxs)
  rw [d.left_inv hxs] at hp
  refine ⟨?_,hFU⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hQ).mpr
  calc
    1=chartJacobian (n := n) a x*G.toLinearMap.normDet := hp.symm
    _ ≤ chartJacobian (n := n) a x*Q := mul_le_mul_of_nonneg_left hGQ (chartJacobian_nonneg a x)

end ChartJacobianBounds
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UniformCharts
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
open Set Filter Manifold Bundle Module Metric
open scoped Topology ContDiff BigOperators NNReal

namespace WeakMTWTransport
section UniformCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_uniform_volume_charts :
    ∃ C : ℝ≥0, 0<C ∧ ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ x : M,
      ∃ a : M, ∃ U : Set M, IsOpen U ∧ x∈U ∧
        U⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) U ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a).symm
          ((extChartAt 𝓘(ℝ,Model n) a) '' U) ∧
        ∀ z∈U, l ≤ chartJacobian (n := n) a z ∧ chartJacobian (n := n) a z≤u := by
  classical
  have H (x : M) : ∃ C D : ℝ≥0, ∃ l u : ℝ, 0<l ∧ 0<u ∧
      ∃ U : Set M, IsOpen U ∧ x∈U ∧ U⊆(extChartAt 𝓘(ℝ,Model n) x).source ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) x) U ∧
        LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) x).symm
          ((extChartAt 𝓘(ℝ,Model n) x) '' U) ∧
        ∀ z∈U, l ≤ chartJacobian (n := n) x z ∧ chartJacobian (n := n) x z≤u := by
    obtain ⟨C,D,r,hr,hUs,hd,hdi⟩ := exists_bilipschitz_chart (n := n) x
    let U := ball x r
    have hUo : IsOpen U := isOpen_ball
    have hxU : x∈U := mem_ball_self hr
    obtain ⟨l,u,hl,hu,hnear⟩ := eventually_chartJacobian_bounds (n := n) x
    obtain ⟨V,hVs,hVo,hxV⟩ := _root_.mem_nhds_iff.mp hnear
    exact ⟨C,D,l,u,hl,hu,U∩V,hUo.inter hVo,⟨hxU,hxV⟩,
      inter_subset_left.trans hUs,hd.mono inter_subset_left,
      hdi.mono (image_mono inter_subset_left),fun z hz => hVs hz.2⟩
  choose C D l u hl hu U hUo hxU hUs hd hdi hj using H
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hUo
    (show univ⊆⋃ x, U x from fun x _ => mem_iUnion.mpr ⟨x,hxU x⟩)
  let C0 : ℝ≥0 := 1+∑ a∈s, (C a+D a)
  let R : ℝ := 1+∑ a∈s, (l a)⁻¹
  let u0 : ℝ := 1+∑ a∈s, u a
  have hC0 : 0<C0 := by dsimp [C0] <;> positivity
  have hR : 0<R := by
    have := Finset.sum_nonneg (fun a (_ : a∈s) => (inv_pos.mpr (hl a)).le)
    dsimp [R]
    linarith
  have hu0 : 0<u0 := by
    have := Finset.sum_nonneg (fun a (_ : a∈s) => (hu a).le)
    dsimp [u0]
    linarith
  refine ⟨C0,hC0,R⁻¹,u0,inv_pos.mpr hR,hu0,?_⟩
  intro x
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hCD : C a+D a≤C0 := by
    have h := Finset.single_le_sum (f := fun a => C a+D a) (fun _ _ => zero_le) ha
    exact h.trans (le_add_of_nonneg_left (by positivity))
  have hCa : C a≤C0 := (le_add_of_nonneg_right (zero_le)).trans hCD
  have hDa : D a≤C0 := (le_add_of_nonneg_left (zero_le)).trans hCD
  have hla : (l a)⁻¹≤R := by
    have h := Finset.single_le_sum (fun b (_ : b∈s) => (inv_pos.mpr (hl b)).le) ha
    dsimp [R]
    linarith
  have hlower : R⁻¹≤l a := by
    have h := (inv_le_inv₀ hR (inv_pos.mpr (hl a))).mpr hla
    simpa only [inv_inv] using h
  have hua : u a≤u0 := by
    have h := Finset.single_le_sum (fun b (_ : b∈s) => (hu b).le) ha
    dsimp [u0]
    linarith
  exact ⟨a,U a,hUo a,hxa,hUs a,(hd a).weaken hCa,(hdi a).weaken hDa,
    fun z hz => ⟨hlower.trans (hj a z hz).1,((hj a z hz).2).trans hua⟩⟩

end UniformCharts
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport

lemma scalar_intrinsic_jacobian_bounds {d j D a b ell u c C : ℝ}
    (hd : 0≤d) (hjD : 0≤j*D) (hell : 0≤ell) (hc : 0 < c) (hC : 0<C)
    (ha : c≤a ∧ a≤C) (hb : c≤b ∧ b≤C) (hl : ell≤d) (hu : d≤u)
    (heq : d*a=b*j*D) : ell*c/C≤j*D ∧ j*D≤u*C/c := by
  have ha0 : 0≤a := hc.le.trans ha.1
  have hu0 : 0≤u := hd.trans hu
  have hlow : ell*c≤d*a := by
    calc
      ell*c ≤ ell*a := mul_le_mul_of_nonneg_left ha.1 hell
      _ ≤ d*a := mul_le_mul_of_nonneg_right hl ha0
  have hhigh : d*a≤u*C := mul_le_mul hu ha.2 ha0 hu0
  constructor
  · apply (div_le_iff₀ hC).mpr
    calc
      ell*c ≤ d*a := hlow
      _ = b*(j*D) := by nlinarith [heq]
      _ ≤ C*(j*D) := mul_le_mul_of_nonneg_right hb.2 hjD
      _ = j*D*C := by ring
  · apply (le_div_iff₀ hc).mpr
    calc
      j*D*c = c*(j*D) := by ring
      _ ≤ b*(j*D) := mul_le_mul_of_nonneg_right hb.1 hjD
      _ = d*a := by nlinarith [heq]
      _ ≤ u*C := hhigh

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_IntrinsicCEMS
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
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section IntrinsicCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_3
lemma exists_uniform_intrinsic_contact_bounds_oai {ell upper : ℝ} (hell : 0<ell)
    (hupper : 0<upper) :
    ∃ chi eta : ℝ, 0 < chi ∧ 0<eta ∧ ∀ (v : M → ℝ) (hv : Continuous v)
      (G : Set M), MeasurableSet G → (∀ᵐ x ∂metricVolume n, x∈G) →
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) →
      InjOn (contactSelection hv) G →
      (∀ x∈G, ∃ p A, NormalAlexandrovContact (n := n) v x p A) →
      (∀ B : Set M, MeasurableSet B → B⊆G →
        ENNReal.ofReal ell*metricVolume n B≤ metricVolume n (contactSelection hv '' B) ∧
        metricVolume n (contactSelection hv '' B)≤ENNReal.ofReal upper*metricVolume n B) →
      ∀ᵐ x ∂metricVolume n, ∃ p A,
        NormalAlexandrovContact (n := n) v x p A ∧
        (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
        chi≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
        expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤eta := by
  obtain ⟨C,hC,c,d,hc,hd,hcharts⟩ := exists_uniform_volume_charts (n := n) (M := M)
  let ell0 : ℝ := ell/((C:ℝ)^n*(C:ℝ)^n)
  let upper0 : ℝ := (C:ℝ)^n*upper*(C:ℝ)^n
  have hCr : 0<(C:ℝ) := hC
  have hell0 : 0<ell0 := by dsimp [ell0] <;> positivity
  have hupper0 : 0<upper0 := by dsimp [upper0] <;> positivity
  refine ⟨ell0*c/d,upper0*d/c,div_pos (mul_pos hell0 hc) hd,
    div_pos (mul_pos hupper0 hd) hc,?_⟩
  intro v hv G hGm hGae hGD hGi hReg hmass
  suffices H : ∀ᵐ x ∂metricVolume n, x∈G → ∃ p A,
      NormalAlexandrovContact (n := n) v x p A ∧
      (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
      ell0*c/d≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
      expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤upper0*d/c by
    filter_upwards [H,hGae] with x hx hxG
    exact hx hxG
  apply ae_of_locally_ae
  intro x hx
  let T := contactSelection hv
  obtain ⟨a,U,hUo,hxU,hUs,hda,hdai,hja⟩ := hcharts x
  obtain ⟨b,V,hVo,hTxV,hVs,hdb,hdbi,hjb⟩ := hcharts (T x)
  have hnear : T ⁻¹' V∈𝓝 x :=
    (contactSelection_continuousAt_of_mdifferentiable hv (hGD x hx)).preimage_mem_nhds
      (hVo.mem_nhds hTxV)
  obtain ⟨W,hWs,hWo,hxW⟩ := _root_.mem_nhds_iff.mp hnear
  let B := G∩(U∩W)
  have hBG : B⊆G := inter_subset_left
  have hBU : B⊆U := fun _ hz => hz.2.1
  have hTBV : T '' B⊆V := by
    rintro _ ⟨z,hz,rfl⟩
    exact hWs hz.2.2
  have hBm : MeasurableSet B := hGm.inter (hUo.inter hWo).measurableSet
  have hloc := local_contact_cems_full hv hBm (fun z hz => hGD z (hBG hz))
    (hGi.mono hBG) (fun z hz => hReg z (hBG hz)) a b
    (hBU.trans hUs) (hTBV.trans hVs) hC hC (hda.mono hBU)
    (hdai.mono (image_mono hBU)) (hdb.mono hTBV) (hdbi.mono (image_mono hTBV))
    (ENNReal.ofReal_pos.mpr hell) (fun A hAm hAB => hmass A hAm (hAB.trans hBG))
  have hloc' := (ae_restrict_iff' hBm).mp hloc
  refine ⟨U∩W,hUo.inter hWo,⟨hxU,hxW⟩,?_⟩
  filter_upwards [hloc',hGae] with z hz hzG hzUW
  obtain ⟨p,A,hp,hpd,R,S,hl,hu,heq⟩ := hz ⟨hzG,hzUW⟩
  have hlr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  have hur := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)) hu
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.coe_toReal,ENNReal.toReal_ofReal hell.le,ENNReal.toReal_ofReal hupper.le,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hlr hur
  have hbounds := scalar_intrinsic_jacobian_bounds (abs_nonneg _)
    (mul_nonneg (expJacobian_nonneg z p) (abs_nonneg _)) hell0.le hc hd
    (hja z hzUW.1) (hjb (T z) (hWs hzUW.2)) hlr hur heq
  exact ⟨p,A,hp,hpd,hbounds⟩

end IntrinsicCEMS
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds_oai.{u_1} := @OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds_oai.{u_1}
