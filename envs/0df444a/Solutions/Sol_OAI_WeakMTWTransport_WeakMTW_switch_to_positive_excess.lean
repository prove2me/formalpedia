-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:56.78046+00:00
-- url     : https://prove2.me/submissions/cb438903-00ea-49e0-b122-ce8683f226bb

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
import Definitions.Def_OAIQ232A018
import Definitions.Def_OAIQ232A030

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
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

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

lemma dualPair_contact_left {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) : ∃ y, contactGap u v x y = 0 := by
  rw [huv.1]
  exact cTransform_gap_zero hv x

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

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_CurveAdvance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma curve_deriv_eq_active_pairing {v : M → ℝ} (hv : Continuous v)
    {γ : ℝ → M} {t d : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    (hd : HasDerivAt (fun s => cTransform v (γ s)) d t)
    {p : TangentSpace 𝓘(ℝ,Model n) (γ t)} (hp : p∈activeLogs v (γ t)) :
    d=inner ℝ p (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1) := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun s : ℝ => cTransform v (γ s)+2*cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))
  have hmin : IsLocalMin f t := by
    apply Filter.Eventually.of_forall
    intro s
    have H := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (γ s)
    dsimp [f]
    linarith
  have hc : HasDerivAt
      (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p)))
      (inner ℝ (-((1/2:ℝ) • p)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1)) t := by
    let D : ℝ →L[ℝ] ℝ := (innerSL ℝ (-((1/2:ℝ) • p))).comp
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) t D :=
      (cost_start_gradient_of_injectivityDomain hID).comp t hγ.hasMFDerivAt
    have hfd : HasFDerivAt
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) D t :=
      hcomp.hasFDerivAt
    exact hfd.hasDerivAt
  have H := hmin.hasDerivAt_eq_zero (hd.add (hc.const_mul (2:ℝ)))
  simp only [inner_neg_left,real_inner_smul_left] at H
  linarith only [H]

lemma curve_neg_cost_deriv_eq_pairing {γ : ℝ → M} {t d : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    {p : TangentSpace 𝓘(ℝ,Model n) (γ t)} (hp : p∈minimizingVectors (γ t))
    (hd : HasDerivAt (fun s => -cost (γ s) (riemannianExp (γ t) p)) d t) :
    d=inner ℝ p (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1) := by
  have hID := contracted_minimizer_mem_injectivityDomain hp
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun s : ℝ => -cost (γ s) (riemannianExp (γ t) p)+
    2*cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))
  have hmin : IsLocalMin f t := by
    apply Filter.Eventually.of_forall
    intro s
    have H := minimizing_split_upper_support hp
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (γ s)
    have H0 := minimizing_split_contact hp
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
    dsimp [f]
    linarith only [H,H0]
  have hc : HasDerivAt
      (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p)))
      (inner ℝ (-((1/2:ℝ) • p)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1)) t := by
    let D : ℝ →L[ℝ] ℝ := (innerSL ℝ (-((1/2:ℝ) • p))).comp
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) t D :=
      (cost_start_gradient_of_injectivityDomain hID).comp t hγ.hasMFDerivAt
    have hfd : HasFDerivAt
        (fun s : ℝ => cost (γ s) (riemannianExp (γ t) ((1/2:ℝ) • p))) D t :=
      hcomp.hasFDerivAt
    exact hfd.hasDerivAt
  have H := hmin.hasDerivAt_eq_zero (hd.add (hc.const_mul (2:ℝ)))
  simp only [inner_neg_left,real_inner_smul_left] at H
  linarith only [H]

lemma spray_neg_cost_deriv_le {z : TangentBundle 𝓘(ℝ,Model n) M} {t d : ℝ} {y : M}
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t) :
    d ≤ dist (sprayFlow t z).1 y*‖z.2‖ := by
  obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) (sprayFlow t z).1 y
  have hproj := hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt t)
  have H := curve_neg_cost_deriv_eq_pairing hproj.mdifferentiableAt hp (by simpa only [he] using hd)
  have hvel : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) (fun s => (sprayFlow s z).1) t (1:ℝ)=
      (sprayFlow t z).2 := spray_velocity_eq_mfderiv ((sprayFlow_curve z).isMIntegralCurveAt t)
  have H' : d=inner ℝ p (sprayFlow t z).2 :=
    H.trans (congrArg (fun q => inner ℝ p q) hvel)
  rw [H']
  have hn : dist (sprayFlow t z).1 y=‖p‖ := by
    change dist (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p)=‖p‖ at hp
    rwa [he] at hp
  rw [hn]
  exact (real_inner_le_norm _ _).trans_eq (by rw [sprayFlow_speed])

lemma curve_deriv_le_active_norm {v : M → ℝ} (hv : Continuous v)
    {γ : ℝ → M} {t d : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t)
    (hd : HasDerivAt (fun s => cTransform v (γ s)) d t)
    {p : TangentSpace 𝓘(ℝ,Model n) (γ t)} (hp : p∈activeLogs v (γ t)) :
    d ≤ ‖p‖*‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ t 1‖ := by
  rw [curve_deriv_eq_active_pairing hv hγ hd hp]
  exact real_inner_le_norm _ _

lemma spray_deriv_le_active_norm {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} {t d : ℝ}
    (hd : HasDerivAt (fun s => cTransform v (sprayFlow s z).1) d t)
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs v (sprayFlow t z).1) : d ≤ ‖p‖*‖z.2‖ := by
  have hproj := hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt t)
  have H := curve_deriv_le_active_norm hv hproj.mdifferentiableAt hd hp
  have hvel : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) (fun s => (sprayFlow s z).1) t (1:ℝ)=
      (sprayFlow t z).2 := spray_velocity_eq_mfderiv ((sprayFlow_curve z).isMIntegralCurveAt t)
  exact H.trans_eq (congrArg (fun q => ‖p‖*‖q‖) hvel |>.trans (by rw [sprayFlow_speed]))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LipschitzSubAeDeriv
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
open Set Filter MeasureTheory
open scoped Topology Interval NNReal

lemma lipschitzOn_sub_le_of_ae_deriv_le {f : ℝ → ℝ} {a b c : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b))
    (hd : ∀ᵐ x : ℝ, x∈Icc a b → deriv f x ≤ c) :
    f b-f a ≤ c*(b-a) := by
  have ha : AbsolutelyContinuousOnInterval f a b :=
    (by rwa [uIcc_of_le hab] : LipschitzOnWith K f (uIcc a b)).absolutelyContinuousOnInterval
  have H := intervalIntegral.integral_mono_ae_restrict hab ha.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume a b)
    ((ae_restrict_iff' measurableSet_Icc).mpr hd)
  rw [ha.integral_deriv_eq_sub,intervalIntegral.integral_const] at H
  simpa only [smul_eq_mul,mul_comm] using H

lemma lipschitzOn_barrier {f : ℝ → ℝ} {a b c : ℝ} {K : ℝ≥0}
    (_ : a ≤ b) (hf : LipschitzOnWith K f (Icc a b)) (hfa : f a ≤ c)
    (hd : ∀ᵐ x : ℝ, x∈Icc a b → c < f x → deriv f x ≤ 0) :
    ∀ x∈Icc a b, f x ≤ c := by
  intro x hx
  by_contra Hx
  have hcx : c < f x := lt_of_not_ge Hx
  let S : Set ℝ := {r∈Icc a x | f r ≤ c}
  have hxs : Icc a x⊆Icc a b := Icc_subset_Icc_right hx.2
  have hS : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.isClosed_le (hf.continuousOn.mono hxs) continuousOn_const)
      (fun _ h => h.1)
  have haS : a∈S := ⟨⟨le_rfl,hx.1⟩,hfa⟩
  obtain ⟨r,hr,hgreat⟩ := hS.exists_isGreatest ⟨a,haS⟩
  have hrx : r < x := lt_of_le_of_ne hr.1.2 (by intro H; subst r; exact (not_le_of_gt hcx) hr.2)
  have hfr : ∀ u∈Icc r x, u≠r → c < f u := by
    intro u hu hur
    by_contra H
    have huS : u∈S := ⟨⟨hr.1.1.trans hu.1,hu.2⟩,le_of_not_gt H⟩
    exact hur (le_antisymm (hgreat huS) hu.1)
  have hsub : Icc r x⊆Icc a b := Icc_subset_Icc hr.1.1 hx.2
  have hd' : ∀ᵐ u : ℝ, u∈Icc r x → deriv f u ≤ 0 := by
    have hneq : ∀ᵐ u : ℝ, u≠r := by rw [ae_iff]; simp
    filter_upwards [hd,hneq] with u hu hur hus
    exact hu (hsub hus) (hfr u hus hur)
  have H := lipschitzOn_sub_le_of_ae_deriv_le hrx.le (hf.mono hsub) hd'
  simp only [zero_mul] at H
  linarith only [H,hr.2,hcx]

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

lemma norm_deficit_advance {q N t D : ℝ} (hq : 0 ≤ q) (hN : 0 ≤ N)
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hgap : q^2 ≤ (1-t)^2*N^2-D) : q*N-(1-t)*N^2 ≤ -D/2 := by
  have ha : 0 ≤ (1-t)*N := mul_nonneg (by linarith only [ht1]) hN
  have hqA : q ≤ (1-t)*N := (sq_le_sq₀ hq ha).mp (by nlinarith only [hgap,hD])
  have hdiff : 0 ≤ (1-t)*N-q := sub_nonneg.mpr hqA
  have hsum : (1-t)*N+q ≤ 2*N := by nlinarith [mul_nonneg ht hN]
  have H := mul_nonneg hdiff (sub_nonneg.mpr hsum)
  nlinarith only [H,hgap]

lemma norm_surplus_advance {q N t D : ℝ} (hq : 0 ≤ q) (hN : 0 ≤ N)
    (_ : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hgap : q^2 ≤ (1-t)^2*N^2+D) : q*N-(1-t)*N^2 ≤ 2*D := by
  by_cases Hq : q ≤ (1-t)*N
  · have H := mul_le_mul_of_nonneg_right Hq hN
    nlinarith only [H,hD]
  · have hdiff : 0 ≤ q-(1-t)*N := (le_of_not_ge Hq).trans (le_refl _)|> sub_nonneg.mpr
    have hsum : N/2 ≤ (1-t)*N+q := by nlinarith only [ht1,hN,hq,mul_nonneg (sub_nonneg.mpr ht1) hN]
    have H := mul_nonneg hdiff (sub_nonneg.mpr hsum)
    nlinarith only [H,hgap]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_RayAdvance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma lipschitz_spray_projection (z : TangentBundle 𝓘(ℝ,Model n) M) :
    LipschitzWith ‖z.2‖₊ (fun t => (sprayFlow t z).1) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simpa only [Real.dist_eq,mul_comm,coe_nnnorm] using dist_sprayFlow_le z s t

lemma cTransform_ray_lipschitz [Nonempty M] {v : M → ℝ} (hv : Continuous v)
    (z : TangentBundle 𝓘(ℝ,Model n) M) :
    ∃ L, LipschitzWith L (fun t => cTransform v (sprayFlow t z).1) := by
  let C : ℝ≥0 := ⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  have hC : ∀ x y : M,dist x y ≤ C := fun x y =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  exact ⟨C*‖z.2‖₊,(cTransform_lipschitz hv hC).comp (lipschitz_spray_projection z)⟩

lemma active_norm_deficit_deriv {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} {t d D : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hd : HasDerivAt (fun s => cTransform v (sprayFlow s z).1) d t)
    (hgap : ∀ p∈activeLogs (n := n) v (sprayFlow t z).1,
      ‖p‖^2 ≤ (1-t)^2*‖z.2‖^2-D) :
    d-(1-t)*‖z.2‖^2 ≤ -D/2 := by
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (sprayFlow t z).1
  have H := spray_deriv_le_active_norm hv hd hp
  have Hg := norm_deficit_advance (norm_nonneg p) (norm_nonneg z.2) ht ht1 hD (hgap p hp)
  linarith only [H,Hg]

lemma cost_norm_surplus_deriv {z : TangentBundle 𝓘(ℝ,Model n) M} {t d D : ℝ} {y : M}
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t)
    (hgap : dist (sprayFlow t z).1 y^2 ≤ (1-t)^2*‖z.2‖^2+D) :
    d-(1-t)*‖z.2‖^2 ≤ 2*D := by
  have H := spray_neg_cost_deriv_le hd
  have Hg := norm_surplus_advance dist_nonneg (norm_nonneg z.2) ht ht1 hD hgap
  linarith only [H,Hg]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_MiddleExclusion
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma neg_cost_ray_lipschitz (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M) :
    ∃ K, LipschitzWith K (fun t => -cost (sprayFlow t z).1 y) := by
  let C : ℝ≥0 := ⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  have hC : ∀ x y : M,dist x y≤C := fun x y =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have H : LipschitzWith C (fun x : M => cost x y) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x x'
    simpa only [Real.dist_eq] using cost_lipschitz_of_distance_bound hC x x' y
  exact ⟨C*‖z.2‖₊,(H.comp (lipschitz_spray_projection z)).neg⟩

omit [Nonempty M] in
lemma rayMountainDifference_lipschitzOn (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M)
    (a vy b B0 By T : ℝ) :
    ∃ K, LipschitzOnWith K (rayMountainDifference z y a vy b B0 By) (Icc 0 T) := by
  obtain ⟨K,hK⟩ := neg_cost_ray_lipschitz z y
  have hc : ContDiff ℝ 1 (fun t : ℝ => (1-t)^2*‖z.2‖^2/2) := by fun_prop
  obtain ⟨L,hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  refine ⟨K+L,?_⟩
  have H := (hK.lipschitzOnWith.add hL).add (LipschitzWith.const (a-vy-b*(By-B0))).lipschitzOnWith
  simp only [add_zero] at H
  exact H

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma rayMountainDifference_hasDerivAt {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    (a vy b B0 By : ℝ) {t d : ℝ}
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t) :
    HasDerivAt (rayMountainDifference z y a vy b B0 By) (d-(1-t)*‖z.2‖^2) t := by
  have hc0 := ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).mul_const (‖z.2‖^2)).div_const 2
  have hc : HasDerivAt (fun s : ℝ => (1-s)^2*‖z.2‖^2/2) (-(1-t)*‖z.2‖^2) t := by
    convert hc0 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    ring
  have H := (hd.add hc).add_const (a-vy-b*(By-B0))
  have he' : d+(-(1-t)*‖z.2‖^2)=d-(1-t)*‖z.2‖^2 := by ring
  rw [he'] at H
  exact H

omit [Nonempty M] in
lemma middle_mountain_barrier {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    {a vy b B0 By D T : ℝ} (hb : 0≤b) (hD : 0<D) (hT : 0≤T) (hT1 : T≤1/2)
    (hs : D/16≤vy-a) (hB : B0+1≤By)
    (hstart : rayMountainDifference z y a vy b B0 By 0≤-b/2) :
    ∀ t∈Icc 0 T, rayMountainDifference z y a vy b B0 By t≤-b/2 := by
  obtain ⟨K,hK⟩ := rayMountainDifference_lipschitzOn z y a vy b B0 By T
  apply lipschitzOn_barrier hT hK hstart
  obtain ⟨C,hC⟩ := neg_cost_ray_lipschitz z y
  have hae : ∀ᵐ t : ℝ, DifferentiableAt ℝ (fun s => -cost (sprayFlow s z).1 y) t :=
    hC.ae_differentiableAt
  filter_upwards [hae] with t ht htI hval
  have hd := ht.hasDerivAt
  have H := spray_neg_cost_deriv_le hd
  have hmul : b≤b*(By-B0) := by nlinarith only [mul_nonneg hb (sub_nonneg.mpr hB)]
  have hgap : dist (sprayFlow t z).1 y^2≤(1-t)^2*‖z.2‖^2-D/8 := by
    dsimp only [rayMountainDifference,cost] at hval
    linarith only [hval,hs,hmul,hb]
  have Hn := norm_deficit_advance dist_nonneg (norm_nonneg z.2) htI.1 (htI.2.trans hT1)
    (show 0≤D/8 by positivity) hgap
  rw [(rayMountainDifference_hasDerivAt a vy b B0 By hd).deriv]
  linarith only [H,Hn,hD]

end

open Set MeasureTheory
open scoped Topology Interval ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ConvexNormSq
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma exists_convex_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {p q : E} {N : ℝ} (hp : p∈S) (hq : q∈S)
    (hpN : ‖p‖^2≤N) (hqN : N≤‖q‖^2) :
    ∃ w∈convexHull ℝ S, ‖w‖^2=N := by
  let f : ℝ → E := fun t => (1-t) • p+t • q
  have hc : Continuous (fun t => ‖f t‖^2) := by dsimp [f]; fun_prop
  have h0 : ‖f 0‖^2≤N := by simpa [f] using hpN
  have h1 : N≤‖f 1‖^2 := by simpa [f] using hqN
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc.continuousOn ⟨h0,h1⟩
  refine ⟨f t,?_,he⟩
  exact (convex_convexHull ℝ S) (subset_convexHull ℝ S hp) (subset_convexHull ℝ S hq)
    (by linarith only [ht.2]) ht.1 (by ring)

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

omit [Nonempty M] in
lemma isCompact_gapSection {u v : M → ℝ} (hv : Continuous v) (x : M) (r : ℝ) :
    IsCompact (gapSection u v x r) := by
  apply IsClosed.isCompact
  exact isClosed_le ((continuous_const.add (continuous_cost_right x)).add hv) continuous_const

lemma gapSection_nonempty {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    (gapSection u v x r).Nonempty := by
  obtain ⟨y, hy⟩ := dualPair_contact_left hv huv x
  exact ⟨y, by simpa only [gapSection, mem_ofPred_eq, hy] using hr⟩

lemma sectionOscillation_extrema {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y0 ∈ gapSection u v x r, ∃ y1 ∈ gapSection u v x r,
      (∀ y ∈ gapSection u v x r, v y0 ≤ v y) ∧
      (∀ y ∈ gapSection u v x r, v y ≤ v y1) ∧
      sectionOscillation u v x r = v y1 - v y0 := by
  have hc := isCompact_gapSection (u := u) hv x r
  have hn := gapSection_nonempty hv huv x hr
  obtain ⟨y0, hy0, hmin⟩ := hc.exists_isMinOn hn hv.continuousOn
  obtain ⟨y1, hy1, hmax⟩ := hc.exists_isMaxOn hn hv.continuousOn
  have hleast : IsLeast (v '' gapSection u v x r) (v y0) := by
    refine ⟨mem_image_of_mem v hy0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have hgreatest : IsGreatest (v '' gapSection u v x r) (v y1) := by
    refine ⟨mem_image_of_mem v hy1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨y0, hy0, y1, hy1, fun _ hy => hmin hy, fun _ hy => hmax hy,
    by rw [sectionOscillation, hleast.csInf_eq, hgreatest.csSup_eq]⟩

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LiftedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma cost_minimizingVector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : cost x (riemannianExp x p)=‖p‖^2/2 := by
  unfold cost
  rw [show dist x (riemannianExp x p)=‖p‖ from hp]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ModifiedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
section ModifiedData
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma modified_transform_bounds {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b H : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s ∧ B s ≤ H) (x : M) :
    u x-b*H ≤ cTransform (modifiedDatum v a D b B) x ∧
      cTransform (modifiedDatum v a D b B) x ≤ u x := by
  have hw := continuous_modifiedDatum hv a D b hB
  have hshift : Continuous (fun y => v y+b*H) := by
    rw [hdual.2]
    exact (continuous_cTransform hu).add continuous_const
  have h1 := cTransform_antitone (w := fun y => v y+b*H) hw hshift
    (fun y => add_le_add_right (mul_le_mul_of_nonneg_left (hbound _).2 hb) (v y)) x
  have h2 := cTransform_antitone hv hw
    (fun y => le_add_of_nonneg_right (mul_nonneg hb (hbound _).1)) x
  rw [cTransform_add_const hv,hdual.1.symm] at h1
  rw [hdual.1.symm] at h2
  exact ⟨h1,h2⟩

lemma modified_contact_original_section {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b H : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s ∧ B s ≤ H) {x y : M}
    (hc : contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B) x y=0) :
    contactGap u v x y ≤ b*H := by
  have Hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual hB hb hbound x).1
  have Ho := mul_nonneg hb (hbound ((v y-a)/D)).1
  dsimp only [contactGap,modifiedDatum] at hc ⊢
  linarith only [Hg,Ho,hc]

omit [CompactSpace M] [Nonempty M] in
lemma modified_excess_at_contact {v : M → ℝ} {a D b : ℝ} {Bc Bo : ℝ → ℝ} {x y : M}
    (hc : contactGap (cTransform (modifiedDatum v a D b Bo))
      (cTransform (cTransform (modifiedDatum v a D b Bo))) x y=0) :
    modifiedExcess v a D b Bc Bo y =
      v y+b*Bc ((v y-a)/D)+cost x y+cTransform (modifiedDatum v a D b Bo) x := by
  dsimp only [contactGap] at hc
  dsimp only [modifiedExcess,modifiedDatum]
  linarith only [hc]

end ModifiedData
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_RayAnchor
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma minimizing_ray_tail_cost {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hp : z.2∈minimizingVectors z.1) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    cost (sprayFlow t z).1 (riemannianExp z.1 z.2)=(1-t)^2*‖z.2‖^2/2 := by
  have hm : dist z.1 (sprayFlow 1 z).1=1*‖z.2‖ := by
    simpa only [one_mul,riemannianExp_eq_sprayFlow] using (show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hp)
  have H := sprayFlow_minimizing_subinterval z ht ht1 hm
  rw [cost,riemannianExp_eq_sprayFlow]
  change dist (sprayFlow t z).1 (sprayFlow 1 z).1^2/2=_
  rw [H,mul_pow]

lemma transformRayDifference_lipschitzOn {v : M → ℝ} (hv : Continuous v)
    (z : TangentBundle 𝓘(ℝ,Model n) M) (a T : ℝ) :
    ∃ K, LipschitzOnWith K (transformRayDifference v z a) (Icc 0 T) := by
  obtain ⟨K,hK⟩ := cTransform_ray_lipschitz hv z
  have hc : ContDiff ℝ 1 (fun t : ℝ => (1-t)^2*‖z.2‖^2/2) := by fun_prop
  obtain ⟨L,hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  refine ⟨K+L,?_⟩
  have H := (hK.lipschitzOnWith.add hL).add (LipschitzWith.const a).lipschitzOnWith
  simp only [add_zero] at H
  exact H

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma transformRayDifference_hasDerivAt {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} (a : ℝ) {t d : ℝ}
    (hd : HasDerivAt (fun s=>cTransform v (sprayFlow s z).1) d t) :
    HasDerivAt (transformRayDifference v z a) (d-(1-t)*‖z.2‖^2) t := by
  have hc0 := ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).mul_const (‖z.2‖^2)).div_const 2
  have hc : HasDerivAt (fun s : ℝ => (1-s)^2*‖z.2‖^2/2) (-(1-t)*‖z.2‖^2) t := by
    convert hc0 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    first | rfl | ring
  have H := (hd.add hc).add_const a
  have he' : d+(-(1-t)*‖z.2‖^2)=d-(1-t)*‖z.2‖^2 := by ring
  rw [he'] at H
  exact H

lemma modified_ray_difference_lower {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hp : z.2∈minimizingVectors z.1)
    {a D b : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    -b*B 0≤transformRayDifference (modifiedDatum v a D b B) z a t := by
  have H := cTransform_gap_nonneg (continuous_modifiedDatum hv a D b hB)
    (sprayFlow t z).1 (riemannianExp z.1 z.2)
  rw [contactGap,modifiedDatum,ha,sub_self,zero_div,minimizing_ray_tail_cost hp ht ht1] at H
  dsimp only [transformRayDifference]
  linarith only [H]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma modified_active_norm_identity {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} {a D b t : ℝ} {B : ℝ → ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1) :
    ‖p‖^2=(1-t)^2*‖z.2‖^2-2*(v (riemannianExp (sprayFlow t z).1 p)-a)
      -2*b*B ((v (riemannianExp (sprayFlow t z).1 p)-a)/D)
      -2*transformRayDifference (modifiedDatum v a D b B) z a t := by
  have hc := hp.2
  have hd : dist (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p)=‖p‖ := hp.1
  dsimp only [contactGap,modifiedDatum,cost] at hc
  rw [hd] at hc
  dsimp only [transformRayDifference]
  linarith only [hc]

lemma modified_right_active_deficit {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {a D b t eta : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) (hb : 0≤b) (hD : 0<D)
    (hbsmall : b≤D/16) (heta : eta≤1/8) (hB0 : B 0≤2)
    (hBn : ∀ s,0≤B s) (ht : 0≤t) (ht1 : t≤1)
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1)
    (hs : 1-eta≤(v (riemannianExp (sprayFlow t z).1 p)-a)/D) :
    ‖p‖^2≤(1-t)^2*‖z.2‖^2-D := by
  have H := modified_active_norm_identity hp
  have HL := modified_ray_difference_lower (D := D) (b := b) hv hz hB ha ht ht1
  have HS := (le_div_iff₀ hD).mp hs
  have HB := mul_nonneg hb (hBn ((v (riemannianExp (sprayFlow t z).1 p)-a)/D))
  have HB0 := mul_le_mul_of_nonneg_left hB0 hb
  have HB1 := mul_le_mul_of_nonneg_left heta hD.le
  nlinarith only [H,HL,HS,HB,HB0,HB1,hbsmall,hD]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_RayBenchmark
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section RayBenchmark
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma ray_benchmark {v : M → ℝ} (hv : Continuous v) {x : M}
    {p q : TangentSpace 𝓘(ℝ,Model n) x} {a D r C d t : ℝ}
    (hp : p∈minimizingVectors x) (hq : q∈minimizingVectors x)
    (ha : v (riemannianExp x p)=a)
    (hgap : contactGap (cTransform v) v x (riemannianExp x q) ≤ r)
    (hangle : ‖p‖^2-inner ℝ p q≤6*D) (ht : 0≤t) (hsmall : ‖t • p‖<d)
    (hTaylor : ∀ p' w : TangentSpace 𝓘(ℝ,Model n) x,
      p'∈minimizingVectors x → ‖w‖<d →
      cost (riemannianExp x w) (riemannianExp x p')≤
        cost x (riemannianExp x p')-inner ℝ p' w+C*‖w‖^2) :
    -cost (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 (riemannianExp x q)-
      v (riemannianExp x q)≥
      -‖p‖^2/2-a-r+(‖p‖^2-6*D)*t-C*‖p‖^2*t^2 := by
  have HT := hTaylor q (t • p) hq hsmall
  have H0 := cTransform_gap_nonneg hv x (riemannianExp x p)
  rw [contactGap,cost_minimizingVector hp,ha] at H0
  dsimp only [contactGap] at hgap
  rw [←riemannianExp_smul x p t]
  rw [inner_smul_right,real_inner_comm p q,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at HT
  have Hangle := mul_le_mul_of_nonneg_right hangle ht
  nlinarith only [HT,H0,hgap,Hangle]

lemma ray_original_section_anchors {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {y1 : M} {a D b r H t C : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0≤b) (hbound : ∀ s,0≤B s ∧ B s≤H)
    (ha : v (riemannianExp z.1 z.2)=a) (ht : 0≤t) (ht1 : t≤1)
    (hanchor : transformRayDifference (modifiedDatum v a D b B) z a t ≤ r)
    (hbench : -cost (sprayFlow t z).1 y1-v y1≥
      -‖z.2‖^2/2-a-r+(‖z.2‖^2-6*D)*t-C*t^2) :
    contactGap u v (sprayFlow t z).1 (riemannianExp z.1 z.2)≤b*H+r ∧
    contactGap u v (sprayFlow t z).1 y1≤b*H+2*r+6*D*t+C*t^2 := by
  have Hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual hB hb hbound (sprayFlow t z).1).1
  dsimp only [transformRayDifference] at hanchor
  constructor
  · rw [contactGap,minimizing_ray_tail_cost hz ht ht1,ha]
    linarith only [Hg,hanchor]
  · dsimp only [contactGap]
    nlinarith only [Hg,hanchor,hbench,mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)]

lemma section_absolute_level_bounds {u v : M → ℝ} (hv : Continuous v)
    (hdual : IsCostDualPair u v) {x y0 y1 y : M} {r a D δ : ℝ}
    (hr : 0 ≤ r) (hD : 0<D) (hy0 : y0∈gapSection u v x r)
    (hy1 : y1∈gapSection u v x r) (hy : y∈gapSection u v x r)
    (ha : v y0=a) (ha1 : v y1=a+D)
    (hosc : sectionOscillation u v x r≤(1+δ)*D) :
    -δ≤(v y-a)/D ∧ (v y-a)/D≤1+δ := by
  obtain ⟨ym,hym,yp,hyp,hmin,hmax,he⟩ := sectionOscillation_extrema hv hdual x hr
  have h0 := hmin y0 hy0
  have h1 := hmax y1 hy1
  have hl := hmin y hy
  have hu := hmax y hy
  rw [ha] at h0
  rw [ha1] at h1
  rw [he] at hosc
  constructor
  · apply (le_div_iff₀ hD).mpr
    nlinarith only [h0,h1,hl,hosc]
  · apply (div_le_iff₀ hD).mpr
    nlinarith only [h0,h1,hu,hosc]

end RayBenchmark
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_LowerSwitch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma rayBenchmarkGap_lipschitzOn (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M)
    (a vy b By D r C T : ℝ) :
    ∃ K, LipschitzOnWith K (fun t => rayBenchmarkGap z y a vy b By D r C t-10*D*t)
      (Icc 0 T) := by
  obtain ⟨K,hK⟩ := neg_cost_ray_lipschitz z y
  have hc : ContDiff ℝ 1 (fun t : ℝ =>
      -vy-b*By+‖z.2‖^2/2+a+r-(‖z.2‖^2-6*D)*t+C*t^2-10*D*t) := by fun_prop
  obtain ⟨L,hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  refine ⟨K+L,?_⟩
  have he : (fun t => rayBenchmarkGap z y a vy b By D r C t-10*D*t) =
      (fun t => -cost (sprayFlow t z).1 y +
        (-vy-b*By+‖z.2‖^2/2+a+r-(‖z.2‖^2-6*D)*t+C*t^2-10*D*t)) := by
    funext t
    dsimp only [rayBenchmarkGap]
    ring
  rw [he]
  exact hK.lipschitzOnWith.add hL

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma rayBenchmarkGap_hasDerivAt {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    (a vy b By D r C : ℝ) {t d : ℝ}
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t) :
    HasDerivAt (fun s => rayBenchmarkGap z y a vy b By D r C s-10*D*s)
      (d-‖z.2‖^2-4*D+2*C*t) t := by
  have H0 := ((((hd.sub_const vy).sub_const (b*By)).add_const (‖z.2‖^2/2)).add_const a).add_const r
  have H := ((H0.sub ((hasDerivAt_id t).const_mul (‖z.2‖^2-6*D))).add
      (((hasDerivAt_id t).pow 2).const_mul C)).sub ((hasDerivAt_id t).const_mul (10*D))
  convert H using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [id_eq] <;> first | rfl | ring)

omit [Nonempty M] in
lemma benchmark_lower_switch_time {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    {a vy b By D r C η T : ℝ} (hb : 0≤b) (hD : 0<D) (hT : 0≤T)
    (hT1 : T≤1/2) (hC : 0≤C) (hBy : 0≤By) (hlevel : -2*η*D≤vy-a)
    (hsmall : 4*η*D+2*r+12*D*T+2*C*T^2+b≤D)
    (hsmall' : 2*C*T≤2*D)
    (hstart : rayBenchmarkGap z y a vy b By D r C 0≤-b/2)
    (hfinish : 0 ≤ rayBenchmarkGap z y a vy b By D r C T) :
    b/(20*D)≤T := by
  obtain ⟨K,hK⟩ := rayBenchmarkGap_lipschitzOn z y a vy b By D r C T
  have hstart' : rayBenchmarkGap z y a vy b By D r C 0-10*D*0≤-b/2 := by simpa using hstart
  have H := lipschitzOn_barrier hT hK hstart'
  have hd : ∀ᵐ t : ℝ, t∈Icc 0 T → -b/2 < rayBenchmarkGap z y a vy b By D r C t-10*D*t →
      deriv (fun s => rayBenchmarkGap z y a vy b By D r C s-10*D*s) t≤0 := by
    obtain ⟨L,hL⟩ := neg_cost_ray_lipschitz z y
    filter_upwards [hL.ae_differentiableAt] with t ht htI hval
    have hDt : 0≤10*D*t := mul_nonneg (by positivity) htI.1
    have hval' : -b/2 ≤ rayBenchmarkGap z y a vy b By D r C t := by linarith only [hval,hDt]
    have htime : 12*D*t≤12*D*T := mul_le_mul_of_nonneg_left htI.2 (by positivity)
    have hsquare : t^2≤T^2 := pow_le_pow_left₀ htI.1 htI.2 2
    have hquad : 2*C*t^2≤2*C*T^2 := mul_le_mul_of_nonneg_left hsquare (by positivity)
    have hcost : dist (sprayFlow t z).1 y^2≤(1-t)^2*‖z.2‖^2+D := by
      dsimp only [rayBenchmarkGap,cost] at hval'
      have hbB := mul_nonneg hb hBy
      have htP := mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)
      nlinarith only [hval',hlevel,hsmall,htime,hquad,hbB,htP]
    have Hn := cost_norm_surplus_deriv htI.1 (htI.2.trans hT1) hD.le ht.hasDerivAt hcost
    have hlin : 2*C*t≤2*C*T := mul_le_mul_of_nonneg_left htI.2 (by positivity)
    rw [(rayBenchmarkGap_hasDerivAt a vy b By D r C ht.hasDerivAt).deriv]
    have htP := mul_nonneg htI.1 (sq_nonneg ‖z.2‖)
    nlinarith only [Hn,hlin,hsmall',htP]
  have HT := H hd T ⟨hT,le_rfl⟩
  apply (div_le_iff₀ (by positivity : 0<20*D)).mpr
  nlinarith only [HT,hfinish]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_RestrictedTransform
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
open scoped Topology NNReal

namespace WeakMTWTransport
section RestrictedTransform
variable {M : Type*} [MetricSpace M] [CompactSpace M]

omit [CompactSpace M] in
lemma exists_restrictedTransform_contact {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) (x : M) :
    ∃ y∈S, restrictedTransform v S x = -cost x y-v y ∧
      ∀ z∈S, -cost x z-v z ≤ restrictedTransform v S x := by
  obtain ⟨y,hy,H⟩ := hS.exists_isMaxOn hSn
    (((continuous_cost_right x).neg.sub hv).continuousOn)
  have hg : IsGreatest ((fun y => -cost x y-v y) '' S) (-cost x y-v y) := by
    refine ⟨mem_image_of_mem _ hy,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact H hz
  refine ⟨y,hy,hg.csSup_eq,?_⟩
  intro z hz
  rw [restrictedTransform,hg.csSup_eq]
  exact H hz

omit [CompactSpace M] in
lemma restrictedTransform_lipschitz {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) {D : ℝ≥0}
    (hD : ∀ x y : M,dist x y≤D) : LipschitzWith D (restrictedTransform v S) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x x'
  obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hv hS hSn x
  obtain ⟨y',hy',he',H'⟩ := exists_restrictedTransform_contact hv hS hSn x'
  have A := H y' hy'
  have B := H' y hy
  have C := (abs_le.mp (cost_lipschitz_of_distance_bound hD x x' y)).1
  have C' := (abs_le.mp (cost_lipschitz_of_distance_bound hD x x' y')).2
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith only [he,he',A,B,C,C']

lemma continuous_restrictedTransform {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) :
    Continuous (restrictedTransform v S) := by
  let D : ℝ≥0 := ⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  exact (restrictedTransform_lipschitz hv hS hSn (D := D)
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded
      (mem_univ x) (mem_univ y))).continuous

variable [Nonempty M]

lemma restrictedTransform_le {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) (x : M) :
    restrictedTransform v S x ≤ cTransform v x := by
  obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hv hS hSn x
  rw [he]
  have Hc := cTransform_gap_nonneg hv x y
  dsimp only [contactGap] at Hc
  linarith only [Hc]

lemma restrictedTransform_eq_of_contact {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) {x y : M}
    (hy : y∈S) (hc : contactGap (cTransform v) v x y=0) :
    restrictedTransform v S x=cTransform v x := by
  obtain ⟨z,hz,he,H⟩ := exists_restrictedTransform_contact hv hS hSn x
  have H' := H y hy
  have Hc := restrictedTransform_le hv hS hSn x
  dsimp only [contactGap] at hc
  linarith only [H',Hc,hc]

lemma cTransform_eq_max_restricted {v : M → ℝ} (hv : Continuous v)
    {S R : Set M} (hS : IsCompact S) (hSn : S.Nonempty)
    (hR : IsCompact R) (hRn : R.Nonempty) {x : M}
    (hcover : ∀ y, contactGap (cTransform v) v x y=0 → y∈S ∪ R) :
    cTransform v x=max (restrictedTransform v S x) (restrictedTransform v R x) := by
  have hle := max_le (restrictedTransform_le hv hS hSn x)
    (restrictedTransform_le hv hR hRn x)
  obtain ⟨y,hy,_⟩ := exists_cTransform_contact hv x
  have hc : contactGap (cTransform v) v x y=0 := by
    dsimp [contactGap]; linarith only [hy]
  rcases hcover y hc with h|h
  · rw [restrictedTransform_eq_of_contact hv hS hSn h hc]
    exact (max_eq_left (restrictedTransform_le hv hR hRn x)).symm
  · rw [restrictedTransform_eq_of_contact hv hR hRn h hc]
    exact (max_eq_right (restrictedTransform_le hv hS hSn x)).symm

end RestrictedTransform
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_ScalarFirstSwitch
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace WeakMTWTransport

lemma scalar_first_switch {f h : ℝ → ℝ} {K : ℝ≥0} {b D r : ℝ}
    (hb : 0<b) (hD : 0<D) (hr : r≤b) (hh : Continuous h) (h0 : 0<h 0)
    (hf : LipschitzOnWith K f (Icc 0 (8*b/D)))
    (hf0 : f 0 ≤ r) (hfT : -2*b≤f (8*b/D))
    (hdrop : ∀ᵐ t : ℝ, t∈Icc 0 (8*b/D) → 0<h t → deriv f t≤-D/2) :
    ∃ τ∈Ioc 0 (8*b/D), h τ=0 ∧ ∀ t∈Ico 0 τ, 0<h t := by
  let T := 8*b/D
  have hT : 0<T := by dsimp [T] <;> positivity
  have hex : ∃ τ∈Icc 0 T, h τ=0 := by
    by_contra H
    have hpos : ∀ t∈Icc 0 T, 0<h t := by
      intro t ht
      by_contra ht'
      have hi := intermediate_value_Icc' ht.1 hh.continuousOn
        (show (0:ℝ)∈Icc (h t) (h 0) from ⟨le_of_not_gt ht',h0.le⟩)
      obtain ⟨s,hs,hse⟩ := hi
      exact H ⟨s,⟨hs.1,hs.2.trans ht.2⟩,hse⟩
    have Hdrop : ∀ᵐ t : ℝ, t∈Icc 0 T → deriv f t≤-D/2 := by
      filter_upwards [hdrop] with t ht hmem
      exact ht hmem (hpos t hmem)
    have Hdec := lipschitzOn_sub_le_of_ae_deriv_le hT.le hf Hdrop
    have he : (-D/2)*(T-0)=-4*b := by dsimp [T]; field_simp <;> ring
    rw [he] at Hdec
    linarith only [Hdec,hf0,hfT,hr,hb]
  let Z : Set ℝ := {t∈Icc 0 T | h t=0}
  have hZ : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_eq hh continuous_const)) (fun _ ht=>ht.1)
  have hZn : Z.Nonempty := by obtain ⟨t,ht,he⟩:=hex; exact ⟨t,ht,he⟩
  obtain ⟨τ,hτ,hτmin⟩ := hZ.exists_isLeast hZn
  have hτ0 : 0<τ := lt_of_le_of_ne hτ.1.1 (by intro H; subst τ; linarith only [h0,hτ.2])
  refine ⟨τ,⟨hτ0,hτ.1.2⟩,hτ.2,?_⟩
  intro t ht
  by_contra ht'
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc' ht.1 hh.continuousOn
    (show (0:ℝ)∈Icc (h t) (h 0) from ⟨le_of_not_gt ht',h0.le⟩)
  have hsZ : s∈Z := ⟨⟨hs.1,hs.2.trans (ht.2.le.trans hτ.1.2)⟩,hse⟩
  exact (not_le_of_gt (hs.2.trans_lt ht.2)) (hτmin hsZ)

end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
section FirstSwitch
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma modified_middle_not_contact {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {a D b r eta t : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) (hb : 0<b) (hD : 0<D)
    (hr : r≤b/4) (ht : 0≤t) (ht1 : t≤1/2)
    (hgap : contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2) ≤ r)
    (hbar : ∀ s∈Icc (1/16) (1-eta),B 0+1≤B s) {y : M}
    (hy : (v y-a)/D∈Icc (1/16) (1-eta)) :
    contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B)
      (sprayFlow t z).1 y≠0 := by
  have Hcost : cost z.1 (riemannianExp z.1 z.2)=‖z.2‖^2/2 := by
    rw [cost,show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hz]
  have hg := cTransform_gap_nonneg hv z.1 y
  rw [contactGap,Hcost,ha] at hgap
  have hBdiff : b≤b*(B ((v y-a)/D)-B 0) := by
    have H := mul_le_mul_of_nonneg_left (hbar _ hy) hb.le
    nlinarith only [H]
  have hs : D/16≤v y-a := by
    have H := (le_div_iff₀ hD).mp hy.1
    linarith only [H]
  have hstart : rayMountainDifference z y a (v y) b (B 0) (B ((v y-a)/D)) 0≤-b/2 := by
    dsimp only [rayMountainDifference]
    rw [sprayFlow_zero]
    norm_num only [sub_zero,one_pow,one_mul]
    dsimp only [contactGap] at hg
    linarith only [hg,hgap,hBdiff,hr,hb]
  have H := middle_mountain_barrier hb.le hD ht ht1 hs (hbar _ hy) hstart t ⟨ht,le_rfl⟩
  intro hc
  have HL := modified_ray_difference_lower (D := D) (b := b) hv hz hB ha ht (by linarith only [ht1])
  dsimp only [rayMountainDifference] at H
  dsimp only [transformRayDifference] at HL
  dsimp only [contactGap,modifiedDatum] at hc
  linarith only [H,HL,hc,hb]

lemma actual_first_switch {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {y1 : M} {a D b r eta : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) (ha1 : v y1=a+D)
    (hb : 0<b) (hD : 0<D) (hr : r≤b/4) (hbD : b≤D/16) (heta0 : 0≤eta) (heta : eta≤1/8)
    (hBn : ∀ s,0≤B s) (hB0 : B 0≤2) (hB1 : B 1=0)
    (hBl : ∀ s≤1/16,1≤B s)
    (hbar : ∀ s∈Icc (1/16) (1-eta),B 0+1≤B s)
    (hgap0 : contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2) ≤ r)
    (hgap1 : contactGap (cTransform v) v z.1 y1 ≤ r) :
    ∃ τ∈Ioc 0 (8*b/D), ∃ ym yp : M,
      (v ym-a)/D<1/16 ∧ 1-eta≤(v yp-a)/D ∧
      contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B)
        (sprayFlow τ z).1 ym=0 ∧
      contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B)
        (sprayFlow τ z).1 yp=0 ∧
      ∀ t∈Icc 0 τ, -b*B 0≤transformRayDifference (modifiedDatum v a D b B) z a t ∧
        transformRayDifference (modifiedDatum v a D b B) z a t ≤ r := by
  let w := modifiedDatum v a D b B
  have hw : Continuous w := continuous_modifiedDatum hv a D b hB
  let S : Set M := {y | (v y-a)/D≤1/16}
  let R : Set M := {y | 1-eta≤(v y-a)/D}
  have hS : IsCompact S := (isClosed_le ((hv.sub continuous_const).div_const D) continuous_const).isCompact
  have hR : IsCompact R := (isClosed_le continuous_const ((hv.sub continuous_const).div_const D)).isCompact
  have hSn : S.Nonempty := ⟨riemannianExp z.1 z.2,by dsimp [S]; rw [ha]; norm_num⟩
  have hRn : R.Nonempty := ⟨y1,by dsimp [R]; simp only [ha1,add_sub_cancel_left,div_self hD.ne']; linarith only [heta0]⟩
  let L : ℝ → ℝ := fun t => restrictedTransform w S (sprayFlow t z).1
  let U : ℝ → ℝ := fun t => restrictedTransform w R (sprayFlow t z).1
  have hL : Continuous L := (continuous_restrictedTransform hw hS hSn).comp
    (lipschitz_spray_projection z).continuous
  have hU : Continuous U := (continuous_restrictedTransform hw hR hRn).comp
    (lipschitz_spray_projection z).continuous
  let T := 8*b/D
  have hT : 0<T := by dsimp [T] <;> positivity
  have hT1 : T≤1/2 := by dsimp [T]; apply (div_le_iff₀ hD).mpr; linarith only [hbD]
  have hcover : ∀ t∈Icc 0 T,∀ y,contactGap (cTransform w) w (sprayFlow t z).1 y=0 → y∈S∪R := by
    intro t ht y hc
    by_contra H
    have hs : 1/16<(v y-a)/D := lt_of_not_ge (fun h=>H (Or.inl h))
    have hr' : (v y-a)/D<1-eta := lt_of_not_ge (fun h=>H (Or.inr h))
    exact modified_middle_not_contact hv hz hB ha hb hD hr ht.1 (ht.2.trans hT1)
      hgap0 hbar ⟨hs.le,hr'.le⟩ hc
  have heq : ∀ t∈Icc 0 T,cTransform w (sprayFlow t z).1=max (L t) (U t) := by
    intro t ht
    exact cTransform_eq_max_restricted hw hS hSn hR hRn (hcover t ht)
  have hL0 : L 0 ≤ cTransform v z.1-b := by
    obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hw hS hSn z.1
    have Hg := cTransform_gap_nonneg hv z.1 y
    have HB := mul_le_mul_of_nonneg_left (hBl ((v y-a)/D) hy) hb.le
    dsimp only [L]
    rw [sprayFlow_zero,he]
    dsimp only [w,modifiedDatum,contactGap] at *
    linarith only [Hg,HB]
  have hU0 : cTransform v z.1-r≤U 0 := by
    obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hw hR hRn z.1
    have hy1 : y1∈R := by dsimp [R]; simp only [ha1,add_sub_cancel_left,div_self hD.ne']; linarith only [heta0]
    have H1 := H y1 hy1
    have he1 : (v y1-a)/D=1 := by simp only [ha1,add_sub_cancel_left,div_self hD.ne']
    dsimp only [w,modifiedDatum] at H1
    rw [he1,hB1,mul_zero,add_zero] at H1
    dsimp only [U]
    rw [sprayFlow_zero]
    dsimp only [contactGap] at hgap1
    linarith only [H1,hgap1]
  have h0 : 0<U 0-L 0 := by linarith only [hL0,hU0,hr,hb]
  let f := transformRayDifference w z a
  obtain ⟨K,hK⟩ := transformRayDifference_lipschitzOn hw z a T
  have hf0 : f 0 ≤ r := by
    have HG := cTransform_antitone hv hw (fun y=>by
      dsimp only [w,modifiedDatum]; exact le_add_of_nonneg_right (mul_nonneg hb.le (hBn _))) z.1
    have Hcost : cost z.1 (riemannianExp z.1 z.2)=‖z.2‖^2/2 := by rw [cost,show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hz]
    rw [contactGap,Hcost,ha] at hgap0
    dsimp only [f,transformRayDifference]
    rw [sprayFlow_zero]
    norm_num only [sub_zero,one_pow,one_mul]
    linarith only [HG,hgap0]
  have hfT : -2*b≤f T := by
    have H := modified_ray_difference_lower (D := D) (b := b) hv hz hB ha hT.le (by linarith only [hT1])
    have HB := mul_le_mul_of_nonneg_left hB0 hb.le
    linarith only [H,HB]
  have hdrop : ∀ᵐ t : ℝ,t∈Icc 0 T → 0<U t-L t → deriv f t≤-D/2 := by
    obtain ⟨C,hC⟩ := cTransform_ray_lipschitz hw z
    filter_upwards [hC.ae_differentiableAt] with t ht htI hpos
    have Hnorm : ∀ p∈activeLogs (n := n) w (sprayFlow t z).1,
        ‖p‖^2≤(1-t)^2*‖z.2‖^2-D := by
      intro p hp
      have hs : 1-eta≤(v (riemannianExp (sprayFlow t z).1 p)-a)/D := by
        rcases hcover t htI _ hp.2 with h|h
        · have HL := restrictedTransform_eq_of_contact hw hS hSn h hp.2
          have HU := restrictedTransform_le hw hR hRn (sprayFlow t z).1
          change L t=cTransform w (sprayFlow t z).1 at HL
          change U t ≤ cTransform w (sprayFlow t z).1 at HU
          linarith only [hpos,HL,HU]
        · exact h
      exact modified_right_active_deficit hv hz hB ha hb.le hD hbD heta hB0 hBn
        htI.1 (by linarith only [htI.2,hT1]) hp hs
    have H := active_norm_deficit_deriv hw htI.1 (htI.2.trans hT1) hD.le ht.hasDerivAt Hnorm
    rw [(transformRayDifference_hasDerivAt a ht.hasDerivAt).deriv]
    exact H
  obtain ⟨τ,hτ,hτe,hpre⟩ := scalar_first_switch hb hD (by linarith only [hr,hb])
    (hU.sub hL) h0 hK hf0 hfT hdrop
  have hτI : τ∈Icc 0 T := ⟨hτ.1.le,hτ.2⟩
  change U τ-L τ=0 at hτe
  have Hτ : U τ=L τ := by linarith only [hτe]
  have Hmax := heq τ hτI
  rw [Hτ,max_self] at Hmax
  obtain ⟨ym,hym,hem,_⟩ := exists_restrictedTransform_contact hw hS hSn (sprayFlow τ z).1
  obtain ⟨yp,hyp,hep,_⟩ := exists_restrictedTransform_contact hw hR hRn (sprayFlow τ z).1
  have hcm : contactGap (cTransform w) w (sprayFlow τ z).1 ym=0 := by
    dsimp only [contactGap]
    change L τ= -cost (sprayFlow τ z).1 ym-w ym at hem
    linarith only [Hmax,hem]
  have hcp : contactGap (cTransform w) w (sprayFlow τ z).1 yp=0 := by
    dsimp only [contactGap]
    change U τ= -cost (sprayFlow τ z).1 yp-w yp at hep
    linarith only [Hmax,Hτ,hep]
  refine ⟨τ,hτ,ym,yp,?_,hyp,hcm,hcp,?_⟩
  · apply lt_of_le_of_ne hym
    intro He
    have hm : (v ym-a)/D∈Icc (1/16) (1-eta) := by rw [He]; constructor <;> linarith only [heta]
    exact modified_middle_not_contact hv hz hB ha hb hD hr hτI.1 (hτI.2.trans hT1)
      hgap0 hbar hm hcm
  · intro t ht
    refine ⟨modified_ray_difference_lower hv hz hB ha ht.1
      (by linarith only [ht.2,hτI.2,hT1]),?_⟩
    have hsmall : Icc 0 t⊆Icc 0 T := Icc_subset_Icc_right (ht.2.trans hτI.2)
    have hne : ∀ᵐ s : ℝ,s≠τ := by rw [ae_iff]; simp
    have hd : ∀ᵐ s : ℝ,s∈Icc 0 t → deriv f s≤-D/2 := by
      filter_upwards [hdrop,hne] with s hs hne hsI
      exact hs (hsmall hsI) (hpre s ⟨hsI.1,lt_of_le_of_ne (hsI.2.trans ht.2) hne⟩)
    have H := lipschitzOn_sub_le_of_ae_deriv_le ht.1 (hK.mono hsmall) hd
    have Hn : (-D/2)*(t-0)≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith only [hD])
      (by linarith only [ht.1])
    change f t ≤ r
    linarith only [H,Hn,hf0]

end FirstSwitch
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SwitchNorms
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section SwitchNorms
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_switch_norm_identity {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} {a D b t : ℝ} {B : ℝ → ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1) :
    ‖p‖^2=(1-t)^2*‖z.2‖^2-2*(v (riemannianExp (sprayFlow t z).1 p)-a)-
      2*b*B ((v (riemannianExp (sprayFlow t z).1 p)-a)/D)-
      2*transformRayDifference (modifiedDatum v a D b B) z a t := by
  have hc := hp.2
  rw [contactGap,cost_minimizingVector hp.1] at hc
  dsimp only [modifiedDatum] at hc
  dsimp only [transformRayDifference]
  linarith only [hc]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_switch_norm_brackets {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} {a D b r H t : ℝ} {B : ℝ → ℝ}
    {pm pp : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hm : pm∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1)
    (hp : pp∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1)
    (hD : 0<D) (hb : 0≤b) (hbD : b≤D/16) (ht : 0≤t) (ht1 : t≤1/2)
    (hBo : ∀ s,0≤B s ∧ B s≤H) (hB0 : B 0≤2)
    (hl : (v (riemannianExp (sprayFlow t z).1 pm)-a)/D≤1/16)
    (hr : 7/8≤(v (riemannianExp (sprayFlow t z).1 pp)-a)/D)
    (hanchor : -b*B 0≤transformRayDifference (modifiedDatum v a D b B) z a t ∧
      transformRayDifference (modifiedDatum v a D b B) z a t ≤ r)
    (hsmall : 2*t*‖z.2‖^2+2*b*H+2*r≤D/4) :
    ‖pp‖^2≤‖z.2‖^2-D/2 ∧ ‖z.2‖^2-D/2≤‖pm‖^2 := by
  have Hm := active_switch_norm_identity hm
  have Hp := active_switch_norm_identity hp
  have hl' := (div_le_iff₀ hD).mp hl
  have hr' := (le_div_iff₀ hD).mp hr
  have HmB := mul_le_mul_of_nonneg_left (hBo ((v (riemannianExp (sprayFlow t z).1 pm)-a)/D)).2 hb
  have HpB := mul_nonneg hb (hBo ((v (riemannianExp (sprayFlow t z).1 pp)-a)/D)).1
  have H0 := mul_le_mul_of_nonneg_left hB0 hb
  have htP := mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)
  have htime : (1-t)^2*‖z.2‖^2≤‖z.2‖^2 := by
    apply mul_le_of_le_one_left (sq_nonneg _) _
    nlinarith only [ht,ht1]
  constructor
  · nlinarith only [Hp,hr',HpB,H0,htime,hanchor.1,hbD,hD]
  · nlinarith only [Hm,hl',HmB,htP,hsmall,hanchor.2,hD]

lemma WeakMTW.active_hull_double_contact (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈convexHull ℝ (activeLogs v x)) :
    p∈minimizingVectors x ∧ contactGap (cTransform v) (cTransform (cTransform v))
      x (riemannianExp x p)=0 := by
  obtain ⟨hm,H⟩ := hmtw.active_hull_global_support hv hp
  refine ⟨hm,le_antisymm ?_ ?_⟩
  · have hh : cTransform (cTransform v) (riemannianExp x p)≤-cTransform v x-cost x (riemannianExp x p) := by
      rw [cTransform_le_iff (continuous_cTransform hv)]
      intro z
      rw [cost_symm]
      linarith only [H z]
    dsimp only [contactGap]
    linarith only [hh]
  · have hh := cTransform_gap_nonneg (continuous_cTransform hv) (riemannianExp x p) x
    dsimp only [contactGap] at hh ⊢
    rw [cost_symm (riemannianExp x p) x] at hh
    linarith only [hh]

end SwitchNorms
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section PositiveExcess
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma positive_modified_excess_at_midnorm {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {a D b r C d t : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    (ha : v (riemannianExp z.1 z.2)=a)
    (hb : 0≤b) (hD : 0<D) (hbD : b≤D/16) (ht : 0≤t) (ht1 : t≤1/2)
    (htime : b/(32*D)≤t)
    (hgap0 : contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2) ≤ r)
    (hc0 : ∀ s, -1≤Bc s) (hc1 : ∀ s≤1/2,1-1/1024≤Bc s) (ho0 : Bo 0≤1+1/1024)
    (hsmall : ‖t • z.2‖<d) (herror : r+(C+1)*t^2*‖z.2‖^2≤b/1024)
    (p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1)
    (hp : p∈minimizingVectors (sprayFlow t z).1)
    (hpN : ‖p‖^2=‖z.2‖^2-D/2)
    (hpC : contactGap (cTransform (modifiedDatum v a D b Bo))
      (cTransform (cTransform (modifiedDatum v a D b Bo)))
      (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p)=0)
    (hTaylor : ∀ p' w : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1,
      p'∈minimizingVectors (sprayFlow t z).1 → ‖w‖<d →
      cost (riemannianExp (sprayFlow t z).1 w) (riemannianExp (sprayFlow t z).1 p')≤
        cost (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p')-inner ℝ p' w+C*‖w‖^2) :
    b/1024≤ modifiedExcess v a D b Bc Bo (riemannianExp (sprayFlow t z).1 p) := by
  let y := riemannianExp (sprayFlow t z).1 p
  let w := modifiedDatum v a D b Bo
  have hw : Continuous w := continuous_modifiedDatum hv a D b ho
  have Hg := cTransform_gap_nonneg hw (sprayFlow t z).1 (riemannianExp z.1 z.2)
  have hy0 : (v (riemannianExp z.1 z.2)-a)/D=0 := by rw [ha]; simp
  rw [contactGap,minimizing_ray_tail_cost hz ht (by linarith only [ht1]) ] at Hg
  change 0 ≤ cTransform w (sprayFlow t z).1+(1-t)^2*‖z.2‖^2/2+
    (v (riemannianExp z.1 z.2)+b*Bo ((v (riemannianExp z.1 z.2)-a)/D)) at Hg
  rw [hy0,ha] at Hg
  have HE := modified_excess_at_contact (Bc := Bc) hpC
  change modifiedExcess v a D b Bc Bo y=v y+b*Bc ((v y-a)/D)+cost (sprayFlow t z).1 y+cTransform w (sprayFlow t z).1 at HE
  have hcost : cost (sprayFlow t z).1 y=‖z.2‖^2/2-D/4 := by
    rw [show y=riemannianExp (sprayFlow t z).1 p from rfl,cost_minimizingVector hp,hpN]
    ring
  change b/1024≤ modifiedExcess v a D b Bc Bo y
  by_cases hlevel : (v y-a)/D≤1/2
  · have hBc := mul_le_mul_of_nonneg_left (hc1 _ hlevel) hb
    have hBo := mul_le_mul_of_nonneg_left ho0 hb
    have hG := cTransform_gap_nonneg hv z.1 y
    rw [contactGap,cost_minimizingVector hz,ha] at hgap0
    dsimp only [contactGap] at hG
    have hback : riemannianExp (sprayFlow t z).1 ((-t) • (sprayFlow t z).2)=z.1 := by
      rw [riemannianExp_smul]
      change (sprayFlow (-t) (sprayFlow t z)).1=z.1
      rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]
    have hwidth : ‖(-t) • (sprayFlow t z).2‖<d := by
      simpa only [norm_smul,Real.norm_eq_abs,abs_neg,sprayFlow_speed] using hsmall
    have HT := hTaylor p ((-t) • (sprayFlow t z).2) hp hwidth
    rw [hback,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ht,sprayFlow_speed] at HT
    change cost z.1 y ≤ cost (sprayFlow t z).1 y-(-t)*inner ℝ p (sprayFlow t z).2+C*(t*‖z.2‖)^2 at HT
    have hcross : D/4≤‖z.2‖^2-inner ℝ p (sprayFlow t z).2 := by
      have H := norm_sub_sq_real p (sprayFlow t z).2
      rw [sprayFlow_speed,hpN] at H
      nlinarith only [H,sq_nonneg ‖p-(sprayFlow t z).2‖]
    have hcross' := mul_le_mul_of_nonneg_right hcross ht
    have htime' := (div_le_iff₀ (by positivity : 0<32*D)).mp htime
    have htP := mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)
    nlinarith only [HE,Hg,hBc,hBo,hG,hgap0,HT,hcross',htime',herror,htP,hb]
  · have hl : D/2≤v y-a := by
      have H := (le_div_iff₀ hD).mp (le_of_lt (lt_of_not_ge hlevel))
      linarith only [H]
    have hBc := mul_le_mul_of_nonneg_left (hc0 ((v y-a)/D)) hb
    have hBo := mul_le_mul_of_nonneg_left ho0 hb
    have htime' : 0≤(2*t-t^2)*‖z.2‖^2 := by
      apply mul_nonneg _ (sq_nonneg _)
      nlinarith only [ht,ht1]
    nlinarith only [HE,Hg,hcost,hl,hBc,hBo,htime',hbD,hb]

end PositiveExcess
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SwitchToExcess
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section SwitchToExcess
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.switch_to_positive_excess_oai (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hd:IsCostDualPair u v)
    {x:M} {p q:TangentSpace 𝓘(ℝ,Model n) x} (hp:p∈minimizingVectors x) (hq:q∈minimizingVectors x)
    {α D b r R H eta C d:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo)
    (ha:v (riemannianExp x p)=α) (ha1:v (riemannianExp x q)=α+D)
    (hb:0 < b) (hD:0 < D) (hr:0 ≤ r) (hR:0 ≤ R) (hC:0 ≤ C)
    (hg0:contactGap u v x (riemannianExp x p) ≤ r)
    (hg1:contactGap u v x (riemannianExp x q) ≤ r)
    (hangle:‖p‖^2-inner ℝ p q≤6*D)
    (heta:0 ≤ eta) (heta1:eta≤1/128) (hrb:r≤b/4) (hbD:b≤D/16)
    (hob:∀s,0 ≤ Bo s ∧ Bo s≤H) (ho0:Bo 0≤1+1/1024) (ho1:Bo 1=0)
    (hol:∀s≤1/16,1≤Bo s) (hbar:∀s∈Icc (1/16) (1-eta),Bo 0+1≤Bo s)
    (hc0:∀s,-1≤Bc s) (hc1:∀s≤1/2,1-1/1024≤Bc s)
    (hsmall:‖((8*b/D):ℝ) • p‖<d)
    (hanchor:b*H+2*r+6*D*(8*b/D)+(C*‖p‖^2)*(8*b/D)^2≤R)
    (hosc:∀z:M,sectionOscillation u v z R≤(1+eta)*D)
    (hlower:4*eta*D+2*r+12*D*(8*b/D)+2*(C*‖p‖^2)*(8*b/D)^2+b≤D)
    (hlower':2*(C*‖p‖^2)*(8*b/D)≤2*D)
    (hnorm:2*(8*b/D)*‖p‖^2+2*b*H+2*r≤D/4)
    (herror:r+(C+1)*(8*b/D)^2*‖p‖^2≤b/1024)
    (hTaylor:∀z:M,∀p' w:TangentSpace 𝓘(ℝ,Model n) z,
      p'∈minimizingVectors z → ‖w‖<d → cost (riemannianExp z w) (riemannianExp z p')≤
        cost z (riemannianExp z p')-inner ℝ p' w+C*‖w‖^2) :
    ∃y:M,b / 1024 ≤ modifiedExcess v α D b Bc Bo y := by
  let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨x,p⟩
  let T:ℝ:=8*b/D
  have hT:0<T:=by dsimp [T] <;> positivity
  have hT1:T≤1/2:=by dsimp [T]; apply (div_le_iff₀ hD).mpr; linarith only [hbD]
  have hg0':contactGap (cTransform v) v x (riemannianExp x p) ≤ r:=by rwa [←hd.1]
  have hg1':contactGap (cTransform v) v x (riemannianExp x q) ≤ r:=by rwa [←hd.1]
  have ho02:Bo 0≤2:=by linarith only [ho0]
  obtain ⟨t,ht,ym,yp,hym,hyp,hcm,hcp,hanch⟩:=actual_first_switch (n := n) (z := z) hv hp ho ha ha1 hb hD hrb hbD
    heta (by linarith only [heta1]) (fun s=>(hob s).1) ho02 ho1 hol hbar hg0' hg1'
  have ht0:0 ≤ t:=ht.1.le
  have ht1:t≤1/2:=ht.2.trans hT1
  have htt:t^2≤T^2:=sq_le_sq₀ ht0 hT.le |>.mpr ht.2
  have hTp:‖t • p‖<d:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    have H:=mul_le_mul_of_nonneg_right ht.2 (norm_nonneg p)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hT.le] at hsmall
    exact H.trans_lt hsmall
  have hbench:=ray_benchmark hv hp hq ha hg1' hangle ht0 hTp (hTaylor x)
  have hbench':-cost (sprayFlow t z).1 (riemannianExp x q)-v (riemannianExp x q)≥
      -‖p‖^2/2-α-r+(‖p‖^2-6*D)*t-(C*‖p‖^2)*t^2:=by simpa only [mul_assoc] using hbench
  have hbCH:0 ≤ C*‖p‖^2:=mul_nonneg hC (sq_nonneg _)
  have htimeC:=mul_le_mul_of_nonneg_left htt hbCH
  have htimeD:=mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 6*D by positivity)
  obtain ⟨hga0,hga1⟩:=ray_original_section_anchors hu hv hd hp ho hb.le hob ha ht0
    (by linarith only [ht1]) (hanch t ⟨ht0,le_rfl⟩).2 hbench'
  have hmove:b*H+2*r+6*D*t+(C*‖p‖^2)*t^2≤R:=by linarith only [hanchor,htimeC,htimeD]
  have hbase:b*H+r≤R:=by
    have hnon:0 ≤ 6*D*t+(C*‖p‖^2)*t^2:=by positivity
    linarith only [hmove,hr,hnon]
  have hmod:=modified_contact_original_section hu hv hd ho hb.le hob hcm
  have hmR:ym∈gapSection u v (sprayFlow t z).1 R:=by
    change contactGap u v (sprayFlow t z).1 ym≤R
    exact hmod.trans (by linarith only [hbase,hr])
  have ha0R:riemannianExp x p∈gapSection u v (sprayFlow t z).1 R:=hga0.trans hbase
  have ha1R:riemannianExp x q∈gapSection u v (sprayFlow t z).1 R:=hga1.trans hmove
  have hlev:-2*eta*D≤v ym-α:=by
    have H:=(le_div_iff₀ hD).mp (section_absolute_level_bounds hv hd hR hD ha0R ha1R hmR ha ha1
      (hosc (sprayFlow t z).1)).1
    have hdeta:=mul_nonneg heta hD.le
    nlinarith only [H,hdeta]
  have hstart:rayBenchmarkGap z ym α (v ym) b (Bo ((v ym-α)/D)) D r (C*‖p‖^2) 0≤-b/2:=by
    have HG:=dualPair_gap_nonneg hv hd x ym
    have HL:=mul_le_mul_of_nonneg_left (hol _ hym.le) hb.le
    change contactGap u v x (riemannianExp x p) ≤ r at hg0
    rw [contactGap,cost_minimizingVector hp,ha] at hg0
    dsimp only [rayBenchmarkGap,z]
    rw [sprayFlow_zero]
    norm_num only [mul_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero,sub_zero]
    dsimp only [contactGap] at HG
    linarith only [HG,HL,hg0,hrb]
  have hfinish:0 ≤ rayBenchmarkGap z ym α (v ym) b (Bo ((v ym-α)/D)) D r (C*‖p‖^2) t:=by
    have HG:=cTransform_gap_nonneg (continuous_modifiedDatum hv α D b ho)
      (sprayFlow t z).1 (riemannianExp x q)
    have h1:(v (riemannianExp x q)-α)/D=1:=by rw [ha1,add_sub_cancel_left,div_self hD.ne']
    dsimp only [contactGap,modifiedDatum] at hcm HG
    rw [h1,ho1,mul_zero,add_zero] at HG
    dsimp only [rayBenchmarkGap]
    linarith only [HG,hcm,hbench']
  have hlowert:4*eta*D+2*r+12*D*t+2*(C*‖p‖^2)*t^2+b≤D:=by
    have HD:=mul_le_mul_of_nonneg_left ht.2 (show 0≤12*D by positivity)
    linarith only [hlower,htimeC,HD]
  have hlower't:2*(C*‖p‖^2)*t≤2*D:= (mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans hlower'
  have htime:=benchmark_lower_switch_time hb.le hD ht0 ht1 hbCH (hob _).1 hlev hlowert
    hlower't hstart hfinish
  obtain ⟨pm,hpm,hem⟩:=exists_minimizing_vector (n:=n) (sprayFlow t z).1 ym
  obtain ⟨pp,hpp,hep⟩:=exists_minimizing_vector (n:=n) (sprayFlow t z).1 yp
  have hmA:pm∈activeLogs (modifiedDatum v α D b Bo) (sprayFlow t z).1:=⟨hpm,by rwa [hem]⟩
  have hpA:pp∈activeLogs (modifiedDatum v α D b Bo) (sprayFlow t z).1:=⟨hpp,by rwa [hep]⟩
  have hnormt:2*t*‖p‖^2+2*b*H+2*r≤D/4:=by
    have H:=mul_le_mul_of_nonneg_right ht.2 (show 0≤2*‖p‖^2 by positivity)
    nlinarith only [H,hnorm]
  obtain ⟨hN1,hN2⟩:=active_switch_norm_brackets (z := z) hmA hpA hD hb.le hbD ht0 ht1 hob ho02
    (by rw [hem]; exact hym.le) (by rw [hep]; linarith only [hyp,heta1]) (hanch t ⟨ht0,le_rfl⟩) hnormt
  obtain ⟨w,hw,hwN⟩:=exists_convex_norm_sq hpA hmA hN1 hN2
  obtain ⟨hwmin,hwcontact⟩:=hmtw.active_hull_double_contact (continuous_modifiedDatum hv α D b ho) hw
  refine ⟨riemannianExp (sprayFlow t z).1 w,?_⟩
  apply positive_modified_excess_at_midnorm (z := z) hv hp ho ha hb.le hD hbD ht0 ht1 ?_ hg0'
    hc0 hc1 ho0 hTp ?_ w hwmin hwN hwcontact (hTaylor (sprayFlow t z).1)
  · calc b/(32*D) ≤ b/(20*D) := div_le_div_of_nonneg_left hb.le (by positivity) (by linarith only [hD])
         _ ≤ t := htime
  · have HH:=mul_le_mul_of_nonneg_left htt (show 0≤(C+1)*‖p‖^2 by positivity)
    nlinarith only [herror,HH]

end SwitchToExcess
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess_oai.{u_1}
