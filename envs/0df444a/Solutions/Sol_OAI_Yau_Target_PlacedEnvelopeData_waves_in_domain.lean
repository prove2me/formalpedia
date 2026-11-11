-- Prove2me | solution 1 for OAI.Yau.Target.PlacedEnvelopeData.waves_in_domain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:15.716194+00:00
-- url     : https://prove2.me/submissions/b02ad1cf-cd1d-409b-8d74-e06b7a2e5fcb

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_construct_triple_source_waves

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdaptedMetricFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem positive_form_adapted_basis (g : LinearMap.BilinForm ℝ V)
    (hpos : ∀ v : V, v ≠ 0 → 0 < g v v) (hsym : ∀ u v, g u v = g v u)
    (hdim : Module.finrank ℝ V = 4) (p q : V) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hpp : g p p = a^2) (hqq : g q q = b^2)
    (hpq : g p q = 0) :
    ∃ e : Module.Basis (Fin 4) ℝ V,
      e 0 = a⁻¹ • p ∧ e 1 = b⁻¹ • q ∧
      ∀ i j, g (e i) (e j) = if i = j then 1 else 0 := by
  classical
  let core : InnerProductSpace.Core ℝ V :=
    { inner := fun u v ↦ g u v
      conj_inner_symm := fun u v ↦ hsym v u
      re_inner_nonneg := fun v ↦ by
        by_cases hv : v = 0
        · simp [hv]
        · exact (hpos v hv).le
      add_left := fun u v w ↦ by simp
      smul_left := fun u v r ↦ by simp
      definite := fun v hv ↦ by
        by_contra hn
        exact (ne_of_gt (hpos v hn)) hv }
  let : NormedAddCommGroup V := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let v : Fin 4 → V := ![a⁻¹ • p, b⁻¹ • q, 0, 0]
  let s : Set (Fin 4) := {0,1}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    change g (v i) (v j) = if (⟨i,hi⟩ : s) = ⟨j,hj⟩ then 1 else 0
    have hqp : g q p = 0 := by rw [hsym q p, hpq]
    change i = 0 ∨ i = 1 at hi
    change j = 0 ∨ j = 1 at hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [v, hpp, hqq, hpq, hqp, smul_eq_mul]
    all_goals try (intro hh; have hval := congrArg Subtype.val hh; norm_num at hval)
    all_goals field_simp [ne_of_gt ha, ne_of_gt hb]
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  refine ⟨e.toBasis, he 0 (by simp [s]), he 1 (by simp [s]), ?_⟩
  intro i j
  exact (orthonormal_iff_ite.mp e.orthonormal) i j

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricConnectionFamilyLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

variable {T : Type*} [TopologicalSpace T]
lemma positive_metric_inverse_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ ContinuousLinearMap.inverse (g t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g t) (hp t))).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g t) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact hc'.comp hg.continuousAt

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma christoffelCovector_continuous (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hD : Continuous D) : Continuous (fun t ↦ christoffelCovector (D t)) := by
  have hflip : Continuous (fun t ↦ (D t).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.comp hD
  exact ((hD.add hflip).sub (hflip.const_clm_comp
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).const_smul (1/2:ℝ)

theorem metricConnection_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ)
    (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g) (hD : Continuous D)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ metricConnection (g t) (D t)) := by
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.comp
    (positive_metric_inverse_continuous g hg hp)).clm_comp (christoffelCovector_continuous D hD)

theorem smooth_metric_connection_continuous (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y, ∀ v : E, v ≠ 0 → 0 < g y v v) :
    Continuous (fun y ↦ metricConnection (g y) (fderiv ℝ g y)) := by
  exact metricConnection_continuous g (fderiv ℝ g) hg.continuous
    (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hp

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdaptedNormalChart
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma basis_equivFunL_symm_single (b : Module.Basis (Fin 4) ℝ _root_.OAI.Yau.Jets.Coord) (i : Fin 4) :
    b.equivFunL.symm (Pi.single i 1) = b i := by
  apply b.equivFunL.injective
  rw [b.equivFunL.apply_symm_apply]
  ext k
  simp [Module.Basis.equivFunL, Module.Basis.equivFun, Pi.single_apply, Finsupp.single_apply, eq_comm]

theorem positive_coordinate_adapted_frame (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (p q : _root_.OAI.Yau.Jets.Coord) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hpp : g p p = a^2) (hqq : g q q = b^2) (hpq : g p q = 0) :
    ∃ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = a⁻¹ • p ∧ e (Pi.single 1 1) = b⁻¹ • q ∧
      ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0 := by
  let G : LinearMap.BilinForm ℝ _root_.OAI.Yau.Jets.Coord :=
    (LinearMap.toContinuousLinearMap : (_root_.OAI.Yau.Jets.Coord →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).symm.toLinearMap.comp
      g.toLinearMap
  have hdim : Module.finrank ℝ _root_.OAI.Yau.Jets.Coord = 4 := Module.finrank_fin_fun (R := ℝ)
  obtain ⟨v, hv0, hv1, hv⟩ := positive_form_adapted_basis G hp hs hdim p q a b ha hb hpp hqq hpq
  refine ⟨v.equivFunL.symm, ?_, ?_, ?_⟩
  · rw [basis_equivFunL_symm_single]; exact hv0
  · rw [basis_equivFunL_symm_single]; exact hv1
  · intro i j
    rw [basis_equivFunL_symm_single, basis_equivFunL_symm_single]
    exact hv i j

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFrameOps
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma metricNormalize_unit (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (hv : 0 < g v v) :
    g (metricNormalize g v) (metricNormalize g v) = 1 := by
  have hr : Real.sqrt (g v v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hh := Real.sq_sqrt hv.le
  simp only [metricNormalize, map_smul, smul_apply, smul_eq_mul]
  field_simp
  nlinarith

lemma metricNormalize_fixed (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (hv : g v v = 1) :
    metricNormalize g v = v := by simp [metricNormalize, hv]

lemma metricNormalize_orthogonal (g : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) (huv : g u v = 0) :
    g u (metricNormalize g v) = 0 := by simp [metricNormalize, huv]

variable {ι : Type*} [Fintype ι]

lemma removeFrame_orthogonal [DecidableEq ι] (g : E →L[ℝ] E →L[ℝ] ℝ) (e : ι → E)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) (v : E) (i : ι) :
    g (e i) (removeFrame g e v) = 0 := by
  classical
  simp [removeFrame, map_sum, he, mul_ite]

lemma removeFrame_fixed (g : E →L[ℝ] E →L[ℝ] ℝ) (e : ι → E) (v : E)
    (hv : ∀ i, g (e i) v = 0) : removeFrame g e v = v := by simp [removeFrame, hv]

variable {T : Type*} [TopologicalSpace T]
lemma metricNormalize_continuousAt (g : T → E →L[ℝ] E →L[ℝ] ℝ) (v : T → E) {t : T}
    (hg : ContinuousAt g t) (hv : ContinuousAt v t) (hpos : 0 < g t (v t) (v t)) :
    ContinuousAt (fun s ↦ metricNormalize (g s) (v s)) t := by
  exact (((hg.clm_apply hv).clm_apply hv).sqrt.inv₀
    (ne_of_gt (Real.sqrt_pos.mpr hpos))).smul hv

lemma metricNormalize_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (v : T → E)
    (hg : Continuous g) (hv : Continuous v) (hpos : ∀ t, 0 < g t (v t) (v t)) :
    Continuous (fun s ↦ metricNormalize (g s) (v s)) :=
  continuous_iff_continuousAt.mpr (fun t ↦ metricNormalize_continuousAt g v hg.continuousAt hv.continuousAt (hpos t))

lemma removeFrame_continuousAt (g : T → E →L[ℝ] E →L[ℝ] ℝ) (e : T → ι → E) (v : T → E) {t : T}
    (hg : ContinuousAt g t) (he : ∀ i, ContinuousAt (fun s ↦ e s i) t) (hv : ContinuousAt v t) :
    ContinuousAt (fun s ↦ removeFrame (g s) (e s) (v s)) t := by
  classical
  apply hv.sub
  have hsum (s : Finset ι) : ContinuousAt (fun x ↦ ∑ i ∈ s, g x (e x i) (v x) • e x i) t := by
    induction s using Finset.induction_on with
    | empty => simpa using (show ContinuousAt (fun _ : T ↦ (0:E)) t from continuousAt_const)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (((hg.clm_apply (he i)).clm_apply hv).smul (he i)).add ih
  exact hsum Finset.univ

lemma removeFrame_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (e : T → ι → E) (v : T → E)
    (hg : Continuous g) (he : ∀ i, Continuous (fun s ↦ e s i)) (hv : Continuous v) :
    Continuous (fun s ↦ removeFrame (g s) (e s) (v s)) :=
  continuous_iff_continuousAt.mpr (fun _ ↦ removeFrame_continuousAt g e v hg.continuousAt
    (fun i ↦ (he i).continuousAt) hv.continuousAt)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ContinuousAdaptedFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : Type*} [TopologicalSpace T]

theorem continue_two_axes (g : T → E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g)
    (hs : ∀ t u v, g t u v = g t v u) (p q : T → E) (hp : Continuous p) (hq : Continuous q)
    (hpp : ∀ t, g t (p t) (p t) = 1) (hqq : ∀ t, g t (q t) (q t) = 1)
    (hpq : ∀ t, g t (p t) (q t) = 0) (t0 : T) (seed : Fin 4 → E)
    (hseed : ∀ i j, g t0 (seed i) (seed j) = if i = j then 1 else 0)
    (hs0 : seed 0 = p t0) (hs1 : seed 1 = q t0) :
    ∃ (U : Set T) (e : T → Fin 4 → E), U ∈ 𝓝 t0 ∧
      (∀ i, ContinuousOn (fun t ↦ e t i) U) ∧
      (∀ t, e t 0 = p t ∧ e t 1 = q t) ∧
      ∀ t ∈ U, ∀ i j, g t (e t i) (e t j) = if i = j then 1 else 0 := by
  let a : T → Fin 2 → E := fun t ↦ ![p t, q t]
  have hac (i : Fin 2) : Continuous (fun t ↦ a t i) := by fin_cases i; exact hp; exact hq
  have ha (t) (i j : Fin 2) : g t (a t i) (a t j) = if i = j then 1 else 0 := by
    have hqp : g t (q t) (p t) = 0 := by rw [hs t, hpq]
    fin_cases i <;> fin_cases j <;> simp [a, hpp, hqq, hpq, hqp]
  let z2 := fun t ↦ removeFrame (g t) (a t) (seed 2)
  have hz2 : Continuous z2 := removeFrame_continuous g a (fun _ ↦ seed 2) hg hac continuous_const
  have hz20 : z2 t0 = seed 2 := by
    apply removeFrame_fixed
    intro i
    fin_cases i
    · simpa [a, ← hs0] using hseed 0 2
    · simpa [a, ← hs1] using hseed 1 2
  have hz2pos : 0 < g t0 (z2 t0) (z2 t0) := by rw [hz20, hseed]; norm_num
  let e2 := fun t ↦ metricNormalize (g t) (z2 t)
  have he20 : e2 t0 = seed 2 := by
    dsimp [e2]
    rw [hz20, metricNormalize_fixed _ _ (by simpa using hseed 2 2)]
  have he2c {t : T} (ht : 0 < g t (z2 t) (z2 t)) : ContinuousAt e2 t :=
    metricNormalize_continuousAt g z2 hg.continuousAt hz2.continuousAt ht
  have he2orth (t : T) (i : Fin 2) : g t (a t i) (e2 t) = 0 :=
    metricNormalize_orthogonal (g t) (a t i) (z2 t) (removeFrame_orthogonal (g t) (a t) (ha t) (seed 2) i)
  let b : T → Fin 3 → E := fun t ↦ ![p t, q t, e2 t]
  have hbc {t : T} (ht : 0 < g t (z2 t) (z2 t)) (i : Fin 3) :
      ContinuousAt (fun s ↦ b s i) t := by
    fin_cases i
    · exact hp.continuousAt
    · exact hq.continuousAt
    · exact he2c ht
  have hb {t : T} (ht : 0 < g t (z2 t) (z2 t)) (i j : Fin 3) :
      g t (b t i) (b t j) = if i = j then 1 else 0 := by
    have hqp : g t (q t) (p t) = 0 := by rw [hs t, hpq]
    have hp2 : g t (p t) (e2 t) = 0 := he2orth t 0
    have hq2 : g t (q t) (e2 t) = 0 := he2orth t 1
    have h2p : g t (e2 t) (p t) = 0 := by rw [hs t, hp2]
    have h2q : g t (e2 t) (q t) = 0 := by rw [hs t, hq2]
    have h22 : g t (e2 t) (e2 t) = 1 := metricNormalize_unit _ _ ht
    fin_cases i <;> fin_cases j <;> simp [b, hpp, hqq, hpq, hqp, hp2, hq2, h2p, h2q, h22]
  let z3 := fun t ↦ removeFrame (g t) (b t) (seed 3)
  have hz3c {t : T} (ht : 0 < g t (z2 t) (z2 t)) : ContinuousAt z3 t :=
    removeFrame_continuousAt g b (fun _ ↦ seed 3) hg.continuousAt (hbc ht) continuousAt_const
  have hz30 : z3 t0 = seed 3 := by
    apply removeFrame_fixed
    intro i
    fin_cases i
    · simpa [b, ← hs0] using hseed 0 3
    · simpa [b, ← hs1] using hseed 1 3
    · simpa [b, he20] using hseed 2 3
  have hz3pos : 0 < g t0 (z3 t0) (z3 t0) := by rw [hz30, hseed]; norm_num
  let e3 := fun t ↦ metricNormalize (g t) (z3 t)
  let U : Set T := {t | 0 < g t (z2 t) (z2 t)} ∩ {t | 0 < g t (z3 t) (z3 t)}
  have hU : U ∈ 𝓝 t0 := by
    apply inter_mem
    · exact (isOpen_lt continuous_const ((hg.clm_apply hz2).clm_apply hz2)).mem_nhds hz2pos
    · exact ((hg.continuousAt.clm_apply (hz3c hz2pos)).clm_apply (hz3c hz2pos)).preimage_mem_nhds
        (Ioi_mem_nhds hz3pos)
  let e : T → Fin 4 → E := fun t ↦ ![p t, q t, e2 t, e3 t]
  refine ⟨U, e, hU, ?_, fun t ↦ ⟨rfl, rfl⟩, ?_⟩
  · intro i t ht
    apply ContinuousAt.continuousWithinAt
    fin_cases i
    · exact hp.continuousAt
    · exact hq.continuousAt
    · exact he2c ht.1
    · exact metricNormalize_continuousAt g z3 hg.continuousAt (hz3c ht.1) ht.2
  · intro t ht i j
    have he3orth (i : Fin 3) : g t (b t i) (e3 t) = 0 :=
      metricNormalize_orthogonal _ _ _ (removeFrame_orthogonal (g t) (b t) (hb ht.1) (seed 3) i)
    have hqp : g t (q t) (p t) = 0 := by rw [hs t, hpq]
    have hp2 : g t (p t) (e2 t) = 0 := he2orth t 0
    have hq2 : g t (q t) (e2 t) = 0 := he2orth t 1
    have h2p : g t (e2 t) (p t) = 0 := by rw [hs t, hp2]
    have h2q : g t (e2 t) (q t) = 0 := by rw [hs t, hq2]
    have h22 : g t (e2 t) (e2 t) = 1 := metricNormalize_unit _ _ ht.1
    have hp3 : g t (p t) (e3 t) = 0 := he3orth 0
    have hq3 : g t (q t) (e3 t) = 0 := he3orth 1
    have h23 : g t (e2 t) (e3 t) = 0 := he3orth 2
    have h3p : g t (e3 t) (p t) = 0 := by rw [hs t, hp3]
    have h3q : g t (e3 t) (q t) = 0 := by rw [hs t, hq3]
    have h32 : g t (e3 t) (e2 t) = 0 := by rw [hs t, h23]
    have h33 : g t (e3 t) (e3 t) = 1 := metricNormalize_unit _ _ ht.2
    fin_cases i <;> fin_cases j <;>
      simp [e, hpp, hqq, hpq, hqp, hp2, hq2, h2p, h2q, h22, hp3, hq3, h23, h3p, h3q, h32, h33]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalAdaptedFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem exists_continuous_unit_adapted_frame (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hs : ∀ t u v, g t u v = g t v u)
    (p q : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hq : Continuous q)
    (hpp : ∀ t, g t (p t) (p t) = 1) (hqq : ∀ t, g t (q t) (q t) = 1)
    (hpq : ∀ t, g t (p t) (q t) = 0) (t0 : T)
    (hpos : ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g t0 v v) :
    ∃ (U : Set T) (e : T → Fin 4 → _root_.OAI.Yau.Jets.Coord), U ∈ 𝓝 t0 ∧
      (∀ i, ContinuousOn (fun t ↦ e t i) U) ∧
      (∀ t, e t 0 = p t ∧ e t 1 = q t) ∧
      ∀ t ∈ U, ∀ i j, g t (e t i) (e t j) = if i = j then 1 else 0 := by
  obtain ⟨v, hv0, hv1, hv⟩ := positive_coordinate_adapted_frame (g t0) hpos (hs t0)
    (p t0) (q t0) 1 1 (by norm_num) (by norm_num)
    (by simpa using hpp t0) (by simpa using hqq t0) (hpq t0)
  exact continue_two_axes g hg hs p q hp hq hpp hqq hpq t0
    (fun i ↦ v (Pi.single i 1)) hv (by simpa using hv0) (by simpa using hv1)

theorem exists_continuous_adapted_frame (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hs : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t, ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g t v v)
    (p q : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hq : Continuous q)
    (hp0 : ∀ t, p t ≠ 0) (hq0 : ∀ t, q t ≠ 0)
    (hpq : ∀ t, g t (p t) (q t) = 0) (t0 : T) :
    ∃ (U : Set T) (e : T → Fin 4 → _root_.OAI.Yau.Jets.Coord), U ∈ 𝓝 t0 ∧
      (∀ i, ContinuousOn (fun t ↦ e t i) U) ∧
      (∀ t, e t 0 = metricNormalize (g t) (p t) ∧ e t 1 = metricNormalize (g t) (q t)) ∧
      ∀ t ∈ U, ∀ i j, g t (e t i) (e t j) = if i = j then 1 else 0 := by
  apply exists_continuous_unit_adapted_frame g hg hs
    (fun t ↦ metricNormalize (g t) (p t)) (fun t ↦ metricNormalize (g t) (q t))
    (metricNormalize_continuous g p hg hp (fun t ↦ hpos t _ (hp0 t)))
    (metricNormalize_continuous g q hg hq (fun t ↦ hpos t _ (hq0 t)))
    (fun t ↦ metricNormalize_unit _ _ (hpos t _ (hp0 t)))
    (fun t ↦ metricNormalize_unit _ _ (hpos t _ (hq0 t)))
    _ t0 (hpos t0)
  intro t
  simp [metricNormalize, hpq]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartedEnvelope
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (metricGradient g S) :=
  (positive_metric_inverse_continuous g hg.continuous hp).clm_apply
    (hS.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalDirection
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

lemma metricNormalize_rescale (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (v : _root_.OAI.Yau.Jets.Coord)
    (h : 0 < g v v) : Real.sqrt (g v v) • metricNormalize g v = v := by
  simp [metricNormalize, smul_smul, ne_of_gt (Real.sqrt_pos.mpr h)]

theorem continue_admissible_direction (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t, ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (t0 : T) (q0 : _root_.OAI.Yau.Jets.Coord) (hperp : g t0 (p t0) q0 = 0)
    (hlen : g t0 q0 q0 = g t0 (p t0) (p t0)+4)
    (hstrict : 0 < H t0 (p t0) (p t0)+H t0 q0 q0) :
    ∃ (U : Set T) (q : T → _root_.OAI.Yau.Jets.Coord), U ∈ 𝓝 t0 ∧ ContinuousOn q U ∧ q t0 = q0 ∧
      ∀ t ∈ U, g t (p t) (q t) = 0 ∧
        g t (q t) (q t) = g t (p t) (p t)+4 ∧
        0 < H t (p t) (p t)+H t (q t) (q t) := by
  let e := fun t ↦ metricNormalize (g t) (p t)
  have he : Continuous e := metricNormalize_continuous g p hg hp (fun t ↦ hpos t _ (hp0 t))
  let a : T → Fin 1 → _root_.OAI.Yau.Jets.Coord := fun t _ ↦ e t
  have ha (t : T) (i j : Fin 1) : g t (a t i) (a t j) = if i = j then 1 else 0 := by
    have hij : i = j := Subsingleton.elim _ _
    simpa [a, hij] using metricNormalize_unit (g t) (p t) (hpos t _ (hp0 t))
  let z := fun t ↦ removeFrame (g t) (a t) q0
  have hz : Continuous z := removeFrame_continuous g a (fun _ ↦ q0) hg (fun _ ↦ he) continuous_const
  have hz0 : z t0 = q0 := by
    apply removeFrame_fixed
    intro i
    simp [a, e, metricNormalize, hperp]
  have hl (t : T) : 0 < g t (p t) (p t)+4 := by have hh := hpos t _ (hp0 t); linarith
  have hzpos : 0 < g t0 (z t0) (z t0) := by rw [hz0, hlen]; exact hl t0
  let q := fun t ↦ Real.sqrt (g t (p t) (p t)+4) • metricNormalize (g t) (z t)
  have hqc {t : T} (ht : 0 < g t (z t) (z t)) : ContinuousAt q t :=
    (((hg.continuousAt.clm_apply hp.continuousAt).clm_apply hp.continuousAt).add continuousAt_const).sqrt.smul
      (metricNormalize_continuousAt g z hg.continuousAt hz.continuousAt ht)
  have hq0 : q t0 = q0 := by
    dsimp [q]
    rw [hz0, ← hlen]
    exact metricNormalize_rescale _ _ (by rw [hlen]; exact hl t0)
  let U : Set T := {t | 0 < g t (z t) (z t)} ∩
    {t | 0 < H t (p t) (p t)+H t (q t) (q t)}
  have hU : U ∈ 𝓝 t0 := by
    apply inter_mem
    · exact (isOpen_lt continuous_const ((hg.clm_apply hz).clm_apply hz)).mem_nhds hzpos
    · have hc := ((hH.continuousAt.clm_apply hp.continuousAt).clm_apply hp.continuousAt).add
        ((hH.continuousAt.clm_apply (hqc hzpos)).clm_apply (hqc hzpos))
      exact hc.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hq0] using hstrict))
  refine ⟨U, q, hU, fun t ht ↦ (hqc ht.1).continuousWithinAt, hq0, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ht.2⟩
  · have hzorth : g t (e t) (z t) = 0 := removeFrame_orthogonal (g t) (a t) (ha t) q0 0
    have hpz : g t (p t) (z t) = 0 := by
      rw [← metricNormalize_rescale (g t) (p t) (hpos t _ (hp0 t))]
      simp only [map_smul, smul_apply, smul_eq_mul]
      change Real.sqrt (g t (p t) (p t)) * g t (e t) (z t) = 0
      rw [hzorth, mul_zero]
    simp [q, metricNormalize, hpz]
  · have hu := metricNormalize_unit (g t) (z t) ht.1
    dsimp [q]
    simp only [map_smul, smul_apply, smul_eq_mul, hu, mul_one]
    nlinarith [Real.sq_sqrt (hl t).le]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdmissibleChartPatch
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (sourceHessian g S) := by
  have hD := hS.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hS.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).sub
    (((ContinuousLinearMap.compL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord ℝ).continuous.comp hD).clm_comp
      (smooth_metric_connection_continuous g hg hp))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_DirectionTripleAlgebra
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma transverseTriple_ne_zero (eps : ℝ) (j : Fin 3) : transverseTriple eps j ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v 1) h
  fin_cases j <;> simp [transverseTriple] at h1

lemma transverseTriple_independent (eps : ℝ) (heps : eps ≠ 0) :
    LinearIndependent ℝ (transverseTriple eps) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 := congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v 1) hc
  have h2 := congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v 2) hc
  have h3 := congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v 3) hc
  simp [Fin.sum_univ_succ,transverseTriple] at h1 h2 h3
  have hc1 : c 1 = 0 := h2.resolve_right heps
  have hc2 : c 2 = 0 := h3.resolve_right heps
  have hc0 : c 0 = 0 := by simpa [hc1,hc2] using h1
  fin_cases j <;> assumption

lemma rescaled_frame_triple_independent (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (eps : ℝ) (heps : eps ≠ 0) (a : Fin 3 → ℝ) (ha : ∀ j, a j ≠ 0) :
    LinearIndependent ℝ (fun j ↦ a j • e (transverseTriple eps j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have he := congrArg e.symm hc
  simp only [map_sum,map_smul,ContinuousLinearEquiv.symm_apply_apply,map_zero,smul_smul] at he
  have h := Fintype.linearIndependent_iff.mp (transverseTriple_independent eps heps)
    (fun i ↦ c i*a i) he j
  exact (mul_eq_zero.mp h).resolve_right (ha j)

lemma transverseTriple_representation (eps : ℝ) (heps : eps ≠ 0) (v : _root_.OAI.Yau.Jets.Coord) (hv : v 0 = 0) :
    v = (v 1-v 2/eps-v 3/eps) • transverseTriple eps 0 +
      (v 2/eps) • transverseTriple eps 1 + (v 3/eps) • transverseTriple eps 2 := by
  ext i
  fin_cases i <;> simp [transverseTriple,hv] <;> field_simp
  ring

lemma rescaled_frame_triple_spans (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (eps : ℝ) (heps : eps ≠ 0) (a : Fin 3 → ℝ) (ha : ∀ j, a j ≠ 0)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : e.symm v 0 = 0) :
    v ∈ Submodule.span ℝ (Set.range (fun j ↦ a j • e (transverseTriple eps j))) := by
  let P := Submodule.span ℝ (Set.range (fun j ↦ a j • e (transverseTriple eps j)))
  have hm (j : Fin 3) : e (transverseTriple eps j) ∈ P := by
    have h := P.smul_mem (a j)⁻¹ (Submodule.subset_span (Set.mem_range_self j))
    simpa [smul_smul,ha j] using h
  have he := congrArg e (transverseTriple_representation eps heps (e.symm v) hv)
  simp only [map_add,map_smul,ContinuousLinearEquiv.apply_symm_apply] at he
  rw [he]
  exact P.add_mem (P.add_mem (P.smul_mem _ (hm 0)) (P.smul_mem _ (hm 1))) (P.smul_mem _ (hm 2))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AdmissibleDirectionTriple
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma transverseDirection_continuous (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (b : ℝ) (j : Fin 3) :
    Continuous (fun eps : ℝ ↦ transverseDirection g e b eps j) := by
  have hz : Continuous (fun eps : ℝ ↦ e (transverseTriple eps j)) := by
    fin_cases j <;> dsimp [transverseTriple] <;> fun_prop
  exact (continuous_const (y := b)).smul (metricNormalize_continuous (fun _ : ℝ ↦ g)
    (fun eps ↦ e (transverseTriple eps j)) continuous_const hz
    (fun eps ↦ hp _ (by intro h; exact transverseTriple_ne_zero eps j (e.injective (by simpa using h)))))

lemma frame_pair_coordinate (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (ho : ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) (v : _root_.OAI.Yau.Jets.Coord) : g (e (Pi.single i 1)) v = e.symm v i := by
  calc
    _ = g (e (Pi.single i 1)) (e (e.symm v)) := by rw [e.apply_symm_apply]
    _ = _ := by
      have hexp : e.symm v = ∑ j : Fin 4, e.symm v j • Pi.single j (1:ℝ) := by
        ext j; simp [Pi.single_apply]
      conv_lhs => rw [hexp]
      simp [map_sum,map_smul,ho,smul_eq_mul]

theorem frame_admissible_direction_triple
    (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (ho : ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b)
    (hstrict : 0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
      H (b • e (Pi.single 1 1)) (b • e (Pi.single 1 1))) :
    ∃ q : Fin 3 → _root_.OAI.Yau.Jets.Coord, LinearIndependent ℝ q ∧
      (∀ j, g (a • e (Pi.single 0 1)) (q j) = 0 ∧ g (q j) (q j) = b^2 ∧
        0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) + H (q j) (q j)) ∧
      ∀ v : _root_.OAI.Yau.Jets.Coord, g (a • e (Pi.single 0 1)) v = 0 → v ∈ Submodule.span ℝ (Set.range q) := by
  have hnon (eps : ℝ) (j : Fin 3) : e (transverseTriple eps j) ≠ 0 := by
    intro h
    exact transverseTriple_ne_zero eps j (e.injective (by simpa using h))
  have hz (j : Fin 3) : transverseDirection g e b 0 j = b • e (Pi.single 1 1) := by
    fin_cases j <;> simp [transverseDirection,transverseTriple,metricNormalize,ho]
  have hev (j : Fin 3) : ∀ᶠ eps : ℝ in 𝓝 0,
      0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
        H (transverseDirection g e b eps j) (transverseDirection g e b eps j) := by
    have hq := transverseDirection_continuous g hp e b j
    have hc : Continuous (fun eps : ℝ ↦
        H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
          H (transverseDirection g e b eps j) (transverseDirection g e b eps j)) :=
      continuous_const.add (((continuous_const (y := H)).clm_apply hq).clm_apply hq)
    exact hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hz] using hstrict))
  obtain ⟨d,hd,hdi⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.mpr hev)
  let eps : ℝ := d/2
  have heps : eps ≠ 0 := by dsimp [eps] <;> positivity
  have hestrict := hdi (show eps ∈ Metric.ball 0 d by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by dsimp [eps] <;> positivity)]
    dsimp [eps] <;> linarith)
  let c : Fin 3 → ℝ := fun j ↦ b * (Real.sqrt (g (e (transverseTriple eps j)) (e (transverseTriple eps j))))⁻¹
  have hc (j : Fin 3) : c j ≠ 0 := mul_ne_zero (ne_of_gt hb)
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hp _ (hnon eps j)))))
  have hq (j : Fin 3) : transverseDirection g e b eps j = c j • e (transverseTriple eps j) := by
    simp [transverseDirection,metricNormalize,c,smul_smul]
  have hqf : transverseDirection g e b eps = fun j ↦ c j • e (transverseTriple eps j) := funext hq
  refine ⟨transverseDirection g e b eps,?_,?_,?_⟩
  · rw [hqf]
    exact rescaled_frame_triple_independent e eps heps c hc
  · intro j
    refine ⟨?_,?_,hestrict j⟩
    · rw [hq]
      have hpair : g (e (Pi.single 0 1)) (e (transverseTriple eps j)) = 0 := by
        rw [frame_pair_coordinate g e ho, e.symm_apply_apply]
        fin_cases j <;> simp [transverseTriple]
      simp [map_smul,smul_eq_mul,hpair]
    · have hn := metricNormalize_unit g (e (transverseTriple eps j)) (hp _ (hnon eps j))
      simp only [transverseDirection,map_smul,smul_apply,smul_eq_mul,hn]
      ring
  · intro v hv
    have hzero : e.symm v 0 = 0 := by
      have hh : a * g (e (Pi.single 0 1)) v = 0 := by simpa [map_smul,smul_eq_mul] using hv
      rw [frame_pair_coordinate g e ho] at hh
      exact (mul_eq_zero.mp hh).resolve_left ha
    rw [hqf]
    exact rescaled_frame_triple_spans e eps heps c hc v hzero

theorem admissible_direction_triple
    (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (p t : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0) (hpt : g p t = 0) (ht : g t t = 1)
    (hstrict : 0 < H p p + (g p p+4)*H t t) :
    ∃ q : Fin 3 → _root_.OAI.Yau.Jets.Coord, LinearIndependent ℝ q ∧
      (∀ j, g p (q j) = 0 ∧ g (q j) (q j) = g p p+4 ∧ 0 < H p p+H (q j) (q j)) ∧
      ∀ v : _root_.OAI.Yau.Jets.Coord, g p v = 0 → v ∈ Submodule.span ℝ (Set.range q) := by
  let a := Real.sqrt (g p p)
  let b := Real.sqrt (g p p+4)
  have ha : 0 < a := Real.sqrt_pos.mpr (hp p hp0)
  have hb : 0 < b := Real.sqrt_pos.mpr (by have h := hp p hp0; linarith)
  have ha2 : a^2 = g p p := Real.sq_sqrt (hp p hp0).le
  have hb2 : b^2 = g p p+4 := Real.sq_sqrt (by have h := hp p hp0; linarith)
  have hqt : g (b • t) (b • t) = b^2 := by
    simp [map_smul,smul_eq_mul,ht,pow_two]
  obtain ⟨e,he0,he1,ho⟩ := positive_coordinate_adapted_frame g hp hs p (b • t) a b ha hb ha2.symm hqt
    (by simp [hpt])
  have heP : a • e (Pi.single 0 1) = p := by simp [he0,smul_smul,ne_of_gt ha]
  have heQ : b • e (Pi.single 1 1) = b • t := by simp [he1,smul_smul,ne_of_gt hb]
  have hHq : H (b • t) (b • t) = (g p p+4)*H t t := by
    simp only [map_smul,smul_apply,smul_eq_mul]
    calc
      b*(b*H t t) = b^2*H t t := by ring
      _ = _ := by rw [hb2]
  have hstr : 0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
      H (b • e (Pi.single 1 1)) (b • e (Pi.single 1 1)) := by
    rw [heP,heQ,hHq]
    exact hstrict
  obtain ⟨q,hqi,hq,hspan⟩ := frame_admissible_direction_triple g H hp e ho a b (ne_of_gt ha) hb hstr
  exact ⟨q,hqi,by simpa only [heP,hb2] using hq,by simpa only [heP] using hspan⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalDirectionTriple
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem continue_admissible_triple (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t, ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (t0 : T) (q0 : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hInd : LinearIndependent ℝ q0)
    (hperp : ∀ j, g t0 (p t0) (q0 j) = 0)
    (hlen : ∀ j, g t0 (q0 j) (q0 j) = g t0 (p t0) (p t0)+4)
    (hstrict : ∀ j, 0 < H t0 (p t0) (p t0)+H t0 (q0 j) (q0 j)) :
    ∃ (U : Set T) (q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord), U ∈ 𝓝 t0 ∧ ContinuousOn q U ∧ q t0 = q0 ∧
      ∀ t ∈ U, LinearIndependent ℝ (q t) ∧ ∀ j,
        g t (p t) (q t j) = 0 ∧ g t (q t j) (q t j) = g t (p t) (p t)+4 ∧
          0 < H t (p t) (p t)+H t (q t j) (q t j) := by
  have hex (j : Fin 3) := continue_admissible_direction g H hg hH hpos p hp hp0
    t0 (q0 j) (hperp j) (hlen j) (hstrict j)
  choose Uj qj hUj hqj hq0 hprop using hex
  let q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord := fun t j ↦ qj j t
  have hqt : q t0 = q0 := funext hq0
  have hqc : ContinuousAt q t0 := continuousAt_pi.mpr (fun j ↦ (hqj j).continuousAt (hUj j))
  have hI : ∀ᶠ t in 𝓝 t0, LinearIndependent ℝ (q t) := by
    have hh : ∀ᶠ q' : Fin 3 → _root_.OAI.Yau.Jets.Coord in 𝓝 (q t0), LinearIndependent ℝ q' := by
      rw [hqt]
      exact hInd.eventually
    exact hqc.eventually hh
  let U : Set T := {t | LinearIndependent ℝ (q t)} ∩ ⋂ j, Uj j
  have hU : U ∈ 𝓝 t0 := inter_mem hI (Filter.iInter_mem.mpr hUj)
  refine ⟨U,q,hU,?_,hqt,?_⟩
  · apply continuousOn_pi.mpr
    intro j
    exact (hqj j).mono (fun t ht ↦ mem_iInter.mp ht.2 j)
  · intro t ht
    exact ⟨ht.1,fun j ↦ hprop j t (mem_iInter.mp ht.2 j)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalFrameTriple
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem exists_local_frame_triple
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hs : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (t0 : T) (hdir : ∃ v : _root_.OAI.Yau.Jets.Coord, g t0 (p t0) v = 0 ∧ g t0 v v = 1 ∧
      0 < H t0 (p t0) (p t0)+(g t0 (p t0) (p t0)+4)*H t0 v v) :
    ∃ U : Set T, U ∈ 𝓝 t0 ∧ Nonempty
      (AdmissibleFrameTriple (fun t : U ↦ g t) (fun t : U ↦ H t) (fun t : U ↦ p t)) := by
  obtain ⟨v,hvp,hvv,hvH⟩ := hdir
  obtain ⟨q0,hqI,hq0,_⟩ := admissible_direction_triple (g t0) (H t0) (hpos t0)
    (hs t0) (p t0) v (hp0 t0) hvp hvv hvH
  obtain ⟨U,q,hU,hq,_,hprop⟩ := continue_admissible_triple g H hg hH hpos p hp hp0
    t0 q0 hqI (fun j ↦ (hq0 j).1) (fun j ↦ (hq0 j).2.1) (fun j ↦ (hq0 j).2.2)
  let u0 : U := ⟨t0,mem_of_mem_nhds hU⟩
  have hqc : Continuous (fun t : U ↦ q t) := continuousOn_iff_continuous_domRestrict.mp hq
  have hqne (t : U) (j : Fin 3) : q t j ≠ 0 := by
    intro hz
    have hh := ((hprop t t.property).2 j).2.1
    rw [hz] at hh
    have hhpos := hpos t (p t) (hp0 t)
    simp only [map_zero] at hh
    linarith
  have hex (j : Fin 3) := exists_continuous_adapted_frame
    (fun t : U ↦ g t) (hg.comp continuous_subtype_val) (fun t ↦ hs t)
    (fun t ↦ hpos t) (fun t : U ↦ p t) (fun t : U ↦ q t j)
    (hp.comp continuous_subtype_val) ((continuous_apply j).comp hqc)
    (fun t ↦ hp0 t) (fun t ↦ hqne t j) (fun t ↦ ((hprop t t.property).2 j).1) u0
  choose V e hV he haxes ho using hex
  let W : Set U := ⋂ j, V j
  have hW : W ∈ 𝓝 u0 := Filter.iInter_mem.mpr hV
  let D : Set T := Subtype.val '' W
  have hD : D ∈ 𝓝 t0 := by
    have hh := mem_nhds_subtype_iff_nhdsWithin.mp hW
    rwa [nhdsWithin_eq_nhds.mpr hU] at hh
  let f : D → U := fun t ↦ ⟨t,by obtain ⟨u,_,hu⟩ := t.property; simp [← hu]⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hfV (t : D) (j : Fin 3) : f t ∈ V j := by
    obtain ⟨u,hu,heq⟩ := t.property
    have hh : f t = u := Subtype.ext heq.symm
    rw [hh]
    exact mem_iInter.mp hu j
  refine ⟨D,hD,⟨{
    q := fun t ↦ q t
    continuous_q := hqc.comp hf
    independent := fun t ↦ (hprop t (f t).property).1
    perpendicular := fun t j ↦ ((hprop t (f t).property).2 j).1
    length := fun t j ↦ ((hprop t (f t).property).2 j).2.1
    strict := fun t j ↦ ((hprop t (f t).property).2 j).2.2
    e := fun t j ↦ e j (f t)
    continuous_e := ?_
    orthonormal := fun t j ↦ ho j (f t) (hfV t j)
    first := fun t j ↦ (haxes j (f t)).1
    second := fun t j ↦ (haxes j (f t)).2 }⟩⟩
  intro j i
  exact (he j i).comp_continuous hf (fun t ↦ hfV t j)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CompactFrameCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem exists_compact_frame_cover [CompactSpace T] [T2Space T]
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hs : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (hdir : ∀ t, ∃ v : _root_.OAI.Yau.Jets.Coord, g t (p t) v = 0 ∧ g t v v = 1 ∧
      0 < H t (p t) (p t)+(g t (p t) (p t)+4)*H t v v) :
    Nonempty (CompactFrameCover g H p) := by
  classical
  have hex (t : T) := exists_local_frame_triple g H hg hH hs hpos p hp hp0 t (hdir t)
  choose U hU hd using hex
  choose K hK hKU hKc using fun t ↦ local_compact_nhds (hU t)
  have hcover : (univ : Set T) ⊆ ⋃ t, interior (K t) := by
    intro t _
    exact mem_iUnion.mpr ⟨t,mem_interior_iff_mem_nhds.mpr (hK t)⟩
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun t ↦ interior (K t)) (fun _ ↦ isOpen_interior) hcover
  refine ⟨⟨s,K,hKc,?_,?_⟩⟩
  · intro t
    obtain ⟨i,hi,ht⟩ := mem_iUnion₂.mp (hscover (mem_univ t))
    exact ⟨i,hi,interior_subset ht⟩
  · intro i
    exact (Classical.choice (hd i)).pullback
      (fun t : K i ↦ (⟨t,hKU i t.property⟩ : U i))
      (continuous_subtype_val.subtype_mk _)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    metricGradient g S =ᶠ[𝓝 x] metricGradient G A := by
  filter_upwards [hg,hS.fderiv (𝕜 := ℝ)] with z hz hd
  simp only [metricGradient,hz,hd]

lemma sourceHessian_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    sourceHessian g S =ᶠ[𝓝 x] sourceHessian G A := by
  filter_upwards [hg,hg.fderiv (𝕜 := ℝ),hS.fderiv (𝕜 := ℝ),
    (hS.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)] with z hz hd hs hss
  simp only [sourceHessian,hz,hd,hs,hss]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransverseSpanning
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma perpendicular_span_le_ker (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p : _root_.OAI.Yau.Jets.Coord) (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hperp : ∀ j, g p (q j) = 0) :
    Submodule.span ℝ (range q) ≤ (g p).toLinearMap.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact hperp j

lemma perpendicular_triple_basis (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0) :
    Submodule.span ℝ (range (Fin.cons p q)) = ⊤ := by
  have hnot : p ∉ Submodule.span ℝ (range q) := by
    intro h
    have hh := perpendicular_span_le_ker g p q hperp h
    exact (ne_of_gt (hp p hp0)) hh
  have hi : LinearIndependent ℝ (Fin.cons p q) := linearIndependent_finCons.mpr ⟨hq,hnot⟩
  exact hi.span_eq_top_of_card_eq_finrank' (by simp [_root_.OAI.Yau.Jets.Coord])

theorem perpendicular_triple_spans (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : g p v = 0) : v ∈ Submodule.span ℝ (range q) := by
  have htop := perpendicular_triple_basis g hp p hp0 q hq hperp
  have hvtop : v ∈ Submodule.span ℝ (insert p (range q)) := by
    rw [← Fin.range_cons,htop]
    trivial
  obtain ⟨a,u,hu,rfl⟩ := Submodule.mem_span_insert.mp hvtop
  have hgu : g p u = 0 := perpendicular_span_le_ker g p q hperp hu
  have ha : a = 0 := by
    have hh : a * g p p = 0 := by simpa [map_add,map_smul,smul_eq_mul,hgu] using hv
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt (hp p hp0))
  simpa [ha] using hu

theorem transverseEnergy_pos (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : g p v = 0) (hv0 : v ≠ 0) : 0 < transverseEnergy g q v := by
  have hnon : 0 ≤ transverseEnergy g q v := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have hzero : ∀ j, g (q j) v = 0 := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      sq_nonneg (g (q j) v))).mp hz.symm
    intro j
    exact (sq_eq_zero_iff).mp (he j (Finset.mem_univ j))
  have hker : Submodule.span ℝ (range q) ≤ (g.flip v).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hzero j
  have hgv : g v v = 0 := hker (perpendicular_triple_spans g hp p hp0 q hq hperp v hv)
  exact (ne_of_gt (hp v hv0)) hgv

lemma transverseEnergy_smul (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) (a : ℝ) :
    transverseEnergy g q (a • v) = a^2 * transverseEnergy g q v := by
  simp [transverseEnergy,map_smul,smul_eq_mul,mul_pow,Finset.mul_sum]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTripleBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

omit [CompactSpace T] in
lemma transverseEnergy_continuous
    (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g)
    (q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : Continuous q) :
    Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ transverseEnergy (g z.1) (q z.1) z.2) := by
  apply continuous_finsetSum
  intro j _
  exact (((hg.comp continuous_fst).clm_apply
    (((continuous_apply j).comp hq).comp continuous_fst)).clm_apply continuous_snd).pow 2

theorem uniform_transverse_spanning
    (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : Continuous q)
    (hqi : ∀ t, LinearIndependent ℝ (q t)) (hperp : ∀ t j, g t (p t) (q t j) = 0) :
    ∃ c > 0, ∀ t v, g t (p t) v = 0 → c*‖v‖^2 ≤ transverseEnergy (g t) (q t) v := by
  let A : Set (T × _root_.OAI.Yau.Jets.Coord) := (univ ×ˢ Metric.sphere 0 1) ∩ {z | g z.1 (p z.1) z.2 = 0}
  have hcompact : IsCompact A :=
    (isCompact_univ.prod (isCompact_sphere (0:_root_.OAI.Yau.Jets.Coord) 1)).inter_right
      (isClosed_eq (((hg.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply
        continuous_snd) continuous_const)
  have hpositive : ∀ z ∈ A, 0 < transverseEnergy (g z.1) (q z.1) z.2 := by
    intro z hz
    apply transverseEnergy_pos (g z.1) (hpos z.1) (p z.1) (hp0 z.1)
      (q z.1) (hqi z.1) (hperp z.1) z.2 hz.2
    intro he
    have hn := hz.1.2
    simp [he] at hn
  obtain ⟨c,hc,C,hC,hbound⟩ := compact_positive_bounds hcompact _
    (transverseEnergy_continuous g hg q hq).continuousOn hpositive
  refine ⟨c,hc,?_⟩
  intro t v hv
  by_cases hz : v = 0
  · simp [hz,transverseEnergy]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ (ne_of_gt hn)]
  have hmem : (t,(‖v‖⁻¹ : ℝ) • v) ∈ A := by
    exact ⟨⟨mem_univ t,by simpa only [Metric.mem_sphere,dist_zero_right] using hunit⟩,
      by simp [map_smul,smul_eq_mul,hv]⟩
  have hh := (hbound _ hmem).1
  rw [transverseEnergy_smul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have hn0 : ‖v‖ ≠ 0 := ne_of_gt hn
  have he : ‖v‖^2 * ((‖v‖⁻¹)^2 * transverseEnergy (g t) (q t) v) =
      transverseEnergy (g t) (q t) v := by field_simp
  rw [he] at hmul
  nlinarith

theorem uniform_direction_strictness
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (d : AdmissibleFrameTriple g H p) :
    ∃ c > 0, ∃ C > 0, ∀ t j,
      c ≤ sourceDirectionEta (g t) (H t) (p t) (d.q t j) ∧
      sourceDirectionEta (g t) (H t) (p t) (d.q t j) ≤ C := by
  have hq : Continuous (fun z : T × Fin 3 ↦ d.q z.1 z.2) :=
    continuous_prod_of_discrete_right.mpr (fun j ↦ (continuous_apply j).comp d.continuous_q)
  have hgP : Continuous (fun z : T × Fin 3 ↦ g z.1 (p z.1) (p z.1)) := ((hg.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply (hp.comp continuous_fst)
  have hgQ : Continuous (fun z : T × Fin 3 ↦ g z.1 (d.q z.1 z.2) (d.q z.1 z.2)) := ((hg.comp continuous_fst).clm_apply hq).clm_apply hq
  have hHP : Continuous (fun z : T × Fin 3 ↦ H z.1 (p z.1) (p z.1)) := ((hH.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply (hp.comp continuous_fst)
  have hHQ : Continuous (fun z : T × Fin 3 ↦ H z.1 (d.q z.1 z.2) (d.q z.1 z.2)) := ((hH.comp continuous_fst).clm_apply hq).clm_apply hq
  have hden (z : T × Fin 3) : 0 < g z.1 (p z.1) (p z.1)+g z.1 (d.q z.1 z.2) (d.q z.1 z.2) := by
    rw [d.length]
    have hh := hpos z.1 (p z.1) (hp0 z.1)
    linarith
  have heta : Continuous (fun z : T × Fin 3 ↦ sourceDirectionEta (g z.1) (H z.1)
      (p z.1) (d.q z.1 z.2)) := (hHP.add hHQ).div (hgP.add hgQ) (fun z ↦ ne_of_gt (hden z))
  obtain ⟨c,hc,C,hC,hb⟩ := compact_positive_bounds isCompact_univ _ heta.continuousOn
    (fun z _ ↦ div_pos (d.strict z.1 z.2) (hden z))
  exact ⟨c,hc,C,hC,fun t j ↦ hb (t,j) (mem_univ _)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSmoothExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem compact_smooth_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  have hsupp : tsupport G ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [G,hz])
  refine ⟨G,hG,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_⟩
  intro x hx
  filter_upwards [hb1 x hx] with z hz
  simp [G,hz]

theorem compact_positive_metric_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ,
      ContDiff ℝ ∞ G ∧ (∀ x u v, G x u v = G x v u) ∧
      (∀ x v, v ≠ 0 → 0 < G x v v) ∧ ∀ x ∈ K, G =ᶠ[𝓝 x] g := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  obtain ⟨x0,hx0⟩ := hUn
  let G := fun x ↦ b x • g x + (1-b x) • g x0
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact (hb.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hbU hx)))).add
        ((contDiffAt_const.sub hb.contDiffAt).smul contDiffAt_const)
    · apply (contDiffAt_const (c := g x0)).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x u v
    by_cases hx : x ∈ tsupport b
    · change b x*g x u v+(1-b x)*g x0 u v = b x*g x v u+(1-b x)*g x0 v u
      rw [hs x (hbU hx),hs x0 hx0]
    · simp [G,image_eq_zero_of_notMem_tsupport hx,hs x0 hx0]
  · intro x v hv
    by_cases hx : x ∈ tsupport b
    · have h1 := hp x (hbU hx) v hv
      have h2 := hp x0 hx0 v hv
      have hb0 := (hbr x).1
      have hb1 := (hbr x).2
      change 0 < b x*g x v v+(1-b x)*g x0 v v
      by_cases hz : b x = 0
      · simpa [hz] using h2
      · have ha : 0 < b x := lt_of_le_of_ne hb0 (Ne.symm hz)
        have hleft := mul_pos ha h1
        have hright := mul_nonneg (sub_nonneg.mpr hb1) h2.le
        linarith
    · simpa [G,image_eq_zero_of_notMem_tsupport hx] using hp x0 hx0 v hv
  · intro x hx
    filter_upwards [hb1 x hx] with z hz
    simp [G,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSourceRepresentatives
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem compact_source_representatives {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hS : ContDiffOn ℝ ∞ S U)
    (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (W A : _root_.OAI.Yau.Jets.Coord → ℝ) (E : Set _root_.OAI.Yau.Jets.Coord),
      ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ W ∧ ContDiff ℝ ∞ A ∧
      (∀ x u v, G x u v = G x v u) ∧ (∀ x v, v ≠ 0 → 0 < G x v v) ∧
      IsOpen E ∧ K ⊆ E ∧ E ⊆ U ∧ (∀ x ∈ E, 0 < W x) ∧
      ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) ∧
        metricGradient G A x = metricGradient g S x ∧ sourceHessian G A x = sourceHessian g S x := by
  obtain ⟨G,hG,hGs,hGp,hGe⟩ := compact_positive_metric_extension hK hU hKU hUn g hg hs hp
  obtain ⟨W,hW,_,_,hWe⟩ := compact_smooth_extension hK hU hKU w hw
  obtain ⟨A,hA,_,_,hAe⟩ := compact_smooth_extension hK hU hKU S hS
  let B : Set _root_.OAI.Yau.Jets.Coord := {x | G x = g x ∧ W x = w x ∧ A x = S x}
  let E := U ∩ interior B
  have hE : IsOpen E := hU.inter isOpen_interior
  have hKE : K ⊆ E := by
    intro x hx
    refine ⟨hKU hx,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact (hGe x hx).and ((hWe x hx).and (hAe x hx))
  have hgerm (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ E) : (G =ᶠ[𝓝 x] g) ∧
      (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) := by
    have hh : ∀ᶠ z in 𝓝 x, G z = g z ∧ W z = w z ∧ A z = S z :=
      mem_of_superset (hE.mem_nhds hx) (fun z hz ↦ interior_subset hz.2)
    exact ⟨hh.mono (fun _ h ↦ h.1),hh.mono (fun _ h ↦ h.2.1),hh.mono (fun _ h ↦ h.2.2)⟩
  refine ⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hKE,inter_subset_left,?_,?_⟩
  · intro x hx
    rw [(hgerm x hx).2.1.self_of_nhds]
    exact hwp x hx.1
  · intro x hx
    obtain ⟨heG,heW,heA⟩ := hgerm x hx
    exact ⟨heG,heW,heA,(metricGradient_eventuallyEq heG heA).self_of_nhds,
      (sourceHessian_eventuallyEq heG heA).self_of_nhds⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_CompactSourceWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem construct_compact_source_waves
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hwpos : ∀ x ∈ U, 0 < w x) (hp0 : ∀ x ∈ D, metricGradient g S x ≠ 0)
    (hdir : ∀ x ∈ D, ∃ v : _root_.OAI.Yau.Jets.Coord,
      g x (metricGradient g S x) v = 0 ∧ g x v v = 1 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x)+
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x v v)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ d : SourceCompactFrameCover g S D,
      Nonempty (TripleSourceWaveData g w S (coverSourceCenter d) d.triple m J K k0) ∧
      ∃ cs > 0, ∃ ce > 0, ∃ Ce > 0, ∀ t : d.Parameter,
        (∀ v, g (coverSourceCenter d t) (metricGradient g S (coverSourceCenter d t)) v = 0 →
          cs*‖v‖^2 ≤ transverseEnergy (g (coverSourceCenter d t)) (d.triple.q t) v) ∧
        ∀ j, ce ≤ sourceDirectionEta (g (coverSourceCenter d t)) (sourceHessian g S (coverSourceCenter d t))
          (metricGradient g S (coverSourceCenter d t)) (d.triple.q t j) ∧
          sourceDirectionEta (g (coverSourceCenter d t)) (sourceHessian g S (coverSourceCenter d t))
            (metricGradient g S (coverSourceCenter d t)) (d.triple.q t j) ≤ Ce := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hp := metricGradient_continuous g hg hpos S hS
  have hH := sourceHessian_continuous g hg hpos S hS
  obtain ⟨d⟩ := exists_compact_frame_cover
    (fun t : D ↦ g t) (fun t : D ↦ sourceHessian g S t)
    (hg.continuous.comp continuous_subtype_val) (hH.comp continuous_subtype_val)
    (fun t ↦ hs t) (fun t ↦ hpos t) (fun t : D ↦ metricGradient g S t)
    (hp.comp continuous_subtype_val) (fun t ↦ hp0 t t.property) (fun t ↦ hdir t t.property)
  have hy := continuous_coverSourceCenter d
  have hn (t : d.Parameter) : metricGradient g S (coverSourceCenter d t) ≠ 0 :=
    hp0 _ (d.center t).property
  have hwd := construct_triple_source_waves g hg hs hpos w hw S hS
    (coverSourceCenter d) hy hn d.triple hU (fun t ↦ hDU (d.center t).property) hwpos m J K k0 hm hJ
  obtain ⟨cs,hcs,hspan⟩ := uniform_transverse_spanning
    (g ∘ coverSourceCenter d) (hg.continuous.comp hy) (fun t ↦ hpos _)
    (metricGradient g S ∘ coverSourceCenter d) (hp.comp hy) hn
    d.triple.q d.triple.continuous_q d.triple.independent d.triple.perpendicular
  obtain ⟨ce,hce,Ce,hCe,heta⟩ := uniform_direction_strictness
    (g ∘ coverSourceCenter d) (sourceHessian g S ∘ coverSourceCenter d)
    (hg.continuous.comp hy) (hH.comp hy) (fun t ↦ hpos _)
    (metricGradient g S ∘ coverSourceCenter d) (hp.comp hy) hn d.triple
  exact ⟨d,hwd,cs,hcs,ce,hce,Ce,hCe,fun t ↦ ⟨hspan t,heta t⟩⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalWavesInDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem construct_local_compact_waves_in_domain {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hS : ContDiffOn ℝ ∞ S U)
    (hwp : ∀ x ∈ U, 0 < w x) (hp0 : ∀ x ∈ D, metricGradient g S x ≠ 0)
    (hdir : ∀ x ∈ D, ∃ v : _root_.OAI.Yau.Jets.Coord, g x (metricGradient g S x) v = 0 ∧ g x v v = 1 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x)+
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x v v)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ a : LocalCompactWaveData g w S D m J K k0, a.E ⊆ U := by
  obtain ⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hDE,hEU,hWp,he⟩ :=
    compact_source_representatives hD hU hDU hUn g hg hs hp w S hw hS hwp
  have hn (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ D) : metricGradient G A x ≠ 0 := by
    rw [(he x (hDE hx)).2.2.2.1]
    exact hp0 x hx
  have hd (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ D) : ∃ v : _root_.OAI.Yau.Jets.Coord,
      G x (metricGradient G A x) v = 0 ∧ G x v v = 1 ∧
      0 < sourceHessian G A x (metricGradient G A x) (metricGradient G A x)+
        (G x (metricGradient G A x) (metricGradient G A x)+4)*sourceHessian G A x v v := by
    obtain ⟨hge,_,_,hpEq,hHEq⟩ := he x (hDE hx)
    rw [hge.self_of_nhds,hpEq,hHEq]
    exact hdir x hx
  obtain ⟨d,⟨b⟩,_⟩ := construct_compact_source_waves G hG hGs hGp W hW A hA
    hD hE hDE hWp hn hd m J K k0 hm hJ
  have hest := local_source_wave_transfer g G w W S A
    (fun t : d.Parameter × Fin 3 ↦ coverSourceCenter d t.1)
    ((continuous_coverSourceCenter d).comp continuous_fst) hE
    (fun t ↦ hDE (d.center t.1).property)
    (fun x hx ↦ ⟨(he x hx).1,(he x hx).2.1,(he x hx).2.2.1.self_of_nhds⟩)
    (fun n t ↦ b.wave (n:ℝ) t) k0 K b.c b.Cw b.Cr b.R b.Cw_pos b.Cr_pos b.estimates
  refine ⟨⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hDE,
    (fun x hx ↦ ⟨(he x hx).1,(he x hx).2.1,(he x hx).2.2.1⟩),hn,d,b,hest⟩,hEU⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_PlacedEnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma PlacedEnvelopeData.closure_U_V {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.U ⊆ d.V :=
  d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans
    (subset_closure.trans d.patch_V)))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PlacedEnvelopeResidualWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

theorem PlacedEnvelopeData.waves_in_domain_oai {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) (ha : 0 ≤ a)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData g w d.S (closure d.U)
      (3*K'+4*k0+6) (K'+k0+1) K' k0, b.E ⊆ d.V := by
  have h0 : (0 : _root_.OAI.Yau.Jets.Coord) ∈ seedCoordCube a := by
    constructor <;> intro i <;> simp only [Pi.zero_apply] <;> linarith
  have h0U : (0 : _root_.OAI.Yau.Jets.Coord) ∈ d.U := d.C_U (d.inner_C (Or.inl h0))
  have h0V : (0 : _root_.OAI.Yau.Jets.Coord) ∈ d.V := d.closure_U_V (subset_closure h0U)
  apply construct_local_compact_waves_in_domain d.compact_closure_U d.open_V d.closure_U_V ⟨0,h0V⟩
    g (hg.mono d.V_branch) (fun x hx ↦ hs x (d.V_branch hx))
    (fun x hx ↦ hp x (d.V_branch hx)) w d.S (hw.mono d.V_branch)
    (d.smooth.mono d.V_branch) (fun x hx ↦ hwp x (d.V_branch hx))
    (fun x hx ↦ (d.admissible x (d.closure_U_V hx)).1)
  · intro x hx
    obtain ⟨hn,v,hv,hpv,hstr⟩ := d.admissible x (d.closure_U_V hx)
    exact ⟨v,hpv,hv,hstr⟩
  · omega
  · omega

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.PlacedEnvelopeData.waves_in_domain_oai := @OAI.Yau.Target.PlacedEnvelopeData.waves_in_domain_oai
