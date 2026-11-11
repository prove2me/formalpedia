-- Prove2me | solution 1 for OAI.Yau.Geometry.corrugation_actual_low_old_margin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:40.191122+00:00
-- url     : https://prove2.me/submissions/ea9cb642-57ac-41e2-aca2-7ab2028fe53c

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_corrugation_actual_low_gradient
import Theorems.Thm_OAI_Yau_Geometry_corrugation_projected_direction_freezing

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

lemma metricGradient_pair (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v) (v : _root_.OAI.Yau.Jets.Coord) :
    g y (metricGradient g S y) v = fderiv ℝ S y v := by
  have hi : ContinuousLinearMap.inverse (g y) = (positiveMetricEquiv (g y) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g y) hp)
  change positiveMetricEquiv (g y) hp (ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrozenFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma frozenFrameCovector_axis (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (i j : Fin 4) :
    frozenFrameCovector e i (e (Pi.single j 1)) = if i=j then 1 else 0 := by
  simp [frozenFrameCovector,Pi.single_apply]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrameBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma metric_unit_coordinate_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hg : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : g v v = 1) : ‖v‖ ≤ 1+c⁻¹ := by
  have h := hg v
  rw [hv] at h
  have hi := mul_inv_cancel₀ hc.ne'
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v,inv_pos.mpr hc]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAffineJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma affine_scalar_first (f : F → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (y x v : E) :
    fderiv ℝ (fun z ↦ f (L (z-y))) x v = fderiv ℝ f (L (x-y)) (L v) := by
  have h := (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).hasFDerivAt.comp x
    (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))
  simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] ℝ ↦ A v) h.fderiv

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDiskWell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set MeasureTheory
open scoped ContDiff
noncomputable section

lemma flatPrimitive_hasDerivAt (t : ℝ) : HasDerivAt flatPrimitive (expNegInvGlue t) t := by
  have hc := (expNegInvGlue.contDiff (n := ⊤)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma flatPrimitive_smooth : ContDiff ℝ ∞ flatPrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (flatPrimitive_hasDerivAt t).differentiableAt,?_⟩
  have he : deriv flatPrimitive = expNegInvGlue := funext (fun t ↦ (flatPrimitive_hasDerivAt t).deriv)
  rw [he]
  exact expNegInvGlue.contDiff

lemma flatPrimitive_zero {t : ℝ} (ht : t ≤ 0) : flatPrimitive t = 0 := by
  unfold flatPrimitive
  calc
    (∫ s in (0:ℝ)..t, expNegInvGlue s) = ∫ s in (0:ℝ)..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact expNegInvGlue.zero_of_nonpos hs.2
    _ = 0 := by simp

lemma corrugationDiskWell_smooth (a R : ℝ) : ContDiff ℝ ∞ (corrugationDiskWell a R) :=
  contDiff_const.mul (flatPrimitive_smooth.comp
    ((contDiff_const.sub (contDiff_fst.pow 2)).sub (contDiff_snd.pow 2)))

lemma corrugationDiskWell_zero {a R : ℝ} {z : ℝ × ℝ} (hz : R^2 ≤ z.1^2+z.2^2) :
    corrugationDiskWell a R z = 0 := by
  unfold corrugationDiskWell
  rw [flatPrimitive_zero (by linarith),mul_zero]

lemma corrugationDiskWell_compactSupport (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    HasCompactSupport (corrugationDiskWell a R) := by
  have hsub : Function.support (corrugationDiskWell a R) ⊆
      (Icc (-R) R) ×ˢ (Icc (-R) R) := by
    intro z hz
    have hn : z.1^2+z.2^2 < R^2 := by
      by_contra h
      exact hz (corrugationDiskWell_zero (le_of_not_gt h))
    constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_Icc.prod isClosed_Icc))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicWell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugation_translate_zero (a : ℝ) (N : ℕ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < (N:ℝ)-1) (hz₂ : |z.2| < (N:ℝ)-1)
    (k : ℤ × ℤ) (hk : k ∉ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ))) :
    corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ)) = 0 := by
  apply corrugationDiskWell_zero
  have hz1 := abs_lt.mp hz₁
  have hz2 := abs_lt.mp hz₂
  simp only [Finset.mem_Icc,Prod.le_def,not_and_or,not_le] at hk
  rcases hk with (hk | hk) | (hk | hk)
  all_goals
    have hk' := (Int.cast_lt (R := ℝ)).mpr hk
    push_cast at hk'
    dsimp only
    nlinarith [sq_nonneg (z.1-(k.1:ℝ)),sq_nonneg (z.2-(k.2:ℝ))]

lemma corrugationPeriodicWell_eq_sum (a : ℝ) (N : ℕ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < (N:ℝ)-1) (hz₂ : |z.2| < (N:ℝ)-1) :
    corrugationPeriodicWell a z =
      ∑ k ∈ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ)),
        corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ)) := by
  apply tsum_eq_sum
  intro k hk
  exact corrugation_translate_zero a N z hz₁ hz₂ k hk

lemma corrugationPeriodicWell_smooth (a : ℝ) : ContDiff ℝ ∞ (corrugationPeriodicWell a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt (max |z.1| |z.2|+1)
  have hz₁ : |z.1| < (N:ℝ)-1 := by have := le_max_left |z.1| |z.2|; linarith
  have hz₂ : |z.2| < (N:ℝ)-1 := by have := le_max_right |z.1| |z.2|; linarith
  have hsum : ContDiff ℝ ∞ (fun w : ℝ × ℝ ↦
      ∑ k ∈ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ)),
        corrugationDiskWell a (1/4) (w.1-(k.1:ℝ),w.2-(k.2:ℝ))) := by
    apply ContDiff.sum
    intro k _
    exact (corrugationDiskWell_smooth a (1/4)).comp
      ((contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.sub contDiff_const))
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < (N:ℝ)-1 :=
    (continuous_fst.abs.continuousAt).eventually_lt_const hz₁
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < (N:ℝ)-1 :=
    (continuous_snd.abs.continuousAt).eventually_lt_const hz₂
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_eq_sum a N w hw1 hw2

lemma corrugationPeriodicWell_periodic (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ) :
    corrugationPeriodicWell a (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) = corrugationPeriodicWell a z := by
  unfold corrugationPeriodicWell
  have h := (Equiv.addRight m).tsum_eq
    (fun k : ℤ × ℤ ↦ corrugationDiskWell a (1/4) (z.1+(m.1:ℝ)-(k.1:ℝ),z.2+(m.2:ℝ)-(k.2:ℝ)))
  simpa only [Equiv.coe_addRight,Prod.fst_add,Prod.snd_add,Int.cast_add,add_sub_add_right_eq_sub] using h.symm

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

lemma nonzero_integer_shift_square (x : ℝ) (hx : |x| ≤ 1/2) (k : ℤ) (hk : k ≠ 0) :
    (1/4:ℝ) ≤ (x-(k:ℝ))^2 := by
  have hx' := abs_le.mp hx
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hk1 : k ≤ -1 := by omega
    have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk1
    nlinarith

lemma corrugationPeriodicWell_cell (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
    corrugationPeriodicWell a z = corrugationDiskWell a (1/4) z := by
  unfold corrugationPeriodicWell
  rw [tsum_eq_single (0 : ℤ × ℤ)]
  · simp
  · intro k hk
    apply corrugationDiskWell_zero
    have h : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
      by_contra h
      simp only [not_or,not_not] at h
      exact hk (Prod.ext h.1 h.2)
    rcases h with h | h
    · have hs := nonzero_integer_shift_square z.1 hz₁ k.1 h
      dsimp only
      nlinarith [sq_nonneg (z.2-(k.2:ℝ))]
    · have hs := nonzero_integer_shift_square z.2 hz₂ k.2 h
      dsimp only
      nlinarith [sq_nonneg (z.1-(k.1:ℝ))]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalizedCorrugation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

lemma localizedCorrugation_smooth (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (localizedCorrugation χ f s J R a b y) :=
  (contDiff_const.mul (hχ.comp ((corrugationSlowMap R).contDiff.comp
    (contDiff_id.sub contDiff_const)))).mul
    (hf.comp ((corrugationFastMap J a b).contDiff.comp (contDiff_id.sub contDiff_const)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationScaledJetsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Yau.Jets
open scoped ContDiff

lemma localizedCorrugation_first (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (localizedCorrugation χ f s J R a b y) x v =
      (s/J) * (fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R v) *
        f (corrugationFastMap J a b (x-y)) +
        χ (corrugationSlowMap R (x-y)) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b v)) := by
  let A := corrugationSlowMap R
  let B := corrugationFastMap J a b
  have hA : ContDiff ℝ ∞ (fun z ↦ χ (A (z-y))) :=
    hχ.comp (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have hB : ContDiff ℝ ∞ (fun z ↦ f (B (z-y))) :=
    hf.comp (B.contDiff.comp (contDiff_id.sub contDiff_const))
  have he : localizedCorrugation χ f s J R a b y =
      (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) := by
    funext z; dsimp [localizedCorrugation,A,B] <;> ring
  rw [he]
  have hd := ((hA.differentiable (by simp) x).hasFDerivAt.mul
    (hB.differentiable (by simp) x).hasFDerivAt).const_mul (s/J)
  change HasFDerivAt (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply,add_apply,smul_eq_mul]
  rw [affine_scalar_first χ hχ,affine_scalar_first f hf]
  dsimp [A,B]
  ring

end

open Yau.Jets Set Filter
open scoped ContDiff Topology

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationMetricError
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma localizedCorrugation_first_scaled (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (localizedCorrugation χ f s J R a b y) x v =
      s*χ (R⁻¹ • (x-y))*fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v) +
      s/(J*R)*f (corrugationFastMap J a b (x-y))*fderiv ℝ χ (R⁻¹ • (x-y)) v := by
  rw [localizedCorrugation_first χ f hχ hf]
  simp only [corrugationSlowMap,corrugationFastMap,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  by_cases hR : R = 0
  · simp [hR]
    field_simp
  · field_simp
    ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJetContinuityLemmas
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

lemma metric_inverse_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (x : T) (hg : ContinuousAt g x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ ContinuousLinearMap.inverse (g y)) x := by
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g x) hp)).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g x) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact hc'.comp hg

lemma metric_connection_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (x : T) (hg : ContinuousAt g x) (hD : ContinuousAt D x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ metricConnection (g y) (D y)) x := by
  have hflip : ContinuousAt (fun t ↦ (D t).flip) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.continuousAt.comp hD
  have hcov : ContinuousAt (fun t ↦ christoffelCovector (D t)) x :=
    ((hD.add hflip).sub
      ((continuousAt_const (y := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).clm_comp hflip)).const_smul (1/2:ℝ)
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.continuousAt.comp
    (metric_inverse_continuousAt g x hg hp)).clm_comp hcov

lemma localMetricGradient_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContinuousAt g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricGradient g f) x :=
  (metric_inverse_continuousAt g x hg hp).clm_apply (hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma localMetricHessian_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContDiffAt ℝ ∞ g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricHessian g f) x := by
  have hD := hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).sub
    (((ContinuousLinearMap.compL ℝ E E ℝ).continuous.continuousAt.comp hD).clm_comp
      (metric_connection_continuousAt g (fderiv ℝ g) x hg.continuousAt
        (hg.continuousAt_fderiv (by simp)) hp))

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricCoercivity
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

lemma uniform_metric_coercivity (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hp : ∀ t v, v ≠ 0 → 0 < g t v v) :
    ∃ c > 0, ∃ B > 0, ∀ t, ‖g t‖ ≤ B ∧ ∀ v, c*‖v‖^2 ≤ g t v v := by
  have hc : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ g z.1 z.2 z.2) :=
    ((hg.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:_root_.OAI.Yau.Jets.Coord) 1)) _ hc.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  obtain ⟨B,hB,hBb⟩ := (isCompact_univ.image hg).isBounded.exists_pos_norm_le
  refine ⟨c,hc0,B,hB,?_⟩
  intro t
  refine ⟨hBb _ ⟨t,mem_univ _,rfl⟩,?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := (hbound (t,(‖v‖⁻¹:ℝ) • v)
    ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*g t v v)) = g t v v := by field_simp
  rw [he] at hmul
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactFreezing
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_convex_freezing (f : _root_.OAI.Yau.Jets.Coord → F) {D : Set _root_.OAI.Yau.Jets.Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D)
    (hdiff : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hder : ContinuousOn (fderiv ℝ f) D) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x-f y‖ ≤ C*‖x-y‖ := by
  obtain ⟨C,hC,hbound⟩ := (hD.image_of_continuousOn hder).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro x hx y hy
  exact hconv.norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun z hz ↦ hbound _ ⟨z,hz,rfl⟩) hy hx

lemma smooth_compact_freezing (f : _root_.OAI.Yau.Jets.Coord → F) {D U : Set _root_.OAI.Yau.Jets.Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x-f y‖ ≤ C*‖x-y‖ := by
  have hat : ∀ x ∈ D, ContDiffAt ℝ ∞ f x :=
    fun x hx ↦ hf.contDiffAt (hU.mem_nhds (hDU hx))
  apply compact_convex_freezing f hD hconv
  · exact fun x hx ↦ (hat x hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · intro x hx
    exact ((hat x hx).continuousAt_fderiv (by simp)).continuousWithinAt

lemma smooth_compact_covector_freezing (S : _root_.OAI.Yau.Jets.Coord → ℝ) {D U : Set _root_.OAI.Yau.Jets.Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ∀ v : _root_.OAI.Yau.Jets.Coord,
      |fderiv ℝ S x v-fderiv ℝ S y v| ≤ C*‖x-y‖*‖v‖ := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ S) U :=
    hS.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨C,hC,hb⟩ := smooth_compact_freezing (fderiv ℝ S) hD hconv hU hDU hd
  refine ⟨C,hC,?_⟩
  intro x hx y hy v
  exact ((fderiv ℝ S x-fderiv ℝ S y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb x hx y hy) (norm_nonneg v))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Metric
noncomputable section

lemma centered_integer_representative (x : ℝ) :
    |x-(⌊x+(1/2:ℝ)⌋:ℤ)| ≤ 1/2 := by
  have h1 := Int.floor_le (x+(1/2:ℝ))
  have h2 := Int.lt_floor_add_one (x+(1/2:ℝ))
  rw [abs_le]
  constructor <;> linarith

lemma corrugationPeriodicWell_representative (a : ℝ) (z : ℝ × ℝ) :
    ∃ w : ℝ × ℝ, |w.1| ≤ 1/2 ∧ |w.2| ≤ 1/2 ∧
      corrugationPeriodicWell a z = corrugationDiskWell a (1/4) w := by
  let m : ℤ × ℤ := (⌊z.1+(1/2:ℝ)⌋,⌊z.2+(1/2:ℝ)⌋)
  let w : ℝ × ℝ := (z.1-(m.1:ℝ),z.2-(m.2:ℝ))
  have h1 : |w.1| ≤ 1/2 := centered_integer_representative z.1
  have h2 : |w.2| ≤ 1/2 := centered_integer_representative z.2
  refine ⟨w,h1,h2,?_⟩
  have he : (w.1+(m.1:ℝ),w.2+(m.2:ℝ))=z := by dsimp [w] <;> simp
  rw [← corrugationPeriodicWell_cell a w h1 h2,← corrugationPeriodicWell_periodic a m w,he]

theorem corrugationPeriodicWell_bounded (a : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z, |corrugationPeriodicWell a z| ≤ B := by
  obtain ⟨B,hB⟩ := ((corrugationDiskWell_smooth a (1/4)).continuous.norm).bddAbove_range_of_hasCompactSupport
    ((corrugationDiskWell_compactSupport a (show (0:ℝ) ≤ 1/4 by norm_num)).norm)
  refine ⟨max B 0+1,by positivity,?_⟩
  intro z
  obtain ⟨w,_,_,hw⟩ := corrugationPeriodicWell_representative a z
  rw [hw]
  have hb := hB ⟨w,rfl⟩
  have hm := le_max_left B 0
  simpa only [Real.norm_eq_abs] using (hb.trans (by linarith : B ≤ max B 0+1))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDirectionEvaluations
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationLeadingVector_second_orthogonal (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) :
    g (corrugationLeadingVector amp t e z) (e (Pi.single 1 1)) = 0 := by
  simp [corrugationLeadingVector,corrugationFastVector,map_add,map_smul,he,Fin.ext_iff]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFirstAxis
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma compact_first_derivative_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ χ x‖ ≤ C := by
  have hcD : IsCompact (tsupport (fderiv ℝ χ)) :=
    hc.of_isClosed_subset isClosed_closure (tsupport_fderiv_subset ℝ (f := χ))
  have hcont : Continuous (fun x ↦ ‖fderiv ℝ χ x‖) := (hχ.continuous_fderiv (by simp)).norm
  obtain ⟨B,hB⟩ := (hcD.image hcont).bddAbove
  refine ⟨max B 0+1,by positivity,fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ χ)
  · exact (hB ⟨x,hx,rfl⟩).trans (by linarith [le_max_left B 0])
  · have hz : fderiv ℝ χ x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    rw [hz]
    simp only [ContinuousLinearMap.opNorm_zero]
    positivity

theorem corrugation_first_axis_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s J R : ℝ), 0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord), a v = 0 → b v = 0 →
      |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤
        s/(J*R)*C*‖v‖ := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hd⟩ := compact_first_derivative_bound χ hχ hc
  refine ⟨B*M,mul_pos hB hM,?_⟩
  intro s J R hs hJ hR a b y x v ha hb
  rw [localizedCorrugation_first_scaled χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ.ne']
  have hz : a.prod b v = 0 := by ext <;> assumption
  rw [hz,map_zero,mul_zero,zero_add,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hs (mul_pos hJ hR).le)]
  have hder : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ M*‖v‖ :=
    ((fderiv ℝ χ _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hd _) (norm_nonneg v))
  calc
    _ ≤ (s/(J*R)*B)*(M*‖v‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hf _) (by positivity)) hder (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma corrugated_first_axis_positive (S : _root_.OAI.Yau.Jets.Coord → ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (amp : ℝ)
    (s J R C A K : ℝ) (_hs : 0 < s) (hA : 0 ≤ A) (_hK : 0 ≤ K)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord)
    (hS : DifferentiableAt ℝ S x)
    (haxis : fderiv ℝ S y v = s)
    (hfreeze : |fderiv ℝ S x v-fderiv ℝ S y v| ≤ A*‖x-y‖*‖v‖)
    (hxy : ‖x-y‖ ≤ R) (hv : ‖v‖ ≤ K)
    (herr : |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤
      s/(J*R)*C*‖v‖)
    (hcoef : 0 ≤ s/(J*R)*C)
    (hsmall₁ : A*R*K ≤ s/4) (hsmall₂ : s/(J*R)*C*K ≤ s/4) :
    s/2 ≤ fderiv ℝ (fun z ↦ S z+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y z) x v := by
  have hw := (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) s J R a b y).differentiable (by simp)
  change s/2 ≤ fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v
  rw [fderiv_add hS hw.differentiableAt,add_apply]
  have hR : 0 ≤ R := (norm_nonneg (x-y)).trans hxy
  have hfreeze' : |fderiv ℝ S x v-s| ≤ s/4 := by
    rw [haxis] at hfreeze
    apply hfreeze.trans
    calc
      A*‖x-y‖*‖v‖ ≤ A*R*K := mul_le_mul (mul_le_mul_of_nonneg_left hxy hA) hv (norm_nonneg _) (by positivity)
      _ ≤ _ := hsmall₁
  have herr' : |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤ s/4 :=
    herr.trans ((mul_le_mul_of_nonneg_left hv hcoef).trans hsmall₂)
  have h1 := (abs_le.mp hfreeze').1
  have h2 := (abs_le.mp herr').1
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFrequencyScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Real
open scoped Topology
noncomputable section

lemma corrugationScale_formula (L : ℝ) (k : ℕ) :
    corrugationScale L k = L/((k:ℝ)+1)^2 := by
  simp [corrugationScale,corrugationSubdivision]

lemma corrugationFrequency_positive (k : ℕ) : 0 < corrugationFrequency k := by
  unfold corrugationFrequency
  positivity

lemma corrugationScale_positive {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < corrugationScale L k := by
  rw [corrugationScale_formula]
  positivity

lemma corrugationFrequency_eighth (k : ℕ) :
    (corrugationFrequency k)^((1:ℝ)/8) = (k:ℝ)+1 := by
  rw [corrugationFrequency,← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
  norm_num

lemma corrugation_scale_rate_identities {L : ℝ} (hL : L ≠ 0) (k : ℕ) :
    (corrugationScale L k)^2*(corrugationFrequency k)^((1:ℝ)/8) = L^2/((k:ℝ)+1)^3 ∧
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ = (L^2)⁻¹/((k:ℝ)+1)^4 ∧
    (corrugationFrequency k*corrugationScale L k)⁻¹ = L⁻¹/((k:ℝ)+1)^6 ∧
    corrugationFrequency k*corrugationScale L k = L*((k:ℝ)+1)^6 := by
  rw [corrugationFrequency_eighth,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

lemma corrugation_power_reciprocal_tendsto (C : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun k : ℕ ↦ C/((k:ℝ)+1)^p) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hp' := (tendsto_pow_atTop hp).comp hk
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def,Pi.inv_apply] using hp'.inv_tendsto_atTop.const_mul C

lemma corrugationScale_tendsto (L : ℝ) :
    Tendsto (corrugationScale L) atTop (𝓝 0) := by
  change Tendsto (fun k ↦ corrugationScale L k) atTop (𝓝 0)
  simp_rw [corrugationScale_formula]
  exact corrugation_power_reciprocal_tendsto L (by norm_num)

lemma corrugation_frequency_scale_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun k ↦ corrugationFrequency k*corrugationScale L k) atTop atTop := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simp_rw [(corrugation_scale_rate_identities hL.ne' _).2.2.2]
  exact ((tendsto_pow_atTop (by norm_num : (6:ℕ) ≠ 0)).comp hk).const_mul_atTop hL

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationOldData
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma corrugationOldSlope_positive (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : metricGradient g S y ≠ 0) : 0 < corrugationOldSlope g S y :=
  Real.sqrt_pos.mpr (hp _ hn)

lemma corrugationOldSlope_continuousOn (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ContinuousOn (corrugationOldSlope g S) U := by
  intro y hy
  have hg' := hg.contDiffAt (hU.mem_nhds hy)
  have hS' := hS.contDiffAt (hU.mem_nhds hy)
  have hgrad : ContinuousAt (metricGradient g S) y :=
    localMetricGradient_continuousAt g S y hg'.continuousAt hS' (hp y hy)
  exact (Real.continuous_sqrt.continuousAt.comp
    ((hg'.continuousAt.clm_apply hgrad).clm_apply hgrad)).continuousWithinAt

lemma corrugationOldSlope_compact_bounds
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∃ B : ℝ, 0 < B ∧
      ∀ y ∈ D, m ≤ corrugationOldSlope g S y ∧ corrugationOldSlope g S y ≤ B := by
  exact compact_positive_bounds hD _
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU)
    (fun y hy ↦ corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy))

lemma compact_metric_comparison (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {D : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hg : ContinuousOn g D)
    (hp : ∀ y ∈ D, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ D, ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  obtain ⟨c,hc,M,hM,hb⟩ := uniform_metric_coercivity (fun y : D ↦ g y)
    hg.domRestrict (fun y v hv ↦ hp y y.property v hv)
  exact ⟨c,hc,M,hM,fun y hy ↦ hb ⟨y,hy⟩⟩

lemma corrugation_frozen_axis_differential
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (y : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g y v v) (hn : metricGradient g S y ≠ 0)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y) :
    fderiv ℝ S y (e (Pi.single 0 1)) = corrugationOldSlope g S y := by
  have hs := corrugationOldSlope_positive g S y hp hn
  have hsq : (corrugationOldSlope g S y)^2 = g y (metricGradient g S y) (metricGradient g S y) :=
    Real.sq_sqrt (hp _ hn).le
  rw [← metricGradient_pair g S y hp,he,map_smul,smul_eq_mul,← hsq]
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNormalizedGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugationGradientRate_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (corrugationGradientRate L) atTop (𝓝 0) := by
  change Tendsto (fun k ↦ corrugationScale L k+1/(corrugationFrequency k*corrugationScale L k)) atTop (𝓝 0)
  simpa only [one_div,add_zero,Pi.inv_apply] using (corrugationScale_tendsto L).add
    (corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNonvanishing
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

theorem corrugation_local_nonvanishing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (amp : ℝ) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, ∀ y ∈ D, ∀ x ∈ D,
      ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x ≠ 0 := by
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨A,hA,hfreeze⟩ := smooth_compact_covector_freezing S hD hconv hU hDU hS
  obtain ⟨C,hC,hfirst⟩ := corrugation_first_axis_bound χ hχ hc amp
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K] <;> positivity
  have ht1 : Tendsto (fun k ↦ A*corrugationScale L k*K) atTop (𝓝 0) := by
    simpa using ((corrugationScale_tendsto L).const_mul A).mul_const K
  have ht2 : Tendsto (fun k ↦ C/(corrugationFrequency k*corrugationScale L k)*K) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (((corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop).const_mul C).mul_const K
  have he1 := ht1.eventually_lt_const (show (0:ℝ) < m/4 by positivity)
  have he2 := ht2.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num)
  filter_upwards [he1,he2] with k hk1 hk2
  intro y hy x hx hxy e he0 he
  let v : _root_.OAI.Yau.Jets.Coord := e (Pi.single 0 1)
  let s : ℝ := corrugationOldSlope g S y
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hv : ‖v‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 v (by simpa [v] using he 0 0)
  have ha : frozenFrameCovector e 2 v = 0 := by dsimp [v]; rw [frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  have hb : frozenFrameCovector e 3 v = 0 := by dsimp [v]; rw [frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have herr := hfirst s (corrugationFrequency k) (corrugationScale L k) hs.le hJ hR _ _ y x v ha hb
  have hsmall1 : A*corrugationScale L k*K ≤ s/4 := by
    have hm' := (hslope y hy).1
    dsimp [s]
    linarith
  have hsmall2 : s/(corrugationFrequency k*corrugationScale L k)*C*K ≤ s/4 := by
    have hh := mul_le_mul_of_nonneg_left hk2.le hs.le
    calc
      _ = s*(C/(corrugationFrequency k*corrugationScale L k)*K) := by ring
      _ ≤ s*(1/4) := hh
      _ = s/4 := by ring
  have hpos := corrugated_first_axis_positive S χ hχ amp s (corrugationFrequency k)
    (corrugationScale L k) C A K hs hA.le hK.le _ _ y x v
    ((hS.contDiffAt (hU.mem_nhds (hDU hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (corrugation_frozen_axis_differential g S y (hp y (hDU hy)) (hn y hy) e he0)
    (hfreeze x hx y hy v) hxy hv herr (by positivity) hsmall1 hsmall2
  intro hz
  have hpair := metricGradient_pair g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y)
    x (hp x (hDU hx)) v
  rw [hz,map_zero,zero_apply] at hpair
  change s/2 ≤ fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v at hpos
  rw [← hpair] at hpos
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationStrictMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma maximizing_margin_from_eta (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p q v : _root_.OAI.Yau.Jets.Coord) (hp : 0 < g p p) (hq : g q q = g p p+4) (hpq : g p q = 0)
    {c : ℝ} (hc : 0 < c) (heta : c ≤ sourceDirectionEta g H p q)
    (hmax : ∀ u, g u u = 1 → g p u = 0 → H u u ≤ H v v) :
    c ≤ H p p/(g p p+4)+H v v := by
  have hqpos : 0 < g q q := by linarith
  have hd : 0 < g p p+g q q := by linarith
  have he := (le_div_iff₀ hd).mp heta
  have hmax' := hmax (metricNormalize g q) (metricNormalize_unit g q hqpos)
    (metricNormalize_orthogonal g p q hpq)
  have hsqrt := Real.sq_sqrt hqpos.le
  have hsqrt0 : Real.sqrt (g q q) ≠ 0 := (Real.sqrt_pos.mpr hqpos).ne'
  have hscale : (g q q)*H (metricNormalize g q) (metricNormalize g q) = H q q := by
    simp only [metricNormalize,map_smul,smul_apply,smul_eq_mul]
    field_simp
    rw [hsqrt]
  have hineq := mul_le_mul_of_nonneg_left hmax' hqpos.le
  rw [hscale,hq] at hineq
  rw [hq] at he
  have hden : 0 < g p p+4 := by linarith
  have hmain : c*(g p p+4) ≤ H p p+(g p p+4)*H v v := by nlinarith
  calc
    c ≤ (H p p+(g p p+4)*H v v)/(g p p+4) := (le_div_iff₀ hden).mpr hmain
    _ = H p p/(g p p+4)+H v v := by field_simp

theorem compact_maximizing_margin {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hsym : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (hdir : ∀ t, ∃ v, g t (p t) v = 0 ∧ g t v v = 1 ∧
      0 < H t (p t) (p t)+(g t (p t) (p t)+4)*H t v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ t v,
      (∀ u, g t u u = 1 → g t (p t) u = 0 → H t u u ≤ H t v v) →
      c ≤ H t (p t) (p t)/(g t (p t) (p t)+4)+H t v v := by
  obtain ⟨d⟩ := exists_compact_frame_cover g H hg hH hsym hpos p hp hp0 hdir
  obtain ⟨c,hc,C,hC,hbound⟩ := uniform_direction_strictness (g ∘ d.center) (H ∘ d.center)
    (hg.comp d.continuous_center) (hH.comp d.continuous_center) (fun z ↦ hpos (d.center z))
    (p ∘ d.center) (hp.comp d.continuous_center) (fun z ↦ hp0 (d.center z)) d.triple
  refine ⟨c,hc,?_⟩
  intro t v hmax
  obtain ⟨z,hz⟩ := d.surjective_center t
  have h := maximizing_margin_from_eta (g (d.center z)) (H (d.center z))
    (p (d.center z)) (d.triple.q z 0) v (hpos _ _ (hp0 _)) (d.triple.length z 0)
    (d.triple.perpendicular z 0) hc (hbound z 0).1 (by simpa [hz] using hmax)
  simpa [hz] using h

theorem corrugation_old_uniform_margin
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ D, ∀ v,
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y v v) →
      c ≤ sourceHessian g S y (metricGradient g S y) (metricGradient g S y)/
        (g y (metricGradient g S y) (metricGradient g S y)+4)+sourceHessian g S y v v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hcP : ContinuousOn (metricGradient g S) D := by
    intro y hy
    exact (localMetricGradient_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))).continuousAt
      (hS.contDiffAt (hU.mem_nhds (hDU hy))) (hp y (hDU hy))).continuousWithinAt
  have hcH : ContinuousOn (sourceHessian g S) D := by
    intro y hy
    exact (localMetricHessian_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))) (hS.contDiffAt (hU.mem_nhds (hDU hy)))
      (hp y (hDU hy))).continuousWithinAt
  obtain ⟨c,hc,hbound⟩ := compact_maximizing_margin (fun y : D ↦ g y) (fun y : D ↦ sourceHessian g S y)
    (hg.continuousOn.mono hDU).domRestrict hcH.domRestrict (fun y ↦ hsym y y.property)
    (fun y ↦ hp y (hDU y.property)) (fun y : D ↦ metricGradient g S y) hcP.domRestrict
    (fun y ↦ (hadm y y.property).1) (fun y ↦ by
      obtain ⟨q,hq,hpq,hstr⟩ := (hadm y y.property).2
      exact ⟨q,hpq,hq,hstr⟩)
  exact ⟨c,hc,fun y hy ↦ hbound ⟨y,hy⟩⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedHessianStability
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma weightedHessianValue_normalized (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p t : _root_.OAI.Yau.Jets.Coord) (hp : 0 < g p p) :
    weightedHessianValue g H p t =
      (g p p/(g p p+4))*H (metricNormalize g p) (metricNormalize g p)+H t t := by
  have hs := Real.sq_sqrt hp.le
  have hs0 := (Real.sqrt_pos.mpr hp).ne'
  have hd : g p p+4 ≠ 0 := by positivity
  unfold weightedHessianValue metricNormalize
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp
  rw [hs]
  ring

theorem weightedHessianValue_uniform_continuity
    (g H : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {D : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hg : ContinuousOn g D) (hH : ContinuousOn H D)
    (hp : ∀ x ∈ D, ∀ v, 0 ≤ g x v v) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ D, ∀ y ∈ D, ∀ p q t u : _root_.OAI.Yau.Jets.Coord,
      ‖p‖ ≤ K → ‖q‖ ≤ K → ‖t‖ ≤ K → ‖u‖ ≤ K →
      ‖x-y‖ < δ → ‖p-q‖ < δ → ‖t-u‖ < δ →
      |weightedHessianValue (g x) (H x) p t-weightedHessianValue (g y) (H y) q u| < ε := by
  let E : Set (_root_.OAI.Yau.Jets.Coord × (_root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord)) := D ×ˢ (Metric.closedBall 0 K ×ˢ Metric.closedBall 0 K)
  have hE : IsCompact E := hD.prod ((isCompact_closedBall 0 K).prod (isCompact_closedBall 0 K))
  let F : _root_.OAI.Yau.Jets.Coord × (_root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord) → ℝ := fun z ↦ weightedHessianValue (g z.1) (H z.1) z.2.1 z.2.2
  have hgc : ContinuousOn (fun z : _root_.OAI.Yau.Jets.Coord × (_root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord) ↦ g z.1) E :=
    hg.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)
  have hHc : ContinuousOn (fun z : _root_.OAI.Yau.Jets.Coord × (_root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord) ↦ H z.1) E :=
    hH.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)
  have hpc : ContinuousOn (fun z : _root_.OAI.Yau.Jets.Coord × (_root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord) ↦ z.2.1) E :=
    (continuous_fst.comp continuous_snd).continuousOn
  have htc : ContinuousOn (fun z : _root_.OAI.Yau.Jets.Coord × (_root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord) ↦ z.2.2) E :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hF : ContinuousOn F E := by
    apply ContinuousOn.add
    · exact ((hHc.clm_apply hpc).clm_apply hpc).div
        (((hgc.clm_apply hpc).clm_apply hpc).add continuousOn_const)
        (fun z hz ↦ by have h := hp z.1 hz.1 z.2.1; positivity)
    · exact (hHc.clm_apply htc).clm_apply htc
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp (hE.uniformContinuousOn_of_continuous hF) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy p q t u hpb hqb htb hub hxy hpq htu
  have hxE : (x,(p,t)) ∈ E := ⟨hx,by simpa using hpb,by simpa using htb⟩
  have hyE : (y,(q,u)) ∈ E := ⟨hy,by simpa using hqb,by simpa using hub⟩
  have hdxy : dist (x,(p,t)) (y,(q,u)) < δ := by
    change max (dist x y) (max (dist p q) (dist t u)) < δ
    simpa only [max_lt_iff,dist_eq_norm] using And.intro hxy (And.intro hpq htu)
  have hr := hd (x,(p,t)) hxE (y,(q,u)) hyE hdxy
  simpa only [Real.dist_eq,F] using hr

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLowOldMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_old_margin_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let q := metricPerpProjection (g x) (metricNormalize (g x) p) (e (Pi.single 1 1))
      let t := metricNormalize (g x) q
      corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ T →
      q ≠ 0 ∧ g x t t = 1 ∧ g x (metricNormalize (g x) p) t = 0 ∧
        c ≤ (g x p p/(g x p p+4))*sourceHessian g S x (metricNormalize (g x) p)
          (metricNormalize (g x) p)+sourceHessian g S x t t := by
  have hn : ∀ y ∈ D, metricGradient g S y ≠ 0 := fun y hy ↦ (hadm y hy).1
  obtain ⟨c,hc,hmargin⟩ := corrugation_old_uniform_margin g S hD hU hDU hg hS hp hsym hadm
  obtain ⟨a,ha0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  have hcP : ContinuousOn (metricGradient g S) D := by
    intro y hy
    exact (localMetricGradient_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))).continuousAt
      (hS.contDiffAt (hU.mem_nhds (hDU hy))) (hp y (hDU hy))).continuousWithinAt
  have hcH : ContinuousOn (sourceHessian g S) D := by
    intro y hy
    exact (localMetricHessian_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))) (hS.contDiffAt (hU.mem_nhds (hDU hy)))
      (hp y (hDU hy))).continuousWithinAt
  obtain ⟨G,hG,hGB⟩ := (hD.image_of_continuousOn hcP).isBounded.exists_pos_norm_le
  have hgp : ∀ y ∈ D, ‖metricGradient g S y‖ ≤ G := fun y hy ↦ hGB _ ⟨y,hy,rfl⟩
  let K : ℝ := G+1+(1+a⁻¹)
  have hKp : G+1 ≤ K := by
    have hi : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
    dsimp [K] <;> linarith
  have hKt : 1+a⁻¹ ≤ K := by dsimp [K] <;> linarith
  have hg0 : ∀ x ∈ D, ∀ v, 0 ≤ g x v v := by
    intro x hx v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp x (hDU hx) v hv).le
  obtain ⟨δ,hδ,hstable⟩ := weightedHessianValue_uniform_continuity g (sourceHessian g S) hD
    (hg.continuousOn.mono hDU) hcH hg0 K (half_pos hc)
  refine ⟨c/2,half_pos hc,?_⟩
  intro T
  obtain ⟨A,hA,hgrad⟩ := corrugation_actual_low_gradient g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 ha ha1 hL T
  obtain ⟨B,hB,hproj⟩ := corrugation_projected_direction_freezing g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 ha ha1 hL
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hcpt amp hL
  have htA : Tendsto (fun k ↦ A*corrugationScale L k) atTop (𝓝 0) := by
    simpa using (corrugationScale_tendsto L).const_mul A
  have htB : Tendsto (fun k ↦ B*corrugationGradientRate L k) atTop (𝓝 0) := by
    simpa using (corrugationGradientRate_tendsto hL).const_mul B
  filter_upwards [hgrad,hproj,hnv,(corrugationScale_tendsto L).eventually_lt_const hδ,
    htA.eventually_lt_const hδ,htA.eventually_lt_const zero_lt_one,
    htB.eventually_lt_const hδ] with k hkgrad hkproj hknv hkR hkA hkA1 hkB
  intro y hy x hx hxy e he0 he hmax
  dsimp only
  intro hreg
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let u := e (Pi.single 1 1)
  let q := metricPerpProjection (g x) (metricNormalize (g x) p) u
  let t := metricNormalize (g x) q
  have hu : g y u u = 1 := by simpa [u] using he 1 1
  obtain ⟨hnq,htunit,htorth,htclose⟩ := hkproj y hy x hx hxy e he0 he u hu
    (corrugationLeadingVector_second_orthogonal (g y) e he amp _ _)
  have hd : ‖p-metricGradient g S y‖ ≤ A*corrugationScale L k := hkgrad y hy x hx hxy e he0 he hreg
  have hpbound : ‖p‖ ≤ K := by
    have htri : ‖p‖ ≤ ‖p-metricGradient g S y‖+‖metricGradient g S y‖ :=
      norm_le_norm_sub_add _ _
    exact (htri.trans (add_le_add (hd.trans hkA1.le) (hgp y hy))).trans (by linarith)
  have htbound : ‖t‖ ≤ K := (metric_unit_coordinate_bound (g x) ha0 (hmetric x hx).2 t htunit).trans hKt
  have hubound : ‖u‖ ≤ K := (metric_unit_coordinate_bound (g y) ha0 (hmetric y hy).2 u hu).trans hKt
  have hdiff := hstable x hx y hy p (metricGradient g S y) t u hpbound
    ((hgp y hy).trans (by linarith)) htbound hubound (hxy.trans_lt hkR)
    (hd.trans_lt hkA) (htclose.trans_lt hkB)
  have hold : c ≤ weightedHessianValue (g y) (sourceHessian g S y) (metricGradient g S y) u :=
    hmargin y hy u hmax
  have hnew : c/2 ≤ weightedHessianValue (g x) (sourceHessian g S x) p t := by
    have hh := (abs_lt.mp hdiff).1
    linarith
  rw [weightedHessianValue_normalized (g x) (sourceHessian g S x) p t
    (hp x (hDU hx) p (hknv y hy x hx hxy e he0 he))] at hnew
  exact ⟨hnq,htunit,htorth,hnew⟩

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.corrugation_actual_low_old_margin_oai := @OAI.Yau.Geometry.corrugation_actual_low_old_margin_oai
