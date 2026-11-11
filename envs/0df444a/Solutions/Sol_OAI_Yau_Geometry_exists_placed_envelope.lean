-- Prove2me | solution 1 for OAI.Yau.Geometry.exists_placed_envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:29:13.001273+00:00
-- url     : https://prove2.me/submissions/23e6ca8a-e8fa-4565-9424-caff914fbcf6

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Theorems.Thm_OAI_Yau_Geometry_corrugation_grid_admissibility
import Theorems.Thm_OAI_Yau_Geometry_corrugation_grid_integrated_gain

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

variable {T : Type*} [TopologicalSpace T]
lemma metricNormalize_continuousAt (g : T → E →L[ℝ] E →L[ℝ] ℝ) (v : T → E) {t : T}
    (hg : ContinuousAt g t) (hv : ContinuousAt v t) (hpos : 0 < g t (v t) (v t)) :
    ContinuousAt (fun s ↦ metricNormalize (g s) (v s)) t := by
  exact (((hg.clm_apply hv).clm_apply hv).sqrt.inv₀
    (ne_of_gt (Real.sqrt_pos.mpr hpos))).smul hv

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

lemma sourceHessian_apply (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y u v : _root_.OAI.Yau.Jets.Coord) : sourceHessian g S y u v =
      fderiv ℝ (fderiv ℝ S) y u v - fderiv ℝ S y (metricConnection (g y) (fderiv ℝ g y) u v) := rfl

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

lemma metric_perpendicular_unit_compact
    (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) :
    IsCompact {v : _root_.OAI.Yau.Jets.Coord | g v v = 1 ∧ g p v = 0} := by
  obtain ⟨c,hc,hbound⟩ := positive_bilinear_coercive g hp
  have hclosed : IsClosed {v : _root_.OAI.Yau.Jets.Coord | g v v = 1 ∧ g p v = 0} :=
    (isClosed_eq (g.continuous.clm_apply continuous_id) continuous_const).inter
      (isClosed_eq (g p).continuous continuous_const)
  apply (isCompact_closedBall (0:_root_.OAI.Yau.Jets.Coord) (1+c⁻¹)).of_isClosed_subset hclosed
  intro v hv
  rw [mem_closedBall,dist_zero_right]
  have hb := hbound v
  rw [hv.1] at hb
  have hi : c*c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v,inv_pos.mpr hc]

lemma exists_maximizing_perpendicular_axis
    (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g v v) (p q₀ : _root_.OAI.Yau.Jets.Coord)
    (hq₀ : g q₀ q₀ = 1) (hpq₀ : g p q₀ = 0) :
    ∃ q : _root_.OAI.Yau.Jets.Coord, g q q = 1 ∧ g p q = 0 ∧
      ∀ v : _root_.OAI.Yau.Jets.Coord, g v v = 1 → g p v = 0 → H v v ≤ H q q := by
  obtain ⟨q,hq,hmax⟩ := (metric_perpendicular_unit_compact g hp p).exists_isMaxOn
    ⟨q₀,hq₀,hpq₀⟩ (H.continuous.clm_apply continuous_id).continuousOn
  exact ⟨q,hq.1,hq.2,fun v hv hvp ↦ hmax ⟨hv,hvp⟩⟩

lemma frozenFrameCovector_axis (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (i j : Fin 4) :
    frozenFrameCovector e i (e (Pi.single j 1)) = if i=j then 1 else 0 := by
  simp [frozenFrameCovector,Pi.single_apply]

theorem exists_corrugation_frozen_frame
    (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (p q₀ : _root_.OAI.Yau.Jets.Coord) (hp₀ : p ≠ 0) (hq₀ : g q₀ q₀ = 1) (hpq₀ : g p q₀ = 0) :
    ∃ (q : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord),
      g q q = 1 ∧ g p q = 0 ∧
      (∀ v : _root_.OAI.Yau.Jets.Coord, g v v = 1 → g p v = 0 → H v v ≤ H q q) ∧
      e (Pi.single 0 1) = (Real.sqrt (g p p))⁻¹ • p ∧
      e (Pi.single 1 1) = q ∧
      (∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) ∧
      frozenFrameCovector e 2 p = 0 ∧ frozenFrameCovector e 3 p = 0 ∧
      frozenFrameCovector e 2 q = 0 ∧ frozenFrameCovector e 3 q = 0 := by
  obtain ⟨q,hqq,hpq,hm⟩ := exists_maximizing_perpendicular_axis g H hp p q₀ hq₀ hpq₀
  have hp' := hp p hp₀
  obtain ⟨e,he0,he1,he⟩ := positive_coordinate_adapted_frame g hp hs p q
    (Real.sqrt (g p p)) 1 (Real.sqrt_pos.mpr hp') (by norm_num)
    (Real.sq_sqrt hp'.le).symm (by simpa using hqq) hpq
  have he1' : e (Pi.single 1 1) = q := by simpa using he1
  have hep : p = Real.sqrt (g p p) • e (Pi.single 0 1) := by
    rw [he0,smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hp').ne',one_smul]
  refine ⟨q,e,hqq,hpq,hm,he0,he1',he,?_,?_,?_,?_⟩
  · rw [hep,map_smul,frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  · rw [hep,map_smul,frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  · rw [← he1',frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  · rw [← he1',frozenFrameCovector_axis]; norm_num [Fin.ext_iff]

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

lemma scalar_product_second (f k : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hk : ContDiff ℝ ∞ k) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f z*k z)) x u v =
      fderiv ℝ (fderiv ℝ f) x u v*k x +
      fderiv ℝ f x v*fderiv ℝ k x u +
      fderiv ℝ f x u*fderiv ℝ k x v +
      f x*fderiv ℝ (fderiv ℝ k) x u v := by
  have hd := (((hf.mul hk).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  have he := congrArg (fun A : E →L[ℝ] ℝ ↦ A u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he]
  have hfun : (fun z ↦ fderiv ℝ (fun w ↦ f w*k w) z v) =
      (fun z ↦ fderiv ℝ f z v*k z+f z*fderiv ℝ k z v) := by
    funext z
    change fderiv ℝ (f*k) z v = _
    rw [fderiv_mul (hf.differentiable (by simp) z) (hk.differentiable (by simp) z)]
    simp
    ring
  rw [hfun]
  have df := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x))
  have dk := (((hk.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x))
  change fderiv ℝ ((fun z ↦ fderiv ℝ f z v)*k+f*(fun z ↦ fderiv ℝ k z v)) x u = _
  rw [((df.mul (hk.differentiable (by simp) x).hasFDerivAt).add
    ((hf.differentiable (by simp) x).hasFDerivAt.mul dk)).fderiv]
  simp
  ring

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

lemma localizedCorrugation_support (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J : ℝ) {R : ℝ} (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    tsupport (localizedCorrugation χ f s J R a b y) ⊆
      (fun x ↦ R⁻¹ • (x-y)) ⁻¹' tsupport χ := by
  apply closure_minimal
  · intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [localizedCorrugation,corrugationSlowMap,hz])
  · exact (isClosed_closure : IsClosed (tsupport χ)).preimage ((continuous_const : Continuous (fun _ : _root_.OAI.Yau.Jets.Coord ↦ R⁻¹)).smul (continuous_id.sub continuous_const))

lemma localizedCorrugation_cube (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (s J : ℝ) {R : ℝ} (hR : 0 < R) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    tsupport (localizedCorrugation χ f s J R a b y) ⊆ ball y (R/2) := by
  intro x hx
  have hz := hχ (localizedCorrugation_support χ f s J a b y hx)
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hz
  rw [mem_ball,dist_eq_norm]
  have hr : R*R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  nlinarith [mul_lt_mul_of_pos_left hz hR]

lemma localizedCorrugation_compact (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (s J : ℝ) {R : ℝ} (hR : 0 < R) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    HasCompactSupport (localizedCorrugation χ f s J R a b y) :=
  (isCompact_closedBall y (R/2)).of_isClosed_subset isClosed_closure
    ((localizedCorrugation_cube χ f hχ s J hR a b y).trans ball_subset_closedBall)

lemma localizedCorrugation_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ∀ z, |χ z| ≤ 1) {B : ℝ} (hf : ∀ z, |f z| ≤ B)
    {s J : ℝ} (hs : 0 ≤ s) (hJ : 0 < J) (R : ℝ)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x : _root_.OAI.Yau.Jets.Coord) :
    |localizedCorrugation χ f s J R a b y x| ≤ (s/J)*B := by
  have hn : 0 ≤ s/J := div_nonneg hs hJ.le
  rw [localizedCorrugation,abs_mul,abs_mul,abs_of_nonneg hn]
  calc
    s/J*|χ _| *|f _| ≤ s/J*1*|f _| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχ _) hn) (abs_nonneg _)
    _ ≤ (s/J)*B := by simpa using mul_le_mul_of_nonneg_left (hf _) hn

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

lemma scalar_const_mul_second (c : ℝ) (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fderiv ℝ (fun z ↦ c*f z)) x u v = c*fderiv ℝ (fderiv ℝ f) x u v := by
  simpa using scalar_product_second (fun _ ↦ c) f contDiff_const hf x u v

end

open Yau.Jets Set Filter
open scoped ContDiff Topology
variable {ι : Type*}

lemma finite_sum_compact_support (I : Finset ι) (w : ι → _root_.OAI.Yau.Jets.Coord → ℝ)
    (hw : ∀ i ∈ I, HasCompactSupport (w i)) :
    HasCompactSupport (fun x ↦ ∑ i ∈ I, w i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change HasCompactSupport (0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    exact HasCompactSupport.zero
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    change HasCompactSupport (w i + fun x ↦ ∑ j ∈ I, w j x)
    exact (hw i (Finset.mem_insert_self i I)).add (ih (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)))

lemma finite_sum_support_subset (I : Finset ι) (w : ι → _root_.OAI.Yau.Jets.Coord → ℝ) (U : Set _root_.OAI.Yau.Jets.Coord)
    (hw : ∀ i ∈ I, tsupport (w i) ⊆ U) :
    tsupport (fun x ↦ ∑ i ∈ I, w i x) ⊆ U := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (tsupport_add _ _).trans (union_subset
      (hw i (Finset.mem_insert_self i I)) (ih (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))))

lemma finite_disjoint_sum_eventually (I : Finset ι) (w : ι → _root_.OAI.Yau.Jets.Coord → ℝ)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)))
    {i : ι} (hi : i ∈ I) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ tsupport (w i)) :
    (fun z ↦ ∑ j ∈ I, w j z) =ᶠ[𝓝 x] w i := by
  classical
  have hz : ∀ j ∈ I, j ≠ i → w j =ᶠ[𝓝 x] 0 := by
    intro j hj hji
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun hjx ↦ Set.disjoint_left.mp (hd i hi j hj hji.symm) hx hjx
  have he : ∀ᶠ z in 𝓝 x, ∀ j ∈ I, j ≠ i → w j z = 0 := by
    apply (eventually_all_finite I.finite_toSet).mpr
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · filter_upwards [hz j hj hji] with z hz
      exact fun _ ↦ hz
  filter_upwards [he] with z hz
  exact Finset.sum_eq_single i hz (fun h ↦ (h hi).elim)

lemma finite_disjoint_sum_bound (I : Finset ι) (w : ι → _root_.OAI.Yau.Jets.Coord → ℝ)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)))
    {B : ℝ} (hB : 0 ≤ B) (hw : ∀ i ∈ I, ∀ x, |w i x| ≤ B) (x : _root_.OAI.Yau.Jets.Coord) :
    |∑ i ∈ I, w i x| ≤ B := by
  classical
  by_cases hx : ∃ i ∈ I, x ∈ tsupport (w i)
  · obtain ⟨i,hi,hxi⟩ := hx
    rw [(finite_disjoint_sum_eventually I w hd hi hxi).eq_of_nhds]
    exact hw i hi x
  · have hz : ∀ i ∈ I, w i x = 0 := by
      intro i hi
      by_contra h
      exact hx ⟨i,hi,subset_tsupport _ h⟩
    rw [Finset.sum_eq_zero hz,abs_zero]
    exact hB

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAssembly
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {ι : Type*}

lemma corrugationSum_smooth (I : Finset ι) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (amp J R : ℝ) (s : ι → ℝ) (e : ι → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (y : ι → _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (corrugationSum I χ amp J R s e y) := by
  apply ContDiff.sum
  intro i _
  exact localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) _ _ _ _ _ _

lemma corrugationSum_compact (I : Finset ι) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (amp J : ℝ) {R : ℝ} (hR : 0 < R)
    (s : ι → ℝ) (e : ι → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (y : ι → _root_.OAI.Yau.Jets.Coord) :
    HasCompactSupport (corrugationSum I χ amp J R s e y) :=
  finite_sum_compact_support I _ (fun _ _ ↦ localizedCorrugation_compact χ _ hχ _ _ hR _ _ _)

lemma corrugationSum_support (I : Finset ι) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (amp J : ℝ) {R : ℝ} (hR : 0 < R)
    (s : ι → ℝ) (e : ι → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (y : ι → _root_.OAI.Yau.Jets.Coord)
    (U : Set _root_.OAI.Yau.Jets.Coord) (hU : ∀ i ∈ I, ball (y i) (R/2) ⊆ U) :
    tsupport (corrugationSum I χ amp J R s e y) ⊆ U :=
  finite_sum_support_subset I _ U (fun i hi ↦
    (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _).trans (hU i hi))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCubePartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma corrugationCubeCenter_mem (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    corrugationCubeCenter o L n k ∈ Set.Icc o (fun i ↦ o i+L) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  constructor <;> intro i
  · dsimp [corrugationCubeCenter]
    have hk : (0:ℝ) ≤ (k i:ℝ) := by positivity
    nlinarith
  · dsimp [corrugationCubeCenter]
    have hk : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma corrugationCube_ball_inside (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) ⊆
      interior (Set.Icc o (fun i ↦ o i+L)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  intro x hx
  rw [← pi_univ_Icc,interior_pi_set Set.finite_univ]
  intro i _
  change x i ∈ interior (Icc (o i) (o i+L))
  rw [interior_Icc]
  constructor
  all_goals
    have hxi : |x i-corrugationCubeCenter o L n k i| < (L/(n:ℝ))/2 := by
      have hnorm := norm_le_pi_norm (x-corrugationCubeCenter o L n k) i
      exact lt_of_le_of_lt hnorm (by simpa [dist_eq_norm] using hx)
    have ha := abs_lt.mp hxi
    dsimp [corrugationCubeCenter] at ha
    have hk0 : (0:ℝ) ≤ (k i:ℝ) := by positivity
    have hk1 : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma corrugationCube_balls_disjoint (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k j : Fin 4 → Fin n) (hkj : k ≠ j) :
    Disjoint (ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2))
      (ball (corrugationCubeCenter o L n j) ((L/(n:ℝ))/2)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ j i := Function.ne_iff.mp hkj
  have hi' : (k i).val ≠ (j i).val := fun h ↦ hi (Fin.ext h)
  have hd : (1:ℝ) ≤ |(k i:ℝ)-(j i:ℝ)| := by
    rcases lt_or_gt_of_ne hi' with h | h
    · have hh : (k i:ℝ)+1 ≤ (j i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j i:ℝ)+1 ≤ (k i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  apply ball_disjoint_ball
  have hcoord := norm_le_pi_norm (corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i
  have he : ‖(corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i‖ =
      (L/(n:ℝ))*|(k i:ℝ)-(j i:ℝ)| := by
    change |(o i+_)-(o i+_)| = _
    rw [add_sub_add_left_eq_sub,← mul_sub,abs_mul,abs_of_pos hR]
    congr 2
    ring
  rw [he] at hcoord
  rw [dist_eq_norm]
  nlinarith

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationGridFrames
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

theorem exists_corrugation_grid_frames (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hp : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q) :
    ∃ e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      ∀ i, let y := corrugationCubeCenter o L n i
      e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
      (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) ∧
      (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
        sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1))) ∧
      0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
        (g y (metricGradient g S y) (metricGradient g S y)+4)*
          sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1)) := by
  have hex : ∀ i : Fin 4 → Fin n, ∃ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      let y := corrugationCubeCenter o L n i
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
      (∀ a b, g y (e (Pi.single a 1)) (e (Pi.single b 1)) = if a=b then 1 else 0) ∧
      (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
        sourceHessian g S y v v ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) ∧
      0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
        (g y (metricGradient g S y) (metricGradient g S y)+4)*
          sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1)) := by
    intro i
    let y := corrugationCubeCenter o L n i
    have hy := corrugationCubeCenter_mem o hL hn i
    obtain ⟨hp0,q0,hq0,hpq0,hstr⟩ := hadm y hy
    obtain ⟨q,e,hq,hpq,hmax,he0,he1,he,_⟩ := exists_corrugation_frozen_frame
      (g y) (sourceHessian g S y) (hp y hy) (hsym y hy) (metricGradient g S y) q0 hp0 hq0 hpq0
    refine ⟨e,he0,he,?_,?_⟩
    · rw [he1]
      exact hmax
    · rw [he1]
      have hmax0 := hmax q0 hq0 hpq0
      have hgpos := hp y hy (metricGradient g S y) hp0
      have hh := mul_le_mul_of_nonneg_left hmax0 (by positivity : 0 ≤ g y (metricGradient g S y) (metricGradient g S y)+4)
      linarith
  choose e he using hex
  exact ⟨e,he⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_LocalAdmissibilityPersistence
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
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T]

lemma admissibility_eventually (g H : T → E →L[ℝ] E →L[ℝ] ℝ) (p : T → E) (x : T)
    (hg : ContinuousAt g x) (hH : ContinuousAt H x) (hp : ContinuousAt p x)
    (hpp : 0 < g x (p x) (p x)) (t : E) (hpt : g x (p x) t = 0)
    (htt : g x t t = 1)
    (hstrict : 0 < H x (p x) (p x) + (g x (p x) (p x)+4)*H x t t) :
    ∀ᶠ y in 𝓝 x, p y ≠ 0 ∧ ∃ u : E, g y (p y) u = 0 ∧ g y u u = 1 ∧
      0 < H y (p y) (p y) + (g y (p y) (p y)+4)*H y u u := by
  let a : T → ℝ := fun y ↦ g y (p y) (p y)
  have ha : ContinuousAt a x := (hg.clm_apply hp).clm_apply hp
  let z : T → E := fun y ↦ t - (g y (p y) t / a y) • p y
  have hz : ContinuousAt z x := continuousAt_const.sub
    ((((hg.clm_apply hp).clm_apply continuousAt_const).div ha hpp.ne').smul hp)
  have hz0 : z x = t := by simp [z,hpt]
  have hzz : 0 < g x (z x) (z x) := by rw [hz0,htt]; norm_num
  let u : T → E := fun y ↦ metricNormalize (g y) (z y)
  have hu : ContinuousAt u x := metricNormalize_continuousAt g z hg hz hzz
  have hu0 : u x = t := by dsimp [u]; rw [hz0]; exact metricNormalize_fixed _ _ htt
  have hs : ContinuousAt (fun y ↦ H y (p y) (p y) + (a y+4)*H y (u y) (u y)) x :=
    ((hH.clm_apply hp).clm_apply hp).add
      ((ha.add continuousAt_const).mul ((hH.clm_apply hu).clm_apply hu))
  have hsa : ∀ᶠ y in 𝓝 x, 0 < H y (p y) (p y) + (a y+4)*H y (u y) (u y) :=
    hs.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hu0,a] using hstrict))
  have haa : ∀ᶠ y in 𝓝 x, 0 < a y := ha.preimage_mem_nhds (Ioi_mem_nhds hpp)
  have hza : ∀ᶠ y in 𝓝 x, 0 < g y (z y) (z y) :=
    ((hg.clm_apply hz).clm_apply hz).preimage_mem_nhds (Ioi_mem_nhds hzz)
  filter_upwards [haa,hza,hsa] with y hy hyz hys
  have hp0 : p y ≠ 0 := by intro he; simp [a,he] at hy
  refine ⟨hp0,u y,?_,metricNormalize_unit _ _ hyz,hys⟩
  apply metricNormalize_orthogonal
  change g y (p y) (t - (g y (p y) t / a y) • p y) = 0
  simp only [map_sub,map_smul,smul_eq_mul]
  change g y (p y) t - (g y (p y) t / a y) * a y = 0
  rw [div_mul_cancel₀ _ hy.ne',sub_self]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AdmissibilityNeighborhood
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

theorem source_admissibility_neighborhood
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hadm : ∀ x ∈ D, metricGradient g S x ≠ 0 ∧
      ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
        0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
          (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t) :
    ∃ V : Set _root_.OAI.Yau.Jets.Coord, IsOpen V ∧ D ⊆ V ∧ V ⊆ U ∧
      ∀ x ∈ V, metricGradient g S x ≠ 0 ∧
        ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
          0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
            (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t := by
  let A : Set _root_.OAI.Yau.Jets.Coord := {x | x ∈ U ∧ metricGradient g S x ≠ 0 ∧
    ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t}
  refine ⟨interior A,isOpen_interior,?_,fun x hx ↦ (interior_subset hx).1,
    fun x hx ↦ (interior_subset hx).2⟩
  intro x hx
  obtain ⟨hn,t,htu,hpt,hstr⟩ := hadm x hx
  have hgx := hg.contDiffAt (hU.mem_nhds (hDU hx))
  have hSx := hS.contDiffAt (hU.mem_nhds (hDU hx))
  have he := admissibility_eventually g (sourceHessian g S) (metricGradient g S) x
    hgx.continuousAt (localMetricHessian_continuousAt g S x hgx hSx (hp x (hDU hx)))
    (localMetricGradient_continuousAt g S x hgx.continuousAt hSx (hp x (hDU hx)))
    (hp x (hDU hx) _ hn) t hpt htu hstr
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hU.mem_nhds (hDU hx),he] with y hy ha
  obtain ⟨hn,u,hpu,hu,hs⟩ := ha
  exact ⟨hy,hn,u,hu,hpu,hs⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridAssembly
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugationGridSum_smooth (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (n : ℕ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (amp J : ℝ)
    (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (corrugationGridSum o L n χ amp J s e) :=
  corrugationSum_smooth _ χ hχ _ _ _ _ _ _

lemma corrugationGridSum_support (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (amp J : ℝ) (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) :
    HasCompactSupport (corrugationGridSum o L n χ amp J s e) ∧
    tsupport (corrugationGridSum o L n χ amp J s e) ⊆ interior (Icc o (fun i ↦ o i+L)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨corrugationSum_compact _ χ hχ _ _ (div_pos hL hnR) _ _ _,?_⟩
  exact corrugationSum_support _ χ hχ _ _ (div_pos hL hnR) _ _ _ _
    (fun k _ ↦ corrugationCube_ball_inside o hL hn k)

theorem corrugationGridSum_uniform_bound (amp : ℝ) : ∃ B : ℝ, 0 < B ∧
    ∀ (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (n : ℕ), 0 < L → 0 < n →
    ∀ (χ : _root_.OAI.Yau.Jets.Coord → ℝ), tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2) → (∀ z, |χ z| ≤ 1) →
    ∀ (J M : ℝ), 0 < J → 0 ≤ M →
    ∀ (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord),
    (∀ k, 0 ≤ s k ∧ s k ≤ M) → ∀ x,
    |corrugationGridSum o L n χ amp J s e x| ≤ M/J*B := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  refine ⟨B,hB,?_⟩
  intro o L n hL hn χ hχ hχb J M hJ hM s e hs x
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR := div_pos hL hnR
  apply finite_disjoint_sum_bound Finset.univ _ (B := M/J*B) _ (by positivity) _ x
  · intro i _ j _ hij
    exact (corrugationCube_balls_disjoint o hL hn i j hij).mono
      (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _)
      (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _)
  · intro i _ z
    exact (localizedCorrugation_bound χ _ hχb hf (hs i).1 hJ _ _ _ _ z).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hs i).2 hJ.le) hB.le)

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

lemma corrugationFrequency_positive (k : ℕ) : 0 < corrugationFrequency k := by
  unfold corrugationFrequency
  positivity

lemma corrugationSubdivision_positive (k : ℕ) : 0 < corrugationSubdivision k := by
  unfold corrugationSubdivision
  positivity

lemma corrugation_power_reciprocal_tendsto (C : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun k : ℕ ↦ C/((k:ℝ)+1)^p) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hp' := (tendsto_pow_atTop hp).comp hk
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def,Pi.inv_apply] using hp'.inv_tendsto_atTop.const_mul C

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridProperties
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

lemma corrugationEnvelopePerturbation_smooth (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (k : ℕ)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (corrugationEnvelopePerturbation o L k g S χ amp e) :=
  corrugationGridSum_smooth o L _ χ hχ _ _ _ _

lemma corrugationEnvelopePerturbation_support (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L) (k : ℕ)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2)) :
    HasCompactSupport (corrugationEnvelopePerturbation o L k g S χ amp e) ∧
    tsupport (corrugationEnvelopePerturbation o L k g S χ amp e) ⊆ interior (Icc o (fun i ↦ o i+L)) :=
  corrugationGridSum_support o hL (corrugationSubdivision_positive k) χ hχ _ _ _ _

theorem corrugationEnvelopePerturbation_small (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp : ℝ)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2)) (hχb : ∀ z, |χ z| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      ∀ x, |corrugationEnvelopePerturbation o L k g S χ amp e x| < ε := by
  obtain ⟨m,hm,B,hB,hs⟩ := corrugationOldSlope_compact_bounds g S isCompact_Icc hU hDU hg hS hp hn
  obtain ⟨M,hM,hbound⟩ := corrugationGridSum_uniform_bound amp
  have ht : Tendsto (fun k ↦ B/corrugationFrequency k*M) atTop (𝓝 0) := by
    simpa [corrugationFrequency] using
      (corrugation_power_reciprocal_tendsto B (by norm_num : (8:ℕ) ≠ 0)).mul_const M
  filter_upwards [ht.eventually_lt_const hε] with k hk
  intro e x
  apply lt_of_le_of_lt _ hk
  exact hbound o L (corrugationSubdivision k) hL (corrugationSubdivision_positive k) χ hχ hχb
    (corrugationFrequency k) B (corrugationFrequency_positive k) hB.le _ e
    (fun i ↦ ⟨(corrugationOldSlope_positive g S _
      (hp _ (hDU (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i)))
      (hn _ (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i))).le,
      (hs _ (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i)).2⟩) x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationEnvelopeJets
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

lemma metricGradient_add (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S w : _root_.OAI.Yau.Jets.Coord → ℝ) {x : _root_.OAI.Yau.Jets.Coord} (hS : DifferentiableAt ℝ S x) (hw : DifferentiableAt ℝ w x) : metricGradient g (S+w) x = metricGradient g S x+metricGradient g w x := by
  unfold metricGradient
  rw [fderiv_add hS hw,map_add]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLocalHessian
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceHessian_add_at (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S w : _root_.OAI.Yau.Jets.Coord → ℝ) {x : _root_.OAI.Yau.Jets.Coord} (hS : ContDiffAt ℝ ∞ S x)
    (hw : ContDiffAt ℝ ∞ w x) (u v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (S+w) x u v = sourceHessian g S x u v+sourceHessian g w x u v := by
  have hSn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 S y := (hS.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hwn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 w y := (hw.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : fderiv ℝ (S+w) =ᶠ[𝓝 x] fderiv ℝ S+fderiv ℝ w := by
    filter_upwards [hSn,hwn] with y hy hz
    exact fderiv_add (hy.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hz.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [sourceHessian_apply,sourceHessian_apply,sourceHessian_apply,he.fderiv_eq,he.self_of_nhds]
  rw [fderiv_add ((hS.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hw.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  simp only [add_apply,Pi.add_apply]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAdmissibleStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem exists_small_admissible_corrugation (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχsupp : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ) (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∃ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      let w := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun i ↦ o i+L)) ∧ (∀ x, |w x| < ε) ∧
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) ∧
        (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
          sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1)))) ∧
      ∃ V : Set _root_.OAI.Yau.Jets.Coord, IsOpen V ∧ Icc o (fun i ↦ o i+L) ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ V, metricGradient g (S+w) x ≠ 0 ∧
          ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x (metricGradient g (S+w) x) t = 0 ∧
            0 < sourceHessian g (S+w) x (metricGradient g (S+w) x) (metricGradient g (S+w) x) +
              (g x (metricGradient g (S+w) x) (metricGradient g (S+w) x)+4)*sourceHessian g (S+w) x t t := by
  have hn := fun y hy ↦ (hadm y hy).1
  have hadmissible := corrugation_grid_admissibility o hL g S χ hU hDU hg hS hp hsym hadm
    hχsmooth hχsupp hχ0 hχ1 hAχ hχA
  have hχb : ∀ z, |χ z| ≤ 1 := fun z ↦ by rw [abs_of_nonneg (hχ0 z)]; exact hχ1 z
  have hsmall := corrugationEnvelopePerturbation_small o hL g S χ corrugationFixedAmplitude
    hU hDU hg hS hp hn hχsupp hχb hε
  filter_upwards [hadmissible,hsmall] with k hk hs
  obtain ⟨e,he⟩ := exists_corrugation_grid_frames o hL (corrugationSubdivision_positive k)
    g S (fun y hy ↦ hp y (hDU hy)) hsym hadm
  let w := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
  have hw : ContDiff ℝ ∞ w := corrugationEnvelopePerturbation_smooth o L k g S χ corrugationFixedAmplitude e hχsmooth
  have had := hk e (fun i ↦ (he i).1) (fun i ↦ (he i).2.1) (fun i ↦ (he i).2.2.1)
  obtain ⟨V,hV,hDV,hVU,hVa⟩ := source_admissibility_neighborhood g (S+w) hU hDU hg (hS.add hw.contDiffOn) hp had
  refine ⟨e,hw,(corrugationEnvelopePerturbation_support o hL k g S χ corrugationFixedAmplitude e hχsupp).1,
    (corrugationEnvelopePerturbation_support o hL k g S χ corrugationFixedAmplitude e hχsupp).2,
    hs e,?_,V,hV,hDV,hVU,hVa⟩
  intro i
  exact ⟨(he i).1,(he i).2.1,(he i).2.2.1⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFixedCutoff
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

lemma corrugationFixedCutoff_spec : ∃ C : ℝ,
    0 < C ∧ ContDiff ℝ ∞ corrugationFixedCutoff ∧ HasCompactSupport corrugationFixedCutoff ∧
    tsupport corrugationFixedCutoff ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2) ∧
    (∀ x, 0 ≤ corrugationFixedCutoff x ∧ corrugationFixedCutoff x ≤ 1) ∧
    (∀ x ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) (1/4), corrugationFixedCutoff =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
    ∀ x, ‖fderiv ℝ corrugationFixedCutoff x‖ ≤ C*(corrugationFixedCutoff x)^((7:ℝ)/8) :=
  Classical.choose_spec exists_corrugation_cutoff

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFixedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem exists_small_fixed_admissible_corrugation (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∃ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      let w := corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun i ↦ o i+L)) ∧ (∀ x, |w x| < ε) ∧
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) ∧
        (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
          sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1)))) ∧
      ∃ V : Set _root_.OAI.Yau.Jets.Coord, IsOpen V ∧ Icc o (fun i ↦ o i+L) ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ V, metricGradient g (S+w) x ≠ 0 ∧
          ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x (metricGradient g (S+w) x) t = 0 ∧
            0 < sourceHessian g (S+w) x (metricGradient g (S+w) x) (metricGradient g (S+w) x) +
              (g x (metricGradient g (S+w) x) (metricGradient g (S+w) x)+4)*sourceHessian g (S+w) x t t := by
  obtain ⟨C,hC,hχ,hc,hsupp,hrange,_,hder⟩ := corrugationFixedCutoff_spec
  exact exists_small_admissible_corrugation o hL g S corrugationFixedCutoff hU hDU hg hS hp hsym hadm
    hχ hsupp (fun z ↦ (hrange z).1) (fun z ↦ (hrange z).2) hC hder hε

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGainStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem exists_small_corrugation_gain_stage {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ), 0 < L →
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (U : Set _root_.OAI.Yau.Jets.Coord),
      IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U → ContDiffOn ℝ ∞ g U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ∀ u v, g y u v = g y v u) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ S : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiffOn ℝ ∞ S U →
      sourceDirectionalAdmissibleOn g S (Icc o (fun j ↦ o j+L)) →
      ∀ ε : ℝ, 0 < ε → ∃ w : _root_.OAI.Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun j ↦ o j+L)) ∧ (∀ x, |w x| < ε) ∧
      sourceDirectionalAdmissibleOn g (S+w) (Icc o (fun j ↦ o j+L)) ∧
      (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+w) x := by
  obtain ⟨γ,hγ,hgain⟩ := corrugation_grid_integrated_gain hc hM
  refine ⟨γ,hγ,?_⟩
  intro o L hL g U hU hDU hg hp hsym hcmp S hS hadm ε hε
  have hsmall := exists_small_fixed_admissible_corrugation o hL g S hU hDU hg hS hp hsym hadm hε
  have hgain' := hgain o L hL g S U hU hDU hg hS hp (fun y hy ↦ (hadm y hy).1) hcmp
  obtain ⟨k,hk,hgaink⟩ := (hsmall.and hgain').exists
  obtain ⟨e,hsmooth,hcompact,hsupp,hsmall,hframe,V,hV,hDV,hVU,hadmnew⟩ := hk
  refine ⟨corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e,
    hsmooth,hcompact,hsupp,hsmall,fun x hx ↦ hadmnew x (hDV hx),?_⟩
  exact hgaink e (fun i ↦ ⟨(hframe i).1,(hframe i).2.1⟩)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFiniteGainLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology

theorem exists_finite_corrugation_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ), 0 < L →
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (U : Set _root_.OAI.Yau.Jets.Coord),
      IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U → ContDiffOn ℝ ∞ g U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ∀ u v, g y u v = g y v u) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ S : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiffOn ℝ ∞ S U →
      sourceDirectionalAdmissibleOn g S (Icc o (fun j ↦ o j+L)) →
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ w : _root_.OAI.Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun j ↦ o j+L)) ∧ (∀ x, |w x| < ε) ∧
      sourceDirectionalAdmissibleOn g (S+w) (Icc o (fun j ↦ o j+L)) ∧
      (1+γ)^n*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+w) x := by
  obtain ⟨γ,hγ,hstage⟩ := exists_small_corrugation_gain_stage hc hM
  refine ⟨γ,hγ,?_⟩
  intro o L hL g U hU hDU hg hp hsym hcmp S hS hadm n
  induction n with
  | zero =>
    intro ε hε
    refine ⟨0,contDiff_const,HasCompactSupport.zero,?_,?_,?_,?_⟩
    · simp
    · simpa using fun _ : _root_.OAI.Yau.Jets.Coord ↦ hε
    · simpa using hadm
    · simp
  | succ n ih =>
    intro ε hε
    obtain ⟨v,hv,hvc,hvs,hvb,hva,hvg⟩ := ih (ε/2) (by linarith)
    obtain ⟨w,hw,hwc,hws,hwb,hwa,hwg⟩ := hstage o L hL g U hU hDU hg hp hsym hcmp
      (S+v) (hS.add hv.contDiffOn) hva (ε/2) (by linarith)
    refine ⟨v+w,hv.add hw,hvc.add hwc,(tsupport_add v w).trans (union_subset hvs hws),?_,?_,?_⟩
    · intro x
      change |v x+w x| < ε
      exact (abs_add_le _ _).trans_lt (by linarith [hvb x,hwb x])
    · simpa only [add_assoc] using hwa
    · calc
        (1+γ)^(n+1)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) =
            (1+γ)*((1+γ)^n*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x)) := by
              rw [pow_succ]; ring
        _ ≤ (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+v) x) :=
          mul_le_mul_of_nonneg_left hvg (by linarith)
        _ ≤ ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+(v+w)) x := by
          simpa only [add_assoc] using hwg

open Yau.Jets Set Filter
open scoped Topology

lemma sourceDirectionalAdmissible_congr (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S R : _root_.OAI.Yau.Jets.Coord → ℝ) {x : _root_.OAI.Yau.Jets.Coord} (he : S =ᶠ[𝓝 x] R) :
    sourceDirectionalAdmissibleOn g S {x} ↔ sourceDirectionalAdmissibleOn g R {x} := by
  have hp : metricGradient g S x = metricGradient g R x := by simp only [metricGradient,he.fderiv_eq]
  have hH : sourceHessian g S x = sourceHessian g R x := by
    simp only [sourceHessian,he.fderiv_eq,he.fderiv.fderiv_eq]
  simp only [sourceDirectionalAdmissibleOn,mem_singleton_iff,forall_eq,hp,hH]

lemma sourceDirectionalAdmissible_support (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S w : _root_.OAI.Yau.Jets.Coord → ℝ) {K D : Set _root_.OAI.Yau.Jets.Coord} (hs : tsupport w ⊆ D)
    (hold : sourceDirectionalAdmissibleOn g S K)
    (hnew : sourceDirectionalAdmissibleOn g (S+w) D) :
    sourceDirectionalAdmissibleOn g (S+w) K := by
  intro x hx
  by_cases hd : x ∈ D
  · exact hnew x hd
  · have he : S+w =ᶠ[𝓝 x] S := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun hw ↦ hd (hs hw))] with y hy
      simp [hy]
    have hh : sourceDirectionalAdmissibleOn g S {x} := fun y hy ↦ by
      rw [mem_singleton_iff] at hy
      subst y
      exact hold x hx
    exact ((sourceDirectionalAdmissible_congr g (S+w) S he).mpr hh) x (mem_singleton x)

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLargeSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem exists_large_admissible_corrugation (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun j ↦ o j+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun j ↦ o j+L), ∀ u v, g y u v = g y v u)
    (hadm : sourceDirectionalAdmissibleOn g S (Icc o (fun j ↦ o j+L)))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun j ↦ o j+L)) ∧ (∀ x, |w x| < ε) ∧ (∀ x, |w x| ≤ ε/2) ∧
      ContDiffOn ℝ ∞ (S+w) U ∧
      T < ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+w) x ∧
      ∃ V : Set _root_.OAI.Yau.Jets.Coord, IsOpen V ∧ Icc o (fun j ↦ o j+L) ⊆ V ∧ V ⊆ U ∧
        sourceDirectionalAdmissibleOn g (S+w) V := by
  let D := Icc o (fun j ↦ o j+L)
  obtain ⟨c,hc,M,hM,hcmp⟩ := compact_metric_comparison g isCompact_Icc (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨γ,hγ,hfinite⟩ := exists_finite_corrugation_gain hc hM
  obtain ⟨m,hm,B,hB,hs⟩ := corrugationOldSlope_compact_bounds g S isCompact_Icc hU hDU hg hS hp
    (fun y hy ↦ (hadm y hy).1)
  have hvol : volume.real D = L^4 := by
    simp [D,measureReal_def,Real.volume_Icc_pi,ENNReal.toReal_ofReal hL.le]
  have hoint : IntegrableOn (corrugationOldSlope g S) D :=
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU).integrableOn_Icc
  have hlow : m*volume.real D ≤ ∫ x in D, corrugationOldSlope g S x := by
    have hh := setIntegral_mono_on (integrableOn_const (isCompact_Icc.measure_ne_top (μ := volume)))
      hoint measurableSet_Icc (fun x hx ↦ (hs x hx).1)
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using hh
  have hpos : 0 < ∫ x in D, corrugationOldSlope g S x := by
    rw [hvol] at hlow
    exact (mul_pos hm (pow_pos hL 4)).trans_le hlow
  obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < 1+γ)).eventually_gt_atTop
    (T/(∫ x in D, corrugationOldSlope g S x))).exists
  have hn' : T < (1+γ)^n*(∫ x in D, corrugationOldSlope g S x) := (div_lt_iff₀ hpos).mp hn
  obtain ⟨w,hw,hwc,hws,hwb,hwa,hwg⟩ := hfinite o L hL g U hU hDU hg hp hsym hcmp S hS hadm n (ε/2) (by linarith)
  have hnewS := hS.add hw.contDiffOn
  refine ⟨w,hw,hwc,hws,fun x ↦ (hwb x).trans (by linarith),fun x ↦ (hwb x).le,hnewS,hn'.trans_le hwg,?_⟩
  exact source_admissibility_neighborhood g (S+w) hU hDU hg hnewS hp hwa

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeNestedDomainsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set
open scoped Topology

open Yau.Jets Set Filter
open scoped ContDiff Topology

theorem exists_signed_envelope_offset {K P : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hP : IsOpen P) (hKP : K ⊆ P) :
    ∃ f : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, |f x| ≤ 1) ∧
      (∀ x ∈ K, f =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∃ C : Set _root_.OAI.Yau.Jets.Coord, IsCompact C ∧ C ⊆ P ∧ K ⊆ C ∧
        ∀ x ∉ C, f x = -1 := by
  obtain ⟨b,hb,hbc,hbP,hbr,hb1⟩ := compact_smooth_cutoff hK hP hKP
  refine ⟨fun x ↦ 2*b x-1,(contDiff_const.mul hb).sub contDiff_const,?_,?_,
    tsupport b,hbc,hbP,?_,?_⟩
  · intro x
    rw [abs_le]
    constructor <;> nlinarith [(hbr x).1,(hbr x).2]
  · intro x hx
    filter_upwards [hb1 x hx] with y hy
    norm_num [hy]
  · intro x hx
    apply subset_tsupport
    have hh := (hb1 x hx).eq_of_nhds
    change b x ≠ 0
    rw [hh]
    norm_num
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeParameterJets
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

lemma metricGradient_const_smul (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    metricGradient g (t • f) x = t • metricGradient g f x := by
  simp only [metricGradient, fderiv_const_smul (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x), map_smul]

lemma sourceHessian_const_smul (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (t • f) x = t • sourceHessian g f x := by
  ext u v
  simp only [sourceHessian, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, smul_apply, smul_eq_mul]
  rw [show t • f = (fun z ↦ t*f z) from rfl, scalar_const_mul_second t f hf]
  rw [fderiv_const_mul (hf.differentiable (by simp) x)]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma envelope_parameter_jets (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S f : _root_.OAI.Yau.Jets.Coord → ℝ) {x : _root_.OAI.Yau.Jets.Coord} (hS : ContDiffAt ℝ ∞ S x)
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    metricGradient g (S+t • f) x = metricGradient g S x + t • metricGradient g f x ∧
    sourceHessian g (S+t • f) x = sourceHessian g S x + t • sourceHessian g f x := by
  constructor
  · rw [metricGradient_add g S (t • f) (hS.differentiableAt (by simp))
      ((contDiff_const.smul hf).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x), metricGradient_const_smul g f hf]
  · ext u v
    rw [sourceHessian_add_at g S (t • f) hS (contDiff_const.smul hf).contDiffAt,
      sourceHessian_const_smul g f hf]
    rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeParameterAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem envelope_parameter_admissibility
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S f : _root_.OAI.Yau.Jets.Coord → ℝ)
    {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (ha : sourceDirectionalAdmissibleOn g S K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → sourceDirectionalAdmissibleOn g (S+t • f) K := by
  let p : ℝ × _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord := fun z ↦ metricGradient g S z.2 + z.1 • metricGradient g f z.2
  let H : ℝ × _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ :=
    fun z ↦ sourceHessian g S z.2 + z.1 • sourceHessian g f z.2
  have he : ∀ᶠ t : ℝ in 𝓝 0, sourceDirectionalAdmissibleOn g (S+t • f) K := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hgx := hg.contDiffAt (hU.mem_nhds (hKU hx))
    have hSx := hS.contDiffAt (hU.mem_nhds (hKU hx))
    have hpx := hp x (hKU hx)
    have hpS : ContinuousAt (metricGradient g S) x :=
      localMetricGradient_continuousAt g S x hgx.continuousAt hSx hpx
    have hpf : ContinuousAt (metricGradient g f) x :=
      localMetricGradient_continuousAt g f x hgx.continuousAt hf.contDiffAt hpx
    have hHS : ContinuousAt (sourceHessian g S) x :=
      localMetricHessian_continuousAt g S x hgx hSx hpx
    have hHf : ContinuousAt (sourceHessian g f) x :=
      localMetricHessian_continuousAt g f x hgx hf.contDiffAt hpx
    have hpc : ContinuousAt p (0,x) := by
      exact (hpS.comp (continuousAt_snd (p := ((0:ℝ),x)) )).fun_add
        (continuousAt_fst.fun_smul (hpf.comp continuousAt_snd))
    have hHc : ContinuousAt H (0,x) := by
      exact (hHS.comp (continuousAt_snd (p := ((0:ℝ),x)) )).fun_add
        (continuousAt_fst.fun_smul (hHf.comp continuousAt_snd))
    obtain ⟨hn,v,hv,hpv,hs⟩ := ha x hx
    have h0 : p (0,x) = metricGradient g S x := by simp [p]
    have hH0 : H (0,x) = sourceHessian g S x := by simp [H]
    have had := admissibility_eventually (fun z : ℝ × _root_.OAI.Yau.Jets.Coord ↦ g z.2) H p (0,x)
      (hgx.continuousAt.comp continuousAt_snd) hHc hpc (by simpa [h0] using hpx _ hn)
      v (by simpa [h0] using hpv) hv (by simpa [h0,hH0] using hs)
    have hUn : ∀ᶠ z : ℝ × _root_.OAI.Yau.Jets.Coord in 𝓝 (0,x), z.2 ∈ U :=
      continuousAt_snd.preimage_mem_nhds (hU.mem_nhds (hKU hx))
    filter_upwards [had,hUn] with z hz hzU
    obtain ⟨hn,v,hpv,hv,hs⟩ := hz
    obtain ⟨hgp,hgH⟩ := envelope_parameter_jets g S f (hS.contDiffAt (hU.mem_nhds hzU)) hf z.1
    rw [hgp,hgH]
    exact ⟨hn,v,hv,hpv,hs⟩
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,fun t ht ↦ hd ?_⟩
  simpa [Real.dist_eq] using ht

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopePlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem exists_placed_envelope_oai (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    {P U K : Set _root_.OAI.Yau.Jets.Coord} (hP : IsOpen P) (hPc : IsCompact (closure P))
    (hU : IsOpen U) (hPU : closure P ⊆ U)
    (hDP : Icc o (fun j ↦ o j+L) ⊆ P) (hK : IsCompact K) (hKP : K ⊆ P)
    (hg : ContDiffOn ℝ ∞ g U) (hS0 : ContDiffOn ℝ ∞ S0 U)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ Icc o (fun j ↦ o j+L), ∀ u v, g x u v = g x v u)
    (hseed : sourceDirectionalAdmissibleOn g S0 (closure P)) (T : ℝ) :
    ∃ (S : _root_.OAI.Yau.Jets.Coord → ℝ) (c : ℝ) (C V : Set _root_.OAI.Yau.Jets.Coord), 0 < c ∧
      ContDiffOn ℝ ∞ S U ∧ IsCompact C ∧ C ⊆ P ∧
      Icc o (fun j ↦ o j+L) ∪ K ⊆ C ∧
      (∀ x ∈ Icc o (fun j ↦ o j+L) ∪ K, S0 x+c ≤ S x) ∧
      (∀ x ∉ C, S x ≤ S0 x-c) ∧
      IsOpen V ∧ closure P ⊆ V ∧ V ⊆ U ∧ sourceDirectionalAdmissibleOn g S V ∧
      T < ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x := by
  let D := Icc o (fun j ↦ o j+L)
  have hDcl : D ⊆ closure P := hDP.trans subset_closure
  obtain ⟨f,hf,hfb,hf1,C,hC,hCP,hDC,hfout⟩ := exists_signed_envelope_offset
    (isCompact_Icc.union hK) hP (union_subset hDP hKP)
  obtain ⟨δ,hδ,had⟩ := envelope_parameter_admissibility g S0 f hPc hU hPU hg hS0 hf hp hseed
  let t := δ/2
  have ht : 0 < t := by dsimp [t] <;> positivity
  have htd : |t| < δ := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hadt := had t htd
  have hSt : ContDiffOn ℝ ∞ (S0+t • f) U := hS0.add (contDiff_const.smul hf).contDiffOn
  obtain ⟨w,hw,hwc,hws,hwb,hwbb,hSw,hgain,W,hW,hDW,hWU,hadw⟩ :=
    exists_large_admissible_corrugation o hL g (S0+t • f) hU (hDcl.trans hPU)
      hg hSt hp hsym (fun x hx ↦ hadt x (hDcl hx)) T (by positivity : 0 < t/2)
  have hadall := sourceDirectionalAdmissible_support g (S0+t • f) w
    (hws.trans interior_subset) hadt (fun x hx ↦ hadw x (hDW hx))
  obtain ⟨V,hV,hPV,hVU,hVa⟩ := source_admissibility_neighborhood g ((S0+t • f)+w)
    hU hPU hg hSw hp hadall
  refine ⟨(S0+t • f)+w,t/2,C,V,by positivity,hSw,hC,hCP,hDC,?_,?_,hV,hPV,hVU,hVa,hgain⟩
  · intro x hx
    have hx1 := (hf1 x hx).eq_of_nhds
    have hb := (abs_lt.mp (hwb x)).1
    change S0 x+t/2 ≤ S0 x+t*f x+w x
    rw [hx1]
    linarith
  · intro x hx
    have hxD : x ∉ D := fun hd ↦ hx (hDC (Or.inl hd))
    have hw0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hxD (interior_subset (hws hs)))
    change S0 x+t*f x+w x ≤ S0 x-t/2
    rw [hfout x hx,hw0]
    linarith

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.exists_placed_envelope_oai := @OAI.Yau.Geometry.exists_placed_envelope_oai
