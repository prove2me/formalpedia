-- Prove2me | solution 1 for OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:36.174205+00:00
-- url     : https://prove2.me/submissions/c4b5f2d0-30f6-4ebb-a399-98dbb86a71e2

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ManifoldCompactExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] [LocallyCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma manifold_compact_smooth_cutoff {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ U ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      ∀ x ∈ K, b =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hb1,hb0,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    I hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hsupp : tsupport (b : M → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra h
    exact hx (hb0 x h)
  refine ⟨b,b.contMDiff,hL.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans hLU,hb,?_⟩
  intro x hx
  exact Filter.Eventually.filter_mono (nhds_le_nhdsSet hx) hb1

lemma manifold_compact_smooth_extension {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : M → F) (hf : ContMDiffOn I 𝓘(ℝ,F) ∞ f U) :
    ∃ G : M → F, ContMDiff I 𝓘(ℝ,F) ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := manifold_compact_smooth_cutoff (I := I) hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContMDiff I 𝓘(ℝ,F) ∞ G := by
    intro x
    by_cases hx : x ∈ tsupport b
    · exact (hb x).smul ((hf x (hbU hx)).contMDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contMDiffAt_const (c := (0:F))).congr_of_eventuallyEq
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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AmbientDerivativeDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Bundle Manifold Set MeasureTheory
open scoped ENNReal NNReal ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma map_edist_le_pathELength (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    (C : ℝ≥0)
    (hC : ∀ x, ENorm.enorm (E := TangentSpace I x →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f x) ≤ C)
    (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0:ℝ) 1)) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 := by
  have hs : ContDiffOn ℝ 1 (f ∘ γ) (Icc (0:ℝ) 1) :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn hγ)
  calc
    edist (f (γ 0)) (f (γ 1)) = ‖(f ∘ γ) 1 - (f ∘ γ) 0‖ₑ := by
      rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖derivWithin (f ∘ γ) (Icc (0:ℝ) 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hs zero_le_one
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖mfderivWithin 𝓘(ℝ) 𝓘(ℝ,F) (f ∘ γ)
          (Icc (0:ℝ) 1) t 1‖ₑ := by
      simp_rw [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin]; rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, C * ‖mfderivWithin 𝓘(ℝ) I γ (Icc (0:ℝ) 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [mfderiv_comp_mfderivWithin t (hf.mdifferentiable one_ne_zero (γ t))
        (hγ.mdifferentiableOn one_ne_zero t ht)
        (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact uniqueDiffOn_Icc zero_lt_one t ht)]
      apply (ContinuousLinearMap.le_opENorm (mfderiv I 𝓘(ℝ,F) f (γ t))
        (mfderivWithin 𝓘(ℝ) I γ (Icc (0:ℝ) 1) t 1)).trans
      gcongr
      exact hC (γ t)
    _ = C * pathELength I γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

lemma map_edist_le_riemannianEDist (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    (C : ℝ≥0) (hpos : 0 < C)
    (hC : ∀ x, ENorm.enorm (E := TangentSpace I x →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f x) ≤ C)
    (x y : M) :
    edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  rw [riemannianEDist, ENNReal.mul_iInf_of_ne (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top]
  simp_rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  simpa using map_edist_le_pathELength f hf C hC
    (γ ∘ projIcc 0 1 zero_le_one) (hγ.comp_contMDiffOn contMDiffOn_projIcc)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactDifferentialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Bundle Manifold Set Filter ContinuousLinearMap
open scoped ENNReal NNReal ContDiff Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma eventually_norm_mfderiv_map_lt (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    (x : M) : ∃ C > 0, ∀ᶠ y in 𝓝 x,
      Norm.norm (E := TangentSpace I y →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f y) < C := by
  let D := inTangentCoordinates I 𝓘(ℝ,F) id f (mfderiv I 𝓘(ℝ,F) f) x
  have hD : ContinuousAt D x := ((hf x).mfderiv_const (m := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  obtain ⟨K,hK,hchart⟩ := eventually_norm_mfderiv_extChartAt_lt I x
  refine ⟨(‖D x‖+1)*K, by positivity, ?_⟩
  have hlocal : ∀ᶠ y in 𝓝 x, ‖D y‖ < ‖D x‖+1 :=
    hD.norm.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hlocal,hchart,chart_source_mem_nhds H x] with y hy hcy hsrc
  have hdecomp : mfderiv I 𝓘(ℝ,F) f y =
      (D y).comp (mfderiv I 𝓘(ℝ,E) (extChartAt I x) y) := by
    let d : E →L[ℝ] F := mfderiv I 𝓘(ℝ,F) f y
    let A : F →L[ℝ] F := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F)
      (extChartAt 𝓘(ℝ,F) (f x)) (f y)
    let B : E →L[ℝ] E := mfderivWithin 𝓘(ℝ,E) I
      (extChartAt I x).symm (range I) (extChartAt I x y)
    let C : E →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) y
    have hA : A = ContinuousLinearMap.id ℝ F := by
      change (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) id (f y) : F →L[ℝ] F) = _
      exact mfderiv_id
    have hcoord : D y = A.comp (d.comp B) :=
      inTangentCoordinates_eq_mfderiv_comp (I := I) (I' := 𝓘(ℝ,F))
        (f := id) (g := f) (ϕ := mfderiv I 𝓘(ℝ,F) f)
        (x₀ := x) (x := y) hsrc (mem_univ _)
    have hBC : B.comp C = ContinuousLinearMap.id ℝ E :=
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := I) (x := x) (y := y) (by simpa only [extChartAt_source] using hsrc)
    ext v
    change d v = D y (C v)
    have hv := congrArg (fun L : E →L[ℝ] F ↦ L (C v)) hcoord
    have hbc := congrArg (fun L : E →L[ℝ] E ↦ L v) hBC
    change B (C v) = v at hbc
    simpa only [hA, comp_apply, id_apply, hbc] using hv.symm
  rw [hdecomp]
  apply (opNorm_comp_le _ _).trans_lt
  let P : TangentSpace I y →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) y
  have hP : ‖P‖ < K := hcy
  exact (mul_le_mul_of_nonneg_right hy.le (norm_nonneg P)).trans_lt
    (mul_lt_mul_of_pos_left hP (by positivity))

lemma compact_norm_mfderiv_bound (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x ∈ K,
      ENorm.enorm (E := TangentSpace I x →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f x) ≤ C := by
  classical
  choose c hc hloc using eventually_norm_mfderiv_map_lt f hf
  obtain ⟨t,ht,hcover⟩ := hK.elim_nhds_subcover
    (fun x ↦ {y | Norm.norm (E := TangentSpace I y →L[ℝ] F)
      (mfderiv I 𝓘(ℝ,F) f y) < c x}) (fun x _ ↦ hloc x)
  let C : ℝ := 1 + ∑ x ∈ t, c x
  have hC : 0 < C := by
    dsimp [C]
    have := Finset.sum_nonneg (fun x (_ : x ∈ t) ↦ (hc x).le)
    linarith
  refine ⟨⟨C,hC.le⟩,hC,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hle : c y ≤ ∑ z ∈ t, c z := Finset.single_le_sum (fun z _ ↦ (hc z).le) hy
  let L : TangentSpace I x →L[ℝ] F := mfderiv I 𝓘(ℝ,F) f x
  have hbound : ‖L‖ ≤ C := by
    change ‖L‖ < c y at hxy
    dsimp [C] <;> linarith
  exact (ofReal_norm (E := TangentSpace I x →L[ℝ] F) L).symm.le.trans
    ((ENNReal.ofReal_le_ofReal hbound).trans_eq (ENNReal.ofReal_eq_coe_nnreal hC.le))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetMetricEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold Set MeasureTheory
open scoped ENNReal NNReal ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_projection_energy_bound (g : SmoothMetric) (P : Manifold5 → F)
    (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
      ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖^2 ≤ (C:ℝ)^2*g.inner x v v := by
  let : RiemannianBundle (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w ↦ rfl⟩
  obtain ⟨C,hpos,hC⟩ := Yau.Geometry.compact_norm_mfderiv_bound P
    (hP.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) isCompact_univ
  refine ⟨C,hpos,?_⟩
  intro x v
  let L : TangentSpace modelWithCorners x →L[ℝ] F :=
    mfderiv modelWithCorners 𝓘(ℝ,F) P x
  have hnorm : ‖L‖ₑ ≤ C := hC x (mem_univ x)
  have hop : ‖L‖ ≤ (C:ℝ) := by exact_mod_cast hnorm
  have hbound : ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖ ≤ (C:ℝ)*‖v‖ := by
    exact (ContinuousLinearMap.le_opNorm L v).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg v))
  have hi : g.inner x v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
  rw [hi]
  nlinarith [sq_nonneg (‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖-(C:ℝ)*‖v‖),
    mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg (norm_nonneg (mfderiv modelWithCorners 𝓘(ℝ,F) P x v))
      (mul_nonneg C.coe_nonneg (norm_nonneg v)))]

variable [MeasurableSpace F] [BorelSpace F]

lemma energy_projection_nodal_measure (g : SmoothMetric) (P : Manifold5 → F)
    (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) (C : ℝ≥0) (hpos : 0 < C)
    (hE : ∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
      ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖^2 ≤ (C:ℝ)^2*g.inner x v v) :
    ∀ (u : Manifold5 → ℝ) (Z : Set F), Z ⊆ P '' {x | u x = 0} →
      Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  let : RiemannianBundle (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w ↦ rfl⟩
  let L (x : Manifold5) : TangentSpace modelWithCorners x →L[ℝ] F :=
    mfderiv modelWithCorners 𝓘(ℝ,F) P x
  have hop (x : Manifold5) : ‖L x‖ ≤ (C:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    intro v
    have hi : g.inner x v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
    have he := hE x v
    rw [hi] at he
    change ‖L x v‖^2 ≤ (C:ℝ)^2*‖v‖^2 at he
    nlinarith only [he, norm_nonneg (L x v),
      mul_nonneg C.coe_nonneg (norm_nonneg v)]
  have hC (x : Manifold5) : ‖L x‖ₑ ≤ C := by exact_mod_cast hop x
  have hd := Yau.Geometry.map_edist_le_riemannianEDist P (hP.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) C hpos hC
  let : MeasurableSpace Manifold5 := borel Manifold5
  let : BorelSpace Manifold5 := ⟨rfl⟩
  let : EMetricSpace Manifold5 := EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5
  let : PseudoEMetricSpace Manifold5 :=
    (EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5).toPseudoEMetricSpace
  have hLip : LipschitzWith C P := hd
  intro u Z hZ
  have hh := (measure_mono hZ).trans
    (hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4) {x | u x = 0})
  simpa only [show (4:ℝ) = (4:ℕ) by norm_num, ENNReal.rpow_natCast, nodalMeasure] using hh

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetProductChart
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Filter Yau.Jets
open scoped ContDiff Topology NNReal ENNReal
noncomputable section

lemma productChart_inverse_mem (p : Manifold5) (a b : ℝ) {z : _root_.OAI.Yau.Jets.Coord × ℝ}
    (hz : z ∈ productChartDomain p a b) :
    productChartInverse p a b z ∈ (extChartAt modelWithCorners p).source :=
  (extChartAt modelWithCorners p).map_target hz

lemma productChart_right_inv (p : Manifold5) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    {z : _root_.OAI.Yau.Jets.Coord × ℝ} (hz : z ∈ productChartDomain p a b) :
    productChart p a b (productChartInverse p a b z) = z := by
  unfold productChart productChartInverse
  rw [(extChartAt modelWithCorners p).right_inv hz, modelCoordinateEquiv.apply_symm_apply]
  simp [hb]

lemma productChart_contMDiffOn (p : Manifold5) (a b : ℝ) :
    ContMDiffOn modelWithCorners 𝓘(ℝ,_root_.OAI.Yau.Jets.Coord × ℝ) ∞ (productChart p a b)
      (extChartAt modelWithCorners p).source := by
  have hc : ContMDiffOn modelWithCorners 𝓘(ℝ,_root_.OAI.Yau.Jets.Coord × ℝ) ∞
      (fun m ↦ modelCoordinateEquiv (extChartAt modelWithCorners p m))
      (extChartAt modelWithCorners p).source :=
    modelCoordinateEquiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn (by
      simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := modelWithCorners) (x := p)))
  have hn : ContDiff ℝ ∞ (fun z : _root_.OAI.Yau.Jets.Coord × ℝ ↦ (z.1,(z.2-a)/b)) :=
    contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const b)
  exact hn.contMDiff.comp_contMDiffOn hc

lemma productChartInverse_continuousOn (p : Manifold5) (a b : ℝ) :
    ContinuousOn (productChartInverse p a b) (productChartDomain p a b) := by
  apply (continuousOn_extChartAt_symm p).comp
    (modelCoordinateEquiv.symm.continuous.comp
      (continuous_fst.prodMk (continuous_const.add (continuous_const.mul continuous_snd)))).continuousOn
  exact fun z hz ↦ hz

lemma compact_productChart_extension (p : Manifold5) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    {K : Set (_root_.OAI.Yau.Jets.Coord × ℝ)} (hK : IsCompact K) (hKD : K ⊆ productChartDomain p a b) :
    ∃ P : Manifold5 → _root_.OAI.Yau.Jets.Coord × ℝ, ContMDiff modelWithCorners 𝓘(ℝ,_root_.OAI.Yau.Jets.Coord × ℝ) ∞ P ∧
      ∀ z ∈ K, P (productChartInverse p a b z) = z := by
  have hL : IsCompact (productChartInverse p a b '' K) :=
    hK.image_of_continuousOn ((productChartInverse_continuousOn p a b).mono hKD)
  obtain ⟨P,hP,_,_,hPK⟩ := Yau.Geometry.manifold_compact_smooth_extension
    (I := modelWithCorners) hL (isOpen_extChartAt_source p)
    (by rintro m ⟨z,hz,rfl⟩; exact productChart_inverse_mem p a b (hKD hz))
    (productChart p a b) (productChart_contMDiffOn p a b)
  refine ⟨P,hP,?_⟩
  intro z hz
  rw [(hPK _ (mem_image_of_mem _ hz)).eq_of_nhds,
    productChart_right_inv p a hb (hKD hz)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetWarpedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

variable (B : Base → AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v)
    (q : Base → ℝ) (hq : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ q) (hpos : ∀ x, 0 < q x)

lemma ambientWeightedMetric_inner (x : Manifold5) (v w : TangentSpace modelWithCorners x) :
    (ambientWeightedMetric B hB hs hp q hq hpos).inner x v w =
      B x.1 (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 v.1)
        (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 w.1) +
      (q x.1)^2 * @inner ℝ ℂ _
        (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2 : ℂ)
        (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 w.2 : ℂ) := by
  change warpedAmbientForm (B x.1) (q x.1)
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x v)
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x w) = _
  erw [targetEmbedding_derivative]
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveMatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma real_dot_self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (v i))

lemma positive_matrix_inverse_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v))
    (v : n → ℝ) :
    b⁻¹ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A⁻¹ *ᵥ v) ∧
    v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ a⁻¹ * (v ⬝ᵥ v) := by
  let u := A⁻¹ *ᵥ v
  have hu : A *ᵥ u = v := by
    dsimp [u]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  have hs : Aᵀ = A := by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  have hcross' : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, hu, dotProduct_comm]
  have hpos := hA.posSemidef.dotProduct_mulVec_nonneg (v - b • u)
  simp only [star_trivial, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hcross', hu] at hpos
  have hnorm := real_dot_self_nonneg (v - a • u)
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm u v] at hnorm
  have hu_lo := hlo u
  rw [hu, dotProduct_comm u v] at hu_lo
  have hupper : a * (v ⬝ᵥ u) ≤ v ⬝ᵥ v := by
    nlinarith [mul_le_mul_of_nonneg_left hu_lo ha.le]
  have hlower : v ⬝ᵥ v ≤ b * (v ⬝ᵥ u) := by
    have h := hhi v
    rw [dotProduct_comm u v] at hpos
    nlinarith
  constructor
  · change b⁻¹ * (v ⬝ᵥ v) ≤ v ⬝ᵥ u
    rw [inv_mul_eq_div, div_le_iff₀ hb]
    nlinarith
  · change v ⬝ᵥ u ≤ a⁻¹ * (v ⬝ᵥ v)
    rw [inv_mul_eq_div, le_div_iff₀ ha]
    nlinarith

lemma positive_matrix_eigenvalue_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b : ℝ)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) (i : n) :
    a ≤ hA.1.eigenvalues i ∧ hA.1.eigenvalues i ≤ b := by
  have he : (⇑(hA.1.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.1.eigenvectorBasis i)) = 1 := by
    have hh := real_inner_self_eq_norm_sq (hA.1.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      hA.1.eigenvectorBasis.orthonormal.1 i, one_pow] using hh
  have hl := hlo ⇑(hA.1.eigenvectorBasis i)
  have hh := hhi ⇑(hA.1.eigenvectorBasis i)
  rw [hA.1.mulVec_eigenvectorBasis, dotProduct_smul, he] at hl hh
  simpa using And.intro hl hh

lemma positive_matrix_determinant_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b : ℝ) (ha : 0 ≤ a)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) :
    a ^ Fintype.card n ≤ A.det ∧ A.det ≤ b ^ Fintype.card n := by
  rw [hA.1.det_eq_prod_eigenvalues]
  constructor
  · simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ : n ↦ a)
      (g := hA.1.eigenvalues) (fun _ _ ↦ ha)
      (fun i _ ↦ (positive_matrix_eigenvalue_bounds A hA a b hlo hhi i).1)
  · simpa using Finset.prod_le_prod (s := Finset.univ) (f := hA.1.eigenvalues)
      (g := fun _ : n ↦ b) (fun i _ ↦ (hA.eigenvalues_pos i).le)
      (fun i _ ↦ (positive_matrix_eigenvalue_bounds A hA a b hlo hhi i).2)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_WeightedCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma weightedBaseMatrix_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b r R rho : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hrho : r ≤ rho) (hR : rho ≤ R)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) (v : n → ℝ) :
    (r/b) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (weightedBaseMatrix A rho *ᵥ v) ∧
    v ⬝ᵥ (weightedBaseMatrix A rho *ᵥ v) ≤ (R/a) * (v ⬝ᵥ v) := by
  have h := positive_matrix_inverse_bounds A hA a b ha hb hlo hhi v
  have hv := real_dot_self_nonneg v
  have hi : 0 ≤ v ⬝ᵥ (A⁻¹ *ᵥ v) := le_trans (by positivity) h.1
  simp only [weightedBaseMatrix, smul_mulVec, dotProduct_smul, smul_eq_mul]
  constructor
  · calc
      _ = r * (b⁻¹ * (v ⬝ᵥ v)) := by ring
      _ ≤ r * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := mul_le_mul_of_nonneg_left h.1 hr.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hrho hi
  · calc
      _ ≤ R * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := mul_le_mul_of_nonneg_right hR hi
      _ ≤ R * (a⁻¹ * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left h.2 ((hr.trans_le hrho).trans_le hR).le
      _ = _ := by ring

lemma determinant_density_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b r R rho : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hrho : r ≤ rho) (hR : rho ≤ R)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) :
    a ^ Fintype.card n / R^2 ≤ (Real.sqrt A.det / rho)^2 ∧
    (Real.sqrt A.det / rho)^2 ≤ b ^ Fintype.card n / r^2 := by
  have h := positive_matrix_determinant_bounds A hA a b ha.le hlo hhi
  have hrp : 0 < rho := hr.trans_le hrho
  have hRp : 0 < R := hrp.trans_le hR
  rw [div_pow, Real.sq_sqrt hA.det_pos.le]
  constructor
  · exact div_le_div₀ hA.det_pos.le h.1 (sq_pos_of_pos hrp) (by nlinarith)
  · exact div_le_div₀ (pow_nonneg hb.le _) h.2 (sq_pos_of_pos hr) (by nlinarith)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TargetWarpedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma roundProductMetric_inner (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    roundProductMetric.inner x v v =
      ‖(mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 v.1 : AmbientBase)‖^2 +
      ‖(mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2 : ℂ)‖^2 := by
  rw [roundProductMetric,ambientWeightedMetric_inner]
  let vb : AmbientBase := mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase)
    (Subtype.val : Base → AmbientBase) x.1 v.1
  let vc : ℂ := mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2
  change innerSL ℝ vb vb + 1^2 * inner ℝ vc vc = ‖vb‖^2 + ‖vc‖^2
  have he (w : AmbientBase) : innerSL ℝ w w = ‖w‖^2 := by
    change @inner ℝ AmbientBase _ w w = _
    exact real_inner_self_eq_norm_sq w
  rw [he]
  simp only [one_pow, one_mul, real_inner_self_eq_norm_sq]

lemma ambientWeightedMetric_comparison
    (B : Base → AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v)
    (q : Base → ℝ) (hq : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ q) (hpos : ∀ x, 0 < q x)
    (c C : ℝ)
    (hlo : ∀ x v, c*‖v‖^2 ≤ B x v v)
    (hhi : ∀ x v, B x v v ≤ C*‖v‖^2)
    (hql : ∀ x, c ≤ (q x)^2) (hqu : ∀ x, (q x)^2 ≤ C)
    (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    c * roundProductMetric.inner x v v ≤
      (ambientWeightedMetric B hB hs hp q hq hpos).inner x v v ∧
    (ambientWeightedMetric B hB hs hp q hq hpos).inner x v v ≤
      C * roundProductMetric.inner x v v := by
  rw [ambientWeightedMetric_inner,roundProductMetric_inner]
  let vb : AmbientBase := mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase)
    (Subtype.val : Base → AmbientBase) x.1 v.1
  let vc : ℂ := mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2
  change c * (‖vb‖^2 + ‖vc‖^2) ≤ B x.1 vb vb + q x.1 ^ 2 * inner ℝ vc vc ∧
    B x.1 vb vb + q x.1 ^ 2 * inner ℝ vc vc ≤ C * (‖vb‖^2 + ‖vc‖^2)
  rw [real_inner_self_eq_norm_sq]
  constructor
  · calc
      _ = c * _ + c * _ := mul_add _ _ _
      _ ≤ _ := add_le_add (hlo _ _) (mul_le_mul_of_nonneg_right (hql _) (sq_nonneg _))
  · calc
      _ ≤ C * _ + C * _ := add_le_add (hhi _ _)
          (mul_le_mul_of_nonneg_right (hqu _) (sq_nonneg _))
      _ = _ := (mul_add _ _ _).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_OriginalCoefficientComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma ambient_dot_self (v : AmbientBase) : (⇑v) ⬝ᵥ (⇑v) = ‖v‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, pow_two]

lemma original_coefficient_bounds
    (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (a b r R rho : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hrho : r ≤ rho) (hR : rho ≤ R)
    (hlo : ∀ v : AmbientBase, a * ‖v‖^2 ≤ ambientMatrixForm A v v)
    (hhi : ∀ v : AmbientBase, ambientMatrixForm A v v ≤ b * ‖v‖^2) :
    (∀ v : AmbientBase, (r/b) * ‖v‖^2 ≤ ambientMatrixForm (weightedBaseMatrix A rho) v v ∧
      ambientMatrixForm (weightedBaseMatrix A rho) v v ≤ (R/a) * ‖v‖^2) ∧
    a^5/R^2 ≤ (ambientCircleWeight A rho)^2 ∧
      (ambientCircleWeight A rho)^2 ≤ b^5/r^2 := by
  have hl (v : Fin 5 → ℝ) : a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
    simpa [ambientMatrixForm_dot, ← ambient_dot_self] using hlo (WithLp.toLp 2 v)
  have hh (v : Fin 5 → ℝ) : v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v) := by
    simpa [ambientMatrixForm_dot, ← ambient_dot_self] using hhi (WithLp.toLp 2 v)
  refine ⟨?_, ?_⟩
  · intro v
    simpa [ambientMatrixForm_dot, ambient_dot_self] using
      weightedBaseMatrix_bounds A hA a b r R rho ha hb hr hrho hR hl hh ⇑v
  · simpa [ambientCircleWeight] using
      determinant_density_bounds A hA a b r R rho ha hb hr hrho hR hl hh

lemma coefficient_comparison_constants_pos (a b r R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hR : 0 < R) :
    0 < min (r/b) (a^5/R^2) ∧ 0 < max (R/a) (b^5/r^2) := by
  constructor
  · exact lt_min (div_pos hr hb) (div_pos (pow_pos ha _) (sq_pos_of_pos hR))
  · exact lt_max_of_lt_left (div_pos hR ha)

lemma independentAmbientMetric_original_comparison
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r)
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hlo : ∀ x v, a * ‖v‖^2 ≤ ambientMatrixForm (A x) v v)
    (hhi : ∀ x v, ambientMatrixForm (A x) v v ≤ b * ‖v‖^2)
    (hrho : ∀ x, r ≤ rho x) (hR : ∀ x, rho x ≤ R)
    (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    min (r/b) (a^5/R^2) * roundProductMetric.inner x v v ≤
      (independentAmbientMetric A rho hA hp hr hrp).inner x v v ∧
    (independentAmbientMetric A rho hA hp hr hrp).inner x v v ≤
      max (R/a) (b^5/r^2) * roundProductMetric.inner x v v := by
  have h (y : Base) := original_coefficient_bounds (A y) (hp y) a b r R (rho y)
    ha hb hr0 (hrho y) (hR y) (hlo y) (hhi y)
  apply ambientWeightedMetric_comparison
  · intro y w
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖w‖)).trans ((h y).1 w).1
  · intro y w
    exact ((h y).1 w).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ‖w‖))
  · intro y
    exact (min_le_right _ _).trans (h y).2.1
  · intro y
    exact (h y).2.2.trans (le_max_right _ _)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereRadialProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped RealInnerProductSpace
noncomputable section

lemma sphere_radial_norm (x : Base) : ‖(x : AmbientBase)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using x.property

lemma sphereTangentProjection_orthogonal (x : Base) (v : AmbientBase) :
    ⟪(x : AmbientBase),sphereTangentProjection x v⟫ = 0 := by
  simp [sphereTangentProjection, inner_sub_right, real_inner_smul_right]

lemma sphereTangentProjection_norm (x : Base) (v : AmbientBase) :
    ‖sphereTangentProjection x v‖^2 + ⟪(x : AmbientBase),v⟫^2 = ‖v‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sphereTangentProjection, inner_sub_left, inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, sq_abs, sphere_radial_norm,mul_one,real_inner_comm v (x : AmbientBase)]
  ring

lemma sphereTangentProjection_restriction (x : Base) (v : AmbientBase) :
    sphereCovectorRestriction x (sphereTangentProjection x v) = sphereCovectorRestriction x v := by
  simp only [sphereTangentProjection,map_sub,map_smul,sphereCovectorRestriction_radial,
    smul_zero,sub_zero]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped RealInnerProductSpace
noncomputable section

lemma intrinsicAmbientMatrix_bounds (A : IntrinsicTensor) (a b : ℝ)
    (hlo : ∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
      a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v))
    (hhi : ∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2)
    (x : Base) (v : AmbientBase) :
    min a 1 * ‖v‖^2 ≤ ambientMatrixForm (intrinsicAmbientMatrix A x) v v ∧
    ambientMatrixForm (intrinsicAmbientMatrix A x) v v ≤ max b 1 * ‖v‖^2 := by
  have hl := hlo x (sphereTangentProjection x v) (sphereTangentProjection_orthogonal x v)
  have hh := hhi x (sphereTangentProjection x v) (sphereTangentProjection_orthogonal x v)
  rw [sphereTangentProjection_restriction] at hl hh
  rw [intrinsicAmbientMatrix_pairing, ← sphereTangentProjection_norm x v]
  constructor
  · calc
      _ = min a 1 * ‖sphereTangentProjection x v‖^2 + min a 1 * ⟪(x : AmbientBase),v⟫^2 := mul_add _ _ _
      _ ≤ a * ‖sphereTangentProjection x v‖^2 + 1 * ⟪(x : AmbientBase),v⟫^2 :=
        add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ b * ‖sphereTangentProjection x v‖^2 + 1 * ⟪(x : AmbientBase),v⟫^2 := by nlinarith
      _ ≤ max b 1 * ‖sphereTangentProjection x v‖^2 + max b 1 * ⟪(x : AmbientBase),v⟫^2 :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
      _ = _ := (mul_add _ _ _).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_TargetUniformProjection
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold Set MeasureTheory Yau.Jets
open scoped ENNReal NNReal ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

 theorem uniform_smooth_projection_nodal_measure (g0 : SmoothMetric) (L : ℝ≥0) (hL : 0 < L)
    (P : Manifold5 → F) (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ g : SmoothMetric,
      (∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
        g0.inner x v v ≤ (L:ℝ)^2*g.inner x v v) →
      ∀ (u : Manifold5 → ℝ) (Z : Set F), Z ⊆ P '' {x | u x = 0} →
        Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  obtain ⟨B,hB,hE⟩ := smooth_projection_energy_bound g0 P hP
  refine ⟨B*L,mul_pos hB hL,?_⟩
  intro g hcomp
  apply energy_projection_nodal_measure g P hP (B*L) (mul_pos hB hL)
  intro x v
  calc
    ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖^2 ≤ (B:ℝ)^2*g0.inner x v v := hE x v
    _ ≤ (B:ℝ)^2*((L:ℝ)^2*g.inner x v v) := by gcongr; exact hcomp x v
    _ = ((B*L:ℝ≥0):ℝ)^2*g.inner x v v := by simp only [NNReal.coe_mul] <;> ring

 theorem uniform_compact_coordinate_nodal_transfer (g0 : SmoothMetric) (L : ℝ≥0) (hL : 0 < L)
    (p : Manifold5) (a : ℝ) {b : ℝ} (hb : b ≠ 0) {K : Set (_root_.OAI.Yau.Jets.Coord × ℝ)} (hK : IsCompact K)
    (hKD : K ⊆ productChartDomain p a b) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ g : SmoothMetric,
      (∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
        g0.inner x v v ≤ (L:ℝ)^2*g.inner x v v) →
      ∀ (u : Manifold5 → ℝ) (Z : Set (_root_.OAI.Yau.Jets.Coord × ℝ)), Z ⊆ K →
        (∀ z ∈ Z, u (productChartInverse p a b z) = 0) →
        Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  obtain ⟨P,hP,hPK⟩ := compact_productChart_extension p a hb hK hKD
  obtain ⟨C,hC,hproj⟩ := uniform_smooth_projection_nodal_measure g0 L hL P hP
  refine ⟨C,hC,?_⟩
  intro g hcomp u Z hZ hzero
  apply hproj g hcomp
  intro z hz
  exact ⟨productChartInverse p a b z,hzero z hz,hPK z (hZ hz)⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_OriginalCoefficientNodalTransfer
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Yau.Jets
open scoped ContDiff NNReal ENNReal
noncomputable section

lemma uniform_original_coefficient_nodal_transfer
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r) (hR0 : 0 < R)
    (p : Manifold5) (s : ℝ) {t : ℝ} (ht : t ≠ 0) {K : Set (_root_.OAI.Yau.Jets.Coord × ℝ)}
    (hK : IsCompact K) (hKD : K ⊆ productChartDomain p s t) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
        (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
        (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
        (hrp : ∀ x, 0 < rho x),
        (∀ x v, a * ‖v‖^2 ≤ ambientMatrixForm (A x) v v) →
        (∀ x v, ambientMatrixForm (A x) v v ≤ b * ‖v‖^2) →
        (∀ x, r ≤ rho x) → (∀ x, rho x ≤ R) →
        ∀ (u : Manifold5 → ℝ) (Z : Set (_root_.OAI.Yau.Jets.Coord × ℝ)), Z ⊆ K →
          (∀ z ∈ Z, u (productChartInverse p s t z) = 0) →
          Measure.hausdorffMeasure (4:ℝ) Z ≤ (C:ℝ≥0∞)^4 *
            nodalMeasure (independentAmbientMetric A rho hA hp hr hrp) u := by
  let c := min (r/b) (a^5/R^2)
  have hc : 0 < c := (coefficient_comparison_constants_pos a b r R ha hb hr0 hR0).1
  let L : ℝ≥0 := ⟨(Real.sqrt c)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg c)⟩
  have hL : 0 < L := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  have he : (L:ℝ)^2 * c = 1 := by
    change ((Real.sqrt c)⁻¹)^2 * c = 1
    rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  dsimp only [c] at he
  obtain ⟨C,hC,hbound⟩ := uniform_compact_coordinate_nodal_transfer
    roundProductMetric L hL p s ht hK hKD
  refine ⟨C,hC,?_⟩
  intro A rho hA hp hr hrp hlo hhi hrho hR
  apply hbound
  intro x v
  have h := (independentAmbientMetric_original_comparison a b r R ha hb hr0
    A rho hA hp hr hrp hlo hhi hrho hR x v).1
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (L:ℝ))
  simpa only [← mul_assoc, he, one_mul] using hh

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_IntrinsicUniformNodal
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Yau.Jets
open scoped ContDiff NNReal ENNReal RealInnerProductSpace
noncomputable section

lemma uniform_intrinsic_coefficient_nodal_transfer_oai
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r) (hR0 : 0 < R)
    (p : Manifold5) (s : ℝ) {t : ℝ} (ht : t ≠ 0) {K : Set (_root_.OAI.Yau.Jets.Coord × ℝ)}
    (hK : IsCompact K) (hKD : K ⊆ productChartDomain p s t) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
        (hs : ∀ x v w, A x v w = A x w v)
        (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
        (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x),
        (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
          a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v)) →
        (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
          A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2) →
        (∀ x, r ≤ rho x) → (∀ x, rho x ≤ R) →
        ∀ (u : Manifold5 → ℝ) (Z : Set (_root_.OAI.Yau.Jets.Coord × ℝ)), Z ⊆ K →
          (∀ z ∈ Z, u (productChartInverse p s t z) = 0) →
          Measure.hausdorffMeasure (4:ℝ) Z ≤ (C:ℝ≥0∞)^4 *
            nodalMeasure (intrinsicWeightedMetric A hA hs hp rho hr hrp) u := by
  obtain ⟨C,hC,hbound⟩ := uniform_original_coefficient_nodal_transfer
    (min a 1) (max b 1) r R (lt_min ha zero_lt_one) (lt_max_of_lt_left hb) hr0 hR0
    p s ht hK hKD
  refine ⟨C,hC,?_⟩
  intro A hA hs hp rho hr hrp hlo hhi hrho hR
  exact hbound (intrinsicAmbientMatrix A) rho (intrinsicAmbientMatrix_smooth A hA)
    (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (fun x v ↦ (intrinsicAmbientMatrix_bounds A a b hlo hhi x v).1)
    (fun x v ↦ (intrinsicAmbientMatrix_bounds A a b hlo hhi x v).2) hrho hR

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer_oai := @OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer_oai
