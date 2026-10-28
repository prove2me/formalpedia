-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_spherical_fixed_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:42:01.400899+00:00
-- url     : https://prove2.me/submissions/a6f85383-4ffe-476c-bc87-b1e1f448f4a3

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_open_model
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_simple_stage
import Theorems.Thm_OAI_YauCounterexamples_fixed_metric_diagonal
import Theorems.Thm_OAI_YauCounterexamples_spherical_largeWitness_eventually

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_HmoDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma positiveFormOn_iff_unit (P : Submodule ℝ E) (T : CoordinateForm E) :
    positiveFormOn P T ↔ ∀ v ∈ P, ‖v‖ = 1 → 0 < T v v := by
  constructor
  · intro h v hv hn
    exact h v hv (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  · intro h v hv hv0
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    let w := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
    have hp := h w (P.smul_mem _ hv) hw
    have he : ‖v‖ • w = v := by simp [w, smul_smul, hn]
    have heq : T v v = ‖v‖^2 * T w w := by
      conv_lhs => rw [← he]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact mul_pos (sq_pos_of_ne_zero hn) hp

attribute [local instance] OAI.YauCounterexamples.hmoDualNorm
attribute [local instance] OAI.YauCounterexamples.hmoDualSpace
local instance hmoFormNorm_r7ed9d4_1 : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmoFormSpace_r7ed9d4_1 : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmoDerivNorm_r7ed9d4_1 : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance hmoDerivSpace_r7ed9d4_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
theorem isOpen_positiveFormOn (P : Submodule ℝ E) :
    IsOpen {T : CoordinateForm E | positiveFormOn P T} := by
  let S : Set E := {v | v ∈ P ∧ ‖v‖ = 1}
  have hS : IsCompact S := by
    have he : S = (P : Set E) ∩ sphere (0 : E) 1 := by
      ext v
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_sphere_zero_iff_norm]
      rfl
    rw [he]
    exact (isCompact_sphere 0 1).inter_left P.closed_of_finiteDimensional
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let B : Set (CoordinateForm E × S) := {p | p.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : CoordinateForm E × S => p.1) := continuous_fst
  have hv : Continuous (fun p : CoordinateForm E × S => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := isClosed_le ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext T
  rw [mem_ofPred_eq, positiveFormOn_iff_unit]
  simp only [mem_compl_iff, mem_image, B, mem_ofPred_eq]
  constructor
  · intro h
    rintro ⟨q,hq,hqT⟩
    subst T
    exact (not_le_of_gt (h q.2 q.2.property.1 q.2.property.2)) hq
  · intro h v hv hn
    by_contra hh
    apply h
    exact ⟨(T,⟨v,hv,hn⟩),not_lt.mp hh,rfl⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {P E F G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace ContinuousSmoothFamilyOn
variable {f : P → E → F} {U : Set E}
lemma value (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousOn (fun z : P × E => f z.1 z.2) (univ ×ˢ U) := by
  have hc := (continuousMultilinearCurryFin0 ℝ E F).continuous.continuousOn.comp
    (hf.jets 0) (mapsTo_univ _ _)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,iteratedFDeriv_zero_apply] using hc

lemma postcomp (hf : ContinuousSmoothFamilyOn f U) (g : F → G)
    (hg : ∀ p x, x ∈ U → ContDiffAt ℝ ∞ g (f p x)) :
    ContinuousSmoothFamilyOn (fun p x => g (f p x)) U := by
  classical
  refine ⟨fun p x hx => (hg p x hx).comp x (hf.smooth p x hx),fun n z hz => ?_⟩
  have hq : ∀ k, ContinuousWithinAt (fun z : P × E => iteratedFDeriv ℝ k g (f z.1 z.2))
      (univ ×ˢ U) z := fun k =>
    ((hg z.1 z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp_continuousWithinAt (f := fun w : P × E => f w.1 w.2) (hf.value z hz)
  have hc : ContinuousWithinAt (fun z : P × E =>
      (ftaylorSeries ℝ g (f z.1 z.2)).taylorComp (ftaylorSeries ℝ (f z.1) z.2) n)
      (univ ×ˢ U) z := by
    apply tendsto_finsetSum
    intro c _
    change ContinuousWithinAt (fun z : P × E =>
      (c.compAlongOrderedFinpartitionL ℝ E F G (iteratedFDeriv ℝ c.length g (f z.1 z.2)))
        (fun j => iteratedFDeriv ℝ (c.partSize j) (f z.1) z.2)) _ z
    exact ((c.compAlongOrderedFinpartitionL ℝ E F G).continuous.continuousAt.comp_continuousWithinAt
      (hq c.length)).eval (continuousWithinAt_pi.mpr (fun j => hf.jets (c.partSize j) z hz))
  apply hc.congr_of_eventuallyEq _ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact iteratedFDeriv_comp (hg w.1 w.2 hw.2) (hf.smooth w.1 w.2 hw.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  · exact iteratedFDeriv_comp (hg z.1 z.2 hz.2) (hf.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma prodMk {g : P → E → G} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) :
    ContinuousSmoothFamilyOn (fun p x => (f p x,g p x)) U := by
  refine ⟨fun p x hx => (hf.smooth p x hx).prodMk (hg.smooth p x hx),fun n => ?_⟩
  have hc := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => E) F G).continuous.continuousOn.comp
    ((hf.jets n).prodMk (hg.jets n)) (mapsTo_univ _ _)
  apply hc.congr
  intro z hz
  exact iteratedFDeriv_prodMk (hf.smooth z.1 z.2 hz.2) (hg.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma const (g : E → F) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) :
    ContinuousSmoothFamilyOn (fun _ : P => g) U := by
  refine ⟨fun _ => hg,fun n z hz => ?_⟩
  exact ((hg z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp_continuousWithinAt (f := Prod.snd)
    continuous_snd.continuousWithinAt

lemma scalar_const (a : P → F) (ha : Continuous a) :
    ContinuousSmoothFamilyOn (fun p (_ : E) => a p) U := by
  refine ⟨fun _ _ _ => contDiffAt_const,fun n => ?_⟩
  cases n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp (ha.comp continuous_fst) |>.continuousOn
  | succ n => simp only [iteratedFDeriv_succ_const]; exact continuousOn_const

lemma add {g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x+g p x) U :=
  (hf.prodMk hg).postcomp (fun z : F × F => z.1+z.2) (fun _ _ _ => by fun_prop)

lemma mul {f g : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x*g p x) U :=
  (hf.prodMk hg).postcomp (fun z : ℝ × ℝ => z.1*z.2) (fun _ _ _ => by fun_prop)

end ContinuousSmoothFamilyOn
end


section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)
lemma compactSmooth_continuousJets (n : ℕ) : Continuous
    (fun z : 𝓓_{K}(E,F) × E => iteratedFDeriv ℝ n z.1 z.2) := by
  have hc := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n).continuous.comp
    (continuous_fst : Continuous (Prod.fst : 𝓓_{K}(E,F) × E → 𝓓_{K}(E,F)))).eval continuous_snd
  change Continuous (fun z : 𝓓_{K}(E,F) × E =>
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n z.1) z.2) at hc
  simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using hc
lemma compactSmooth_family : ContinuousSmoothFamilyOn (fun f : 𝓓_{K}(E,F) => (f:E→F)) univ :=
  ⟨fun f _ _ => f.contDiff.contDiffAt,fun n => (compactSmooth_continuousJets K n).continuousOn⟩

end


section
open Set Filter Function Manifold
open scoped Topology ContDiff SchwartzMap
namespace ContinuousSmoothFamilyOn
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E}
lemma sum {ι : Type*} (s : Finset ι) (f : ι → P → E → F)
    (hf : ∀ i ∈ s, ContinuousSmoothFamilyOn (f i) U) :
    ContinuousSmoothFamilyOn (fun p x => ∑ i ∈ s, f i p x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalar_const (P:=P) (E:=E) (U:=U) (fun _ => (0 : F)) continuous_const
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma mono {f : P → E → F} (hf : ContinuousSmoothFamilyOn f U) {V : Set E} (hV : V ⊆ U) :
    ContinuousSmoothFamilyOn f V :=
  ⟨fun p x hx => hf.smooth p x (hV hx),fun n => (hf.jets n).mono (prod_mono_right hV)⟩
lemma of_local {f : P → E → F}
    (hf : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ContinuousSmoothFamilyOn f V) :
    ContinuousSmoothFamilyOn f U := by
  constructor
  · intro p x hx
    obtain ⟨V,hV,hxV,hfV⟩ := hf x hx
    exact hfV.smooth p x hxV
  · intro n z hz
    obtain ⟨V,hV,hzV,hfV⟩ := hf z.2 hz.2
    exact ((hfV.jets n (z) ⟨mem_univ _,hzV⟩).continuousAt
      ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _,hzV⟩)).continuousWithinAt
lemma congr {f g : P → E → F} (hU : IsOpen U) (hf : ContinuousSmoothFamilyOn f U)
    (he : ∀ p, EqOn (g p) (f p) U) : ContinuousSmoothFamilyOn g U := by
  have heq (p : P) (x : E) (hx : x ∈ U) : g p =ᶠ[𝓝 x] f p :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,he p⟩
  refine ⟨fun p x hx => (hf.smooth p x hx).congr_of_eventuallyEq (heq p x hx),fun n => ?_⟩
  apply (hf.jets n).congr
  intro z hz
  exact ((heq z.1 z.2 hz.2).iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
end ContinuousSmoothFamilyOn

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealMetricForm
attribute [local instance] OAI.YauCounterexamples.instIsTopologicalAddGroupContinuousLinearMapRealIdTangentSpaceModelWithCornersSelf_solutions
local instance instContinuousSMulRealContinuousLinearMapIdTangentSpaceModelWithCornersSelf_solutions_r7ed9d4_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance instIsTopologicalAddGroupTangentForm_r7ed9d4_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance instContinuousSMulRealTangentForm_r7ed9d4_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffAt_chartTrivMetricForm (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : ContDiffAt ℝ ∞ (chartTrivMetricForm g p) y := by
  let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
    fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
  have hx : (chartAt E p).symm y ∈ (chartFormTrivialization (E:=E) p).baseSet := by
    rw [chartFormTrivialization_baseSet]
    exact (chartAt E p).map_target hy
  have hg := ((chartFormTrivialization (E:=E) p).contMDiffAt_section_iff hx).mp
    (g.contMDiff ((chartAt E p).symm y))
  exact contMDiffAt_iff_contDiffAt.mp (hg.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))

variable (g : SmoothMetric E M) (p : M) (K : Compacts E)

omit [T2Space M] in
lemma isOpen_chartTensorPositive (hK : (K : Set E) ⊆ (chartAt E p).target) :
    IsOpen {H : 𝓓_{K}(E,MetricForm E) | chartTensorPositive g p K H} := by
  rw [isOpen_iff_mem_nhds]
  intro H hH
  apply K.isCompact.eventually_forall_of_forall_eventually
  intro y hy
  have hEval : Continuous (fun z : 𝓓_{K}(E,MetricForm E) × E => z.1 z.2) := by
    simpa only [univ_prod_univ,continuousOn_univ] using (compactSmooth_family (F:=MetricForm E) K).value
  have h₁ : ContinuousAt (fun z : 𝓓_{K}(E,MetricForm E) × E => chartTrivMetricForm g p z.2) (H,y) :=
    ContinuousAt.comp (f := Prod.snd) (g := chartTrivMetricForm g p) (x := (H,y))
      (contDiffAt_chartTrivMetricForm g p (hK hy)).continuousAt continuous_snd.continuousAt
  have h₂ : Continuous (fun z : 𝓓_{K}(E,MetricForm E) × E => symmetrizeMetricForm (z.1 z.2)) :=
    (symmetrizeMetricForm (E:=E)).continuous.comp hEval
  have hc := h₁.add h₂.continuousAt
  exact hc.eventually ((isOpen_positiveFormOn (⊤ : Submodule ℝ E)).mem_nhds (hH y hy))

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

variable (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
variable (ht : (chartAt E p).target = univ)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma smoothMetric_ext {g h : SmoothMetric E M}
    (he : ∀ x v w, g.inner x v w = h.inner x v w) : g=h := by
  have hi : g.inner=h.inner := funext (fun x => ContinuousLinearMap.ext (fun v =>
    ContinuousLinearMap.ext (fun w => he x v w)))
  cases g
  cases h
  cases hi
  rfl

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealMetricForm_1
lemma chartTensorMetric_ofMetric (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) :
    chartTensorMetric g₀ p K (ht ▸ subset_univ _) (chartTensorOfMetric g₀ p K ht g he)
      (chartTensorOfMetric_positive g₀ p K ht g he) = g := by
  apply smoothMetric_ext
  intro x v w
  by_cases hx : x ∈ (chartAt E p).source
  · change g₀.inner x v w + chartFormPush p (fun y =>
      symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y)) x v w = _
    rw [chartFormPush_pairing p hx]
    rw [chartTensorOfMetric_isSymm]
    change g₀.inner x v w + (chartMetricForm g p ((chartAt E p) x) -
      chartMetricForm g₀ p ((chartAt E p) x)) _ _ = _
    have hxy : (chartAt E p).symm ((chartAt E p) x) = x := (chartAt E p).left_inv hx
    have htxy := (chartAt E p).map_source hx
    rw [← chartFormTrivialization_metric g p htxy,← chartFormTrivialization_metric g₀ p htxy]
    rw [hxy]
    rw [sub_apply,sub_apply,chartFormTrivialization_pairing p hx,chartFormTrivialization_pairing p hx]
    have hx' : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hx
    simp only [Trivialization.symm_apply_apply_mk _ hx']
    ring
  · have hn : x ∉ (chartAt E p).symm '' (K : Set E) := by
      rintro ⟨y,hy,rfl⟩
      exact hx ((chartAt E p).map_target (ht ▸ mem_univ y))
    change g₀.inner x v w + chartFormPush p (fun y =>
      symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y)) x v w = _
    rw [chartFormPush_eq_zero_of_not_source p hx]
    simp only [zero_apply,add_zero,← he x hn]
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
section ChartTensorCoordinate
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal1
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal2
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal3
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal4
local instance chartTensorCoordLocal5_r7ed9d4_1 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal6_r7ed9d4_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal7_r7ed9d4_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance chartTensorCoordLocal8_r7ed9d4_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
lemma chartMetricForm_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : 𝓓_{K}(E,MetricForm E))
    (hH : chartTensorPositive g p K H) {y : E} (hy : y ∈ (chartAt E p).target) :
    chartMetricForm (chartTensorMetric g p K hK H hH) p y =
      chartMetricForm g p y + symmetrizeMetricForm (H y) := by
  rw [← chartFormTrivialization_metric _ p hy,← chartFormTrivialization_metric g p hy]
  ext v w
  rw [chartFormTrivialization_pairing p ((chartAt E p).map_target hy),add_apply,add_apply,
    chartFormTrivialization_pairing p ((chartAt E p).map_target hy)]
  change g.inner _ _ _ + chartFormPush p (fun y => symmetrizeMetricForm (H y)) _ _ _ = _
  congr 1
  rw [← chartFormTrivialization_pairing p ((chartAt E p).map_target hy),
    chartFormPush_trivialization p ((chartAt E p).map_target hy),(chartAt E p).right_inv hy]

lemma metricCoefficient_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : 𝓓_{K}(E,MetricForm E))
    (hH : chartTensorPositive g p K H) {y : E} (hy : y ∈ (chartAt E p).target)
    (i j : CoordIndex E) :
    metricCoefficients (chartTensorMetric g p K hK H hH) p y i j =
      metricCoefficients g p y i j + symmetrizeMetricForm (H y)
        (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  have h := congrArg (fun B : MetricForm E => B (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
    (chartMetricForm_chartTensorMetric g p K hK H hH hy)
  simpa only [add_apply,chartMetricForm_pairing,metricCoefficients,coordinateVector] using h

variable {P : Type*} [TopologicalSpace P]
lemma family_chartTensorMetric_main (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : P → 𝓓_{K}(E,MetricForm E))
    (hH : ∀ a, chartTensorPositive g p K (H a)) (hc : Continuous H) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (chartTensorMetric g p K hK (H a) (hH a)) p y i j)
      (chartAt E p).target := by
  have hfamily := compactSmooth_family (F:=MetricForm E) K
  have hparam : ContinuousSmoothFamilyOn (fun a => (H a : E → MetricForm E)) univ := by
    refine ⟨fun a => hfamily.smooth (H a),fun degree => ?_⟩
    exact (hfamily.jets degree).comp ((hc.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun pair hpair => ⟨mem_univ _,hpair.2⟩)
  have hf := hparam.postcomp
    (fun B : MetricForm E => symmetrizeMetricForm B (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
    (fun _ _ _ => by fun_prop)
  have hb := ContinuousSmoothFamilyOn.const (P:=P) (fun y => metricCoefficients g p y i j)
    (fun y hy => (contDiffOn_metricCoefficient g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy))
  apply (hb.add (hf.mono (subset_univ _))).congr (chartAt E p).open_target
  intro a y hy
  exact metricCoefficient_chartTensorMetric g p K hK (H a) (hH a) hy i j
end ChartTensorCoordinate

variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

local instance chartTensorCoordLocal13 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance

omit [T2Space M] in
lemma continuousSmoothFamily_from_chart (q : P → SmoothMetric E M) (g : SmoothMetric E M)
    (p : M) (S : Set M) (hS : IsClosed S) (hSp : S ⊆ (chartAt E p).source)
    (hq : ∀ i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y i j) (chartAt E p).target)
    (he : ∀ a x, x ∉ S → (q a).inner x = g.inner x) (r : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target := by
  classical
  apply ContinuousSmoothFamilyOn.of_local
  intro y hy
  by_cases hp : (chartAt E r).symm y ∈ (chartAt E p).source
  · obtain ⟨V,hV,hVo,hyV⟩ := mem_nhds_iff.mp (chart_overlap_nhds p r hy hp)
    have ht : ∀ z ∈ V, ContDiffAt ℝ ∞ (chartTransition p r) z :=
      fun z hz => contDiffAt_chartTransition p r (hV hz).1 (hV hz).2
    have hf (k l : CoordIndex E) : ContinuousSmoothFamilyOn
        (fun a z => metricCoefficients (q a) p (chartTransition p r z) k l) V := by
      have hmap : MapsTo (chartTransition p r) V (chartAt E p).target :=
        fun point hpoint => (chartAt E p).map_source (hV hpoint).2
      refine ⟨fun param point hpoint =>
        ((hq k l).smooth param _ (hmap hpoint)).comp point (ht point hpoint),
        fun degree pair hpair => ?_⟩
      have htransition : ContinuousOn (chartTransition p r) V :=
        fun point hpoint => (ht point hpoint).continuousAt.continuousWithinAt
      have hcomp : ContinuousOn (fun pair : P × E => (pair.1,chartTransition p r pair.2))
          (univ ×ˢ V) := continuousOn_fst.prodMk
        (htransition.comp continuousOn_snd (fun point hpoint => hpoint.2))
      have houter (order : ℕ) : ContinuousWithinAt
          (fun pair : P × E => iteratedFDeriv ℝ order
            (fun point => metricCoefficients (q pair.1) p point k l) (chartTransition p r pair.2))
          (univ ×ˢ V) pair :=
        (((hq k l).jets order).comp hcomp
          (fun point hpoint => ⟨mem_univ _,hmap hpoint.2⟩)) pair hpair
      have hinner (order : ℕ) : ContinuousWithinAt
          (fun pair : P × E => iteratedFDeriv ℝ order (chartTransition p r) pair.2)
          (univ ×ˢ V) pair :=
        ((ht pair.2 hpair.2).continuousAt_iteratedFDeriv
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl order)).comp_continuousWithinAt
          continuous_snd.continuousWithinAt
      have hjet : ContinuousWithinAt (fun pair : P × E =>
          (ftaylorSeries ℝ (fun point => metricCoefficients (q pair.1) p point k l)
            (chartTransition p r pair.2)).taylorComp (ftaylorSeries ℝ (chartTransition p r) pair.2)
            degree) (univ ×ˢ V) pair := by
        apply tendsto_finsetSum
        intro partition _
        change ContinuousWithinAt (fun pair : P × E =>
          (partition.compAlongOrderedFinpartitionL ℝ E E ℝ
            (iteratedFDeriv ℝ partition.length
              (fun point => metricCoefficients (q pair.1) p point k l) (chartTransition p r pair.2)))
            (fun index => iteratedFDeriv ℝ (partition.partSize index) (chartTransition p r) pair.2)) _ pair
        exact ((partition.compAlongOrderedFinpartitionL ℝ E E ℝ).continuous.continuousAt.comp_continuousWithinAt
          (houter partition.length)).eval
            (continuousWithinAt_pi.mpr (fun index => hinner (partition.partSize index)))
      apply hjet.congr_of_eventuallyEq _ ?_
      · filter_upwards [self_mem_nhdsWithin] with point hpoint
        exact iteratedFDeriv_comp ((hq k l).smooth point.1 _ (hmap hpoint.2)) (ht point.2 hpoint.2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl degree)
      · exact iteratedFDeriv_comp ((hq k l).smooth pair.1 _ (hmap hpair.2)) (ht pair.2 hpair.2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl degree)
    have hT (k l : CoordIndex E) : ContinuousSmoothFamilyOn
        (fun _ : P => fun z => coordinateTransitionMatrix p r z k l) V := by
      apply ContinuousSmoothFamilyOn.const
      intro z hz
      simp only [coordinateTransitionMatrix,LinearMap.toMatrix_apply]
      change ContDiffAt ℝ ∞ (fun z => (Module.finBasis ℝ E).repr
        ((fderiv ℝ (chartTransition p r) z) (Module.finBasis ℝ E l)) k) z
      exact ((Module.finBasis ℝ E).coord k).toContinuousLinearMap.contDiff.contDiffAt.comp z
        (((ht z hz).fderiv_right (by simp)).clm_apply contDiffAt_const)
    have htensor := ContinuousSmoothFamilyOn.sum Finset.univ (fun l => fun a z =>
        (∑ k, coordinateTransitionMatrix p r z k i *
          metricCoefficients (q a) p (chartTransition p r z) k l) * coordinateTransitionMatrix p r z l j)
      (fun l _ => (ContinuousSmoothFamilyOn.sum Finset.univ _
        (fun k _ => (hT k i).mul (hf k l))).mul (hT l j))
    refine ⟨V,hVo,hyV,htensor.congr hVo ?_⟩
    intro a z hz
    exact congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_change (q a) p r (hV hz).1 (hV hz).2)
  · have hn : (chartAt E r).symm y ∉ S := fun hn => hp (hSp hn)
    have hn' := ((chartAt E r).continuousAt_symm hy).eventually (hS.isOpen_compl.mem_nhds hn)
    obtain ⟨V,hV,hVo,hyV⟩ := mem_nhds_iff.mp (inter_mem ((chartAt E r).open_target.mem_nhds hy) hn')
    refine ⟨V,hVo,hyV,?_⟩
    have hf := ContinuousSmoothFamilyOn.const (P:=P) (fun z => metricCoefficients g r z i j)
      (U:=V) (fun z hz => (contDiffOn_metricCoefficient g r i j).contDiffAt
        ((chartAt E r).open_target.mem_nhds (hV hz).1))
    apply hf.congr hVo
    intro a z hz
    exact congrArg (fun B => B (coordinateVector r z i) (coordinateVector r z j))
      (he a ((chartAt E r).symm z) (hV hz).2)
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal9
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal10
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal11
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal12
local instance chartTensorCoordLocal14_r7ed9d4_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal15_r7ed9d4_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance chartTensorCoordLocal16_r7ed9d4_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
lemma family_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : P → 𝓓_{K}(E,MetricForm E))
    (hH : ∀ a, chartTensorPositive g p K (H a)) (hc : Continuous H)
    (r : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (chartTensorMetric g p K hK (H a) (hH a)) r y i j)
      (chartAt E r).target := by
  apply continuousSmoothFamily_from_chart _ g p ((chartAt E p).symm '' (K : Set E))
  · exact (K.isCompact.image_of_continuousOn ((chartAt E p).continuousOn_symm.mono hK)).isClosed
  · rintro x ⟨y,hy,rfl⟩
    exact (chartAt E p).map_target (hK hy)
  · exact family_chartTensorMetric_main g p K hK H hH hc
  · intro a x hx
    change g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H a y)) x = g.inner x
    suffices hh : chartFormPush p (fun y => symmetrizeMetricForm (H a y)) x = 0 by
      rw [hh]
      ext v w
      change g.inner x v w + (0 : ℝ) = g.inner x v w
      exact add_zero _
    by_cases hxp : x ∈ (chartAt E p).source
    · apply chartFormPush_zero
      have hy : (chartAt E p) x ∉ (K : Set E) := by
        intro hy
        exact hx ⟨(chartAt E p) x,hy,(chartAt E p).left_inv hxp⟩
      simp [manifoldChartPush,hxp,(H a).zero_on_compl hy]
    · exact chartFormPush_eq_zero_of_not_source p hxp

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_SphericalOpenFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
local instance sphericalOpenFormNorm_r7ed9d4_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalOpenFormSpace_r7ed9d4_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
lemma sphericalPositiveSet_isOpen (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    IsOpen (sphericalPositiveSet g₀) :=
  isOpen_chartTensorPositive g₀ sourcePole sphericalTensorSupport
    ((sphere_chart_target sourcePole).symm ▸ subset_univ _)
lemma sphericalTensorMetric_of (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3))
    (he : sphericalExterior g₀ g (3/10)) :
    sphericalTensorMetric g₀ ⟨sphericalTensorOf g₀ g he,sphericalTensorOf_positive g₀ g he⟩=g :=
  chartTensorMetric_ofMetric g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole)
    g (sphericalExterior_support le_rfl he)
lemma sphericalTensorMetric_family (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (r : Sphere 3) (i j : CoordIndex (Euclidean 3)) :
    ContinuousSmoothFamilyOn
      (fun H y => metricCoefficients (sphericalTensorMetric g₀ H) r y i j)
      (chartAt (Euclidean 3) r).target :=
  family_chartTensorMetric g₀ sourcePole sphericalTensorSupport
    ((sphere_chart_target sourcePole).symm ▸ subset_univ _) Subtype.val
    (fun H => H.property) continuous_subtype_val r i j

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactSmoothJetMap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_of_uniform_jets (u : ℕ → E → F) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (G : (m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F))
    (hG : ∀ m, TendstoUniformly (fun j => iteratedFDeriv ℝ m (u j)) (G m) atTop) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧
      ∀ m, iteratedFDeriv ℝ m f = G m := by
  let f : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x m => G m x
  have hp : HasFTaylorSeriesUpTo ∞ f p := by
    refine ⟨fun _ => rfl, ?_, fun m _ => (G m).continuous⟩
    intro m hm x
    have ht : TendstoUniformly
      (fun j y => (iteratedFDeriv ℝ (m+1) (u j) y).curryLeft)
      (fun y => (G (m+1) y).curryLeft) atTop := by
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).isometry.uniformContinuous
        |>.comp_tendstoUniformly (hG (m+1))
    exact hasFDerivAt_of_tendstoUniformly ht
      (fun j y => (hu j).ftaylorSeries.fderiv m hm y)
      (fun y => (hG m).tendsto_at y) x
  refine ⟨f,hp.contDiff,fun m => ?_⟩
  funext x
  exact (hp.eq_iteratedFDeriv (m:=m) (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) x).symm


end

open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)

theorem compactSmoothJetMap_isClosed : IsClosed (range (compactSmoothJetMap (F:=F) K)) := by
  let : ∀ m : ℕ, FirstCountableTopology (E →ᵇ (E [×m]→L[ℝ] F)) := fun _ => inferInstance
  let : FirstCountableTopology ((m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F)) := inferInstance
  apply IsSeqClosed.isClosed
  intro v G hv hlim
  choose u hu using hv
  have hG : ∀ m, TendstoUniformly (fun j => iteratedFDeriv ℝ m (u j)) (G m) atTop := by
    intro m
    have ht := (continuous_apply m).tendsto G |>.comp hlim
    have htu : Tendsto (fun j => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ m (u j))
        atTop (𝓝 (G m)) := by
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      funext j
      exact congrArg (fun w => w m) (hu j)
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu
  obtain ⟨f,hf,hfj⟩ := smooth_of_uniform_jets (fun j => u j) (fun j => (u j).contDiff) G hG
  have hzero : EqOn f 0 Kᶜ := by
    intro x hx
    have hconst : ∀ j, iteratedFDeriv ℝ 0 (u j) x = 0 := by
      intro j
      ext z
      simp only [iteratedFDeriv_zero_apply]
      exact (u j).zero_on_compl hx
    have hGX : G 0 x = 0 := tendsto_nhds_unique ((hG 0).tendsto_at x)
      (by simpa only [hconst] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E [×0]→L[ℝ] F)) atTop (𝓝 0)))
    have hh := congrArg (fun h : E → E [×0]→L[ℝ] F => h x) (hfj 0)
    rw [hGX] at hh
    have he := congrArg (fun p : E [×0]→L[ℝ] F => p (fun _ => 0)) hh
    simpa using he
  refine ⟨⟨f,hf,hzero⟩,?_⟩
  funext m
  apply BoundedContinuousFunction.ext
  intro x
  rw [compactSmoothJetMap, ContinuousLinearMap.pi_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrArg (fun h : E → E [×m]→L[ℝ] F => h x) (hfj m)

variable [CompleteSpace F]

theorem compactSmooth_complete : CompleteSpace 𝓓_{K}(E,F) := by
  apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜:=ℝ)
    (n:=⊤) (K:=K)).isUniformInducing.completeSpace
  exact (compactSmoothJetMap_isClosed (F:=F) K).isComplete



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_SphericalFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance sphericalFixedFormComplete : CompleteSpace (MetricForm (Euclidean 3)) := by
  let : ContinuousSMul ℝ (Euclidean 3) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (Euclidean 3 →L[ℝ] ℝ) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Euclidean 3 →L[ℝ] ℝ) := ContinuousLinearMap.instCompleteSpace
  exact ContinuousLinearMap.instCompleteSpace

lemma sphericalStageRadius_bounds (n : ℕ) :
    1/5 ≤ sphericalStageRadius n ∧ sphericalStageRadius n < sphericalStageRadius (n+1) ∧
      sphericalStageRadius (n+1)<3/10 := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0<10*((n:ℝ)+1) := by positivity
  have h2 : 0<10*((n:ℝ)+1+1) := by positivity
  dsimp [sphericalStageRadius]
  rw [Nat.cast_add,Nat.cast_one]
  constructor
  · have hh : 1/(10*((n:ℝ)+1)) ≤ 1/10 := (div_le_div_iff₀ h1 (by norm_num)).mpr (by nlinarith)
    linarith
  constructor
  · have hh : 1/(10*((n:ℝ)+1+1)) < 1/(10*((n:ℝ)+1)) :=
      (div_lt_div_iff₀ h2 h1).mpr (by linarith)
    linarith
  · have hh := div_pos (show (0:ℝ)<1 by norm_num) h2
    linarith

local instance sphericalFixedFormNorm_r7ed9d4_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalFixedFormSpace_r7ed9d4_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
theorem exists_spherical_fixed_witnesses_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
    ∃ g ∈ N, ∀ n : ℕ, SphericalLargeWitness g ((n:ℝ)+1) ((n:ℝ)+1) := by
  classical
  let : MetricSpace SphericalTensor := compactSmoothMetricSpace sphericalTensorSupport
  let : CompleteSpace SphericalTensor := compactSmooth_complete sphericalTensorSupport
  obtain ⟨O,hO,h0O,hON⟩ := exists_spherical_open_model g₀ hg₀ N hN
  let P : ℕ → Set SphericalTensor := fun n =>
    {H | ∃ g : SmoothMetric (Euclidean 3) (Sphere 3), ∃ he : sphericalExterior g₀ g (sphericalStageRadius n),
      H=sphericalTensorOf g₀ g (sphericalExterior_mono
        ((sphericalStageRadius_bounds n).2.1.trans (sphericalStageRadius_bounds n).2.2).le he) ∧ H∈O}
  let W : ℕ → Set SphericalTensor := fun n =>
    {H | ∃ hp : H∈sphericalPositiveSet g₀,
      SphericalLargeWitness (sphericalTensorMetric g₀ ⟨H,hp⟩) ((n:ℝ)+1) ((n:ℝ)+1)}
  have hstep : ∀ n, ∀ H ∈ P n, ∀ U : Set SphericalTensor, IsOpen U → H∈U →
      ∃ K∈P (n+1), K∈U ∧ ∃ V : Set SphericalTensor, IsOpen V ∧ K∈V ∧ V⊆W n := by
    intro n H hH U hU hHU
    obtain ⟨g,he,rfl,hgO⟩ := hH
    let e := sphericalExterior_mono
      ((sphericalStageRadius_bounds n).2.1.trans (sphericalStageRadius_bounds n).2.2).le he
    obtain ⟨hp,hgN,hgood⟩ := hON _ hgO
    have hmetric : sphericalTensorMetric g₀ ⟨sphericalTensorOf g₀ g e,hp⟩=g := sphericalTensorMetric_of g₀ g e
    rw [hmetric] at hgood
    let R := sphericalStageRadius n
    let C := sphericalStageRadius (n+1)
    have hR := (sphericalStageRadius_bounds n).1
    have hRC : R<C := (sphericalStageRadius_bounds n).2.1
    have hC : C<3/10 := (sphericalStageRadius_bounds n).2.2
    obtain ⟨k,hkM,hk3,h,eh,hhU,u,hu,hu0,hue,hreg,hsimple,hscore⟩ :=
      exists_spherical_simple_stage g₀ hg₀ g hgood.1 (R:=R)
        (t:=(5*R+C)/6) (s:=(4*R+2*C)/6) (r:=(3*R+3*C)/6)
        (a:=(2*R+4*C)/6) (b:=(R+5*C)/6) (c:=C) hR
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) hC he hgood.2 ((n:ℝ)+1) (n+3) (U∩O) (hU.inter hO) ⟨hHU,hgO⟩
    let eh' := sphericalExterior_mono hC.le eh
    let K := sphericalTensorOf g₀ h eh'
    let z : SphericalPositiveTensor g₀ := ⟨K,sphericalTensorOf_positive g₀ h eh'⟩
    have hqz : sphericalTensorMetric g₀ z=h := sphericalTensorMetric_of g₀ h eh'
    have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hkreal : (n:ℝ)+3≤k := by exact_mod_cast hkM
    have hk3real : (3:ℝ)≤k := by exact_mod_cast hk3
    have hepos : 0 < sphereFrequency k := by dsimp [sphereFrequency]; positivity
    have heB : (n:ℝ)+1 < sphereFrequency k := by dsimp [sphereFrequency]; nlinarith
    have heD : sphereFrequency k<2*(k:ℝ)^2 := by dsimp [sphereFrequency]; nlinarith
    have hev := spherical_largeWitness_eventually (sphericalTensorMetric g₀)
      (sphericalTensorMetric_family g₀) z k hk3 (sphereFrequency k) hepos u hu hu0
      (by simpa only [hqz] using hue) hreg (by simpa only [hqz] using hsimple)
      ((n:ℝ)+1) ((n:ℝ)+1) heB heD hscore
    obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
    refine ⟨K,⟨h,eh,rfl,hhU.2⟩,hhU.1,Subtype.val '' V,
      (sphericalPositiveSet_isOpen g₀).isOpenMap_subtype_val V hVo,⟨z,hzV,rfl⟩,?_⟩
    rintro H ⟨v,hv,rfl⟩
    exact ⟨v.property,hV hv⟩
  have hzP : (0:SphericalTensor)∈P 0 := by
    refine ⟨g₀,(fun _ _ => rfl),?_,h0O⟩
    exact (sphericalTensorOf_zero g₀).symm
  obtain ⟨H,hHO,hHW⟩ := fixed_metric_diagonal P W hstep 0 hzP hO h0O
  obtain ⟨hp,hgN,hgood⟩ := hON H hHO
  refine ⟨sphericalTensorMetric g₀ ⟨H,hp⟩,hgN,?_⟩
  intro n
  exact (hHW n).choose_spec

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_spherical_fixed_witnesses_oai := @OAI.YauCounterexamples.exists_spherical_fixed_witnesses_oai
