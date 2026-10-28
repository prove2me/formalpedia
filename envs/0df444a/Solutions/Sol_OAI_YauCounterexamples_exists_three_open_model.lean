-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_open_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:44:56.135259+00:00
-- url     : https://prove2.me/submissions/f48f9234-b1ae-49c8-8acd-61794440eace

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011

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
local instance hmoFormNorm_r4127fe_1 : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmoFormSpace_r4127fe_1 : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmoDerivNorm_r4127fe_1 : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance hmoDerivSpace_r4127fe_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
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
lemma neg {f : P → E → F} (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => -f p x) U :=
  hf.postcomp (fun z : F => -z) (fun _ _ _ => contDiffAt_id.neg)
lemma sub {f g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x-g p x) U := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
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
local instance instContinuousSMulRealContinuousLinearMapIdTangentSpaceModelWithCornersSelf_solutions_r4127fe_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance instIsTopologicalAddGroupTangentForm_r4127fe_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance instContinuousSMulRealTangentForm_r4127fe_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
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
local instance chartTensorCoordLocal5_r4127fe_1 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal6_r4127fe_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal7_r4127fe_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance chartTensorCoordLocal8_r4127fe_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
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
local instance chartTensorCoordLocal14_r4127fe_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal15_r4127fe_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance chartTensorCoordLocal16_r4127fe_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ContinuousFamilyEventuallyTest
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma continuousFamily_eventually_test (q : P → SmoothMetric E M)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target)
    (a₀ : P) (t : CoordinateTest E M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in 𝓝 a₀, ∀ y ∈ t.compactSet,
      ‖iteratedFDeriv ℝ t.order (fun z => metricCoefficients (q a) t.center z t.row t.column -
        metricCoefficients (q a₀) t.center z t.row t.column) y‖ < ε := by
  apply t.isCompact.eventually_forall_of_forall_eventually
  intro y hy
  have hf := (hq t.center t.row t.column).sub (ContinuousSmoothFamilyOn.const
    (fun y => metricCoefficients (q a₀) t.center y t.row t.column)
    (fun y hy => (hq t.center t.row t.column).smooth a₀ y hy))
  have hc := (hf.jets t.order).continuousAt (x := (a₀,y))
    ((isOpen_univ.prod (chartAt E t.center).open_target).mem_nhds ⟨mem_univ _,t.inTarget hy⟩)
  apply hc.norm.eventually (gt_mem_nhds ?_)
  simp only [sub_self,iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
  exact hε
lemma continuousFamily_eventually_neighborhood (q : P → SmoothMetric E M)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target)
    (a₀ : P) {N : Set (SmoothMetric E M)} (hN : IsSmoothNeighborhood (q a₀) N) :
    ∀ᶠ a in 𝓝 a₀, q a ∈ N := by
  obtain ⟨tests,ε,hε,hN⟩ := hN
  have hh : ∀ᶠ a in 𝓝 a₀, ∀ t ∈ tests, ∀ y ∈ t.compactSet,
      ‖iteratedFDeriv ℝ t.order (fun z => metricCoefficients (q a) t.center z t.row t.column -
        metricCoefficients (q a₀) t.center z t.row t.column) y‖ < ε := by
    apply (Filter.eventually_all_finite tests.finite_toSet).mpr
    intro t ht
    exact continuousFamily_eventually_test q hq a₀ t hε
  exact hh.mono (fun a ha => hN (q a) ha)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormNorm
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormSpace
lemma threePositiveSet_isOpen (R : ℝ) : IsOpen (threePositiveSet R) :=
  isOpen_chartTensorPositive threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _)
lemma threeTensorMetric_of (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) :
    threeTensorMetric R ⟨threeTensorOf R g he,threeTensorOf_positive R g he⟩=g :=
  chartTensorMetric_ofMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
lemma threeTensorMetric_zero (R : ℝ) : threeTensorMetric R ⟨0,threePositive_zero R⟩=threeBackgroundMetric := by
  simpa only [threeTensorOf_zero] using threeTensorMetric_of R threeBackgroundMetric (fun _ _ => rfl)
lemma threeTensorMetric_family (R : ℝ) (r : ThreeManifold) (i j : CoordIndex ThreeModel) :
    ContinuousSmoothFamilyOn (fun H y => metricCoefficients (threeTensorMetric R H) r y i j)
      (chartAt ThreeModel r).target :=
  family_chartTensorMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _) Subtype.val
    (fun H => H.property) continuous_subtype_val r i j
lemma exists_three_open_model_oai (R : ℝ) (N : Set (SmoothMetric ThreeModel ThreeManifold))
    (hN : IsSmoothNeighborhood threeBackgroundMetric N) :
    ∃ O : Set (ThreeTensor R), IsOpen O ∧ 0∈O ∧
      ∀ H∈O, ∃ hp : H∈threePositiveSet R, threeTensorMetric R ⟨H,hp⟩∈N := by
  let z₀ : ThreePositiveTensor R := ⟨0,threePositive_zero R⟩
  have htest : IsSmoothNeighborhood (threeTensorMetric R z₀) N := by
    rw [show threeTensorMetric R z₀=threeBackgroundMetric from threeTensorMetric_zero R]
    exact hN
  have hev := continuousFamily_eventually_neighborhood (threeTensorMetric R)
    (threeTensorMetric_family R) z₀ htest
  obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
  refine ⟨Subtype.val '' V,(threePositiveSet_isOpen R).isOpenMap_subtype_val V hVo,
    ⟨z₀,hzV,rfl⟩,?_⟩
  rintro H ⟨z,hz,rfl⟩
  exact ⟨z.property,hV hz⟩
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_open_model_oai := @OAI.YauCounterexamples.exists_three_open_model_oai
