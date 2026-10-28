-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_local_metric_radial_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:08:57.286423+00:00
-- url     : https://prove2.me/submissions/3ccfad3d-c275-47e5-93de-a21c40e9f4f9

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PathExtension
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma pathExtension_coe (u : C(unitInterval, E)) (s : unitInterval) :
    pathExtension u s = u s := by
  simp only [pathExtension_apply, projIcc_val]

lemma hasDerivAt_volterra_extension (u : C(unitInterval, E)) (s : ℝ) :
    HasDerivAt (fun r => ∫ t in 0..r, pathExtension u t) (pathExtension u s) s := by
  apply integral_hasDerivAt_right
  · exact (pathExtension u).continuous.intervalIntegrable _ _
  · exact (pathExtension u).continuous.stronglyMeasurableAtFilter _ _
  · exact (pathExtension u).continuous.continuousAt

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FlowParameters
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
open scoped Topology ContDiff
universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.superpositionContinuousNorm
attribute [local instance] OAI.YauCounterexamples.superpositionContinuousSpace
attribute [local instance] OAI.YauCounterexamples.superpositionContinuousMapNorm
attribute [local instance] OAI.YauCounterexamples.superpositionContinuousMapSpace
lemma hasFDerivAt_superposition {f : E → F} (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    HasFDerivAt (superposition f hf.continuous)
      (continuousMapApply ⟨(fderiv ℝ f) ∘ u, (hf.continuous_fderiv (by simp)).comp u.continuous⟩) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc := (isCompact_closedBall (0 : E) (‖u‖ + 1)).uniformContinuousOn_of_continuous
    (hf.continuous_fderiv (by simp)).continuousOn
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let r := min δ 1
  have hr : 0 < r := lt_min hδ zero_lt_one
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const
    (show ‖(0 : C(K, E))‖ < r by simpa using hr)] with h hh
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hx : u x ∈ closedBall (0 : E) (‖u‖ + 1) := by
    rw [mem_closedBall, dist_zero_right]
    exact (u.norm_coe_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have hs : ball (u x) r ⊆ closedBall (0 : E) (‖u‖ + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    calc ‖y‖ ≤ ‖y - u x‖ + ‖u x‖ := by simpa only [add_comm] using norm_le_insert' y (u x)
         _ ≤ 1 + ‖u‖ := add_le_add (by simpa only [dist_eq_norm] using (mem_ball.mp hy).le.trans (min_le_right δ 1))
           (u.norm_coe_le_norm x)
         _ = ‖u‖ + 1 := add_comm _ _
  have hderiv : ∀ y ∈ ball (u x) r, ‖fderiv ℝ f y - fderiv ℝ f (u x)‖ ≤ ε := by
    intro y hy
    simpa only [dist_eq_norm] using (hbound y (hs hy) (u x) hx
      ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
  have hhx : u x + h x ∈ ball (u x) r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (h.norm_coe_le_norm x).trans_lt hh
  have hb := (convex_ball (u x) r).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf.differentiable (by simp) y) hderiv (mem_ball_self hr) hhx
  simpa only [ContinuousMap.sub_apply, ContinuousMap.add_apply, superposition_apply,
      continuousMapApply_apply, ContinuousMap.coe_mk, Function.comp_apply, add_sub_cancel_left]
    using (by simpa only [add_sub_cancel_left] using hb :
      ‖f (u x + h x) - f (u x) - fderiv ℝ f (u x) (h x)‖ ≤ ε * ‖h x‖).trans
        (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm x) hε.le)

attribute [local instance] OAI.YauCounterexamples.superpositionMapNorm
attribute [local instance] OAI.YauCounterexamples.superpositionMapSpace
lemma contDiff_nat_superposition (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → F) (hf : ContDiff ℝ ∞ f), ContDiff ℝ n (superposition (K := K) f hf.continuous) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    exact contDiff_zero.mpr (Differentiable.continuous (fun u => (hasFDerivAt_superposition hf u).differentiableAt))
  | succ n ih =>
    intro F _ _ f hf
    rw [show (↑(n + 1) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun u => continuousMapApplyCLM (superposition (fderiv ℝ f)
      (hf.continuous_fderiv (by simp)) u), ?_, ?_⟩
    · exact (continuousMapApplyCLM (K := K) (E := E) (F := F)).contDiff.comp
        (ih (fderiv ℝ f) (hf.fderiv_right (by simp)))
    · intro u
      exact hasFDerivAt_superposition hf u

theorem contDiff_superposition {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superposition (K := K) f hf.continuous) := by
  rw [contDiff_infty]
  exact fun n => contDiff_nat_superposition n f hf


end

section
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem smooth_inverse_on {f : X → X} (hf : ContDiff ℝ ∞ f) (x : X)
    (D : X ≃L[ℝ] X) (hd : HasFDerivAt f (D : X →L[ℝ] X) x) :
    ∃ (e : OpenPartialHomeomorph X X) (W : Set X),
      (e : X → X) = f ∧ x ∈ e.source ∧ IsOpen W ∧ f x ∈ W ∧ W ⊆ e.target ∧
      ContDiffOn ℝ ∞ e.symm W := by
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  have hex : x ∈ e.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hefx : f x ∈ e.target := e.map_source hex
  have hunit : ∀ᶠ z in 𝓝 x, IsUnit (fderiv ℝ f z) := by
    apply (hf.continuous_fderiv (by simp)).continuousAt.eventually
    apply Units.isOpen.mem_nhds
    rw [hd.fderiv]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr D.bijective
  have hu : ∀ᶠ y in 𝓝 (f x), IsUnit (fderiv ℝ f (e.symm y)) := by
    have hc : Tendsto e.symm (𝓝 (f x)) (𝓝 x) := by
      have hc := e.symm.continuousAt hefx
      change Tendsto e.symm (𝓝 (f x)) (𝓝 (e.symm (f x))) at hc
      have he : e.symm (f x) = x := e.left_inv hex
      rwa [he] at hc
    exact hc.eventually hunit
  obtain ⟨W, hWsub, hWo, hW⟩ := _root_.mem_nhds_iff.mp (hu.and (e.open_target.mem_nhds hefx))
  refine ⟨e, W, rfl, hex, hWo, hW, fun y hy => (hWsub hy).2, ?_⟩
  intro y hy
  obtain ⟨huy, hyt⟩ := hWsub hy
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp huy
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ f (e.symm y))
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have ha : HasFDerivAt (e : X → X) (A : X →L[ℝ] X) (e.symm y) :=
    hf.differentiable (by simp) (e.symm y) |>.hasFDerivAt
  exact (e.contDiffAt_symm hyt ha (hf.contDiffAt)).contDiffWithinAt

end

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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma flowIntegralMap_smooth {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (flowIntegralMap V hV.continuous) := by
  refine contDiff_fst.prodMk ((contDiff_snd.sub ?_).sub ?_)
  · exact (ContinuousLinearMap.const ℝ unitInterval : E →L[ℝ] C(unitInterval, E)).contDiff.comp contDiff_fst.snd
  · exact contDiff_fst.fst.smul (volterra.contDiff.comp ((contDiff_superposition hV).comp contDiff_snd))

lemma flowIntegralMap_derivative {V : E → E} (hV : ContDiff ℝ ∞ V) (x : E) :
    HasFDerivAt (flowIntegralMap V hV.continuous)
      (flowIntegralDerivative (volterra (superposition V hV.continuous (ContinuousMap.const unitInterval x))) :
        FlowParameters E →L[ℝ] FlowParameters E) ((0,x), ContinuousMap.const unitInterval x) := by
  let p : FlowParameters E := ((0,x), ContinuousMap.const unitInterval x)
  let P := ContinuousLinearMap.fst ℝ (ℝ × E) C(unitInterval, E)
  let U := ContinuousLinearMap.snd ℝ (ℝ × E) C(unitInterval, E)
  let T := (ContinuousLinearMap.fst ℝ ℝ E).comp P
  let X := (ContinuousLinearMap.snd ℝ ℝ E).comp P
  have hQ := volterra.hasFDerivAt.comp p
    (((contDiff_superposition hV).differentiable (by simp) (U p)).hasFDerivAt.comp p U.hasFDerivAt)
  have hh := P.hasFDerivAt (x := p) |>.prodMk
    ((U.hasFDerivAt.sub ((ContinuousLinearMap.const ℝ unitInterval).hasFDerivAt.comp p X.hasFDerivAt)).sub
      (T.hasFDerivAt.smul hQ))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q s <;> simp [flowIntegralDerivative, p, P, U, T, X]

theorem smooth_integral_paths {V : E → E} (hV : ContDiff ℝ ∞ V) (x : E) :
    ∃ (O : Set (ℝ × E)) (u : (ℝ × E) → C(unitInterval, E)),
      IsOpen O ∧ (0,x) ∈ O ∧ ContDiffOn ℝ ∞ u O ∧ u (0,x) = ContinuousMap.const unitInterval x ∧
      ∀ p ∈ O, u p = ContinuousMap.const unitInterval p.2 + p.1 • volterra (superposition V hV.continuous (u p)) := by
  let p : FlowParameters E := ((0,x), ContinuousMap.const unitInterval x)
  let D := flowIntegralDerivative (volterra (superposition V hV.continuous (ContinuousMap.const unitInterval x)))
  obtain ⟨e, W, hef, hep, hWo, hpW, hWt, hWs⟩ := smooth_inverse_on
    (flowIntegralMap_smooth hV) p D (flowIntegralMap_derivative hV x)
  let z : ℝ × E → FlowParameters E := fun q => (q,0)
  have hzp : z (0,x) = flowIntegralMap V hV.continuous p := by
    simp [z, flowIntegralMap, p]
  refine ⟨z ⁻¹' W, fun q => (e.symm (z q)).2, hWo.preimage (by fun_prop), ?_, ?_, ?_, ?_⟩
  · change z (0,x) ∈ W
    rwa [hzp]
  · exact (hWs.comp (f := z) (s := z ⁻¹' W) (by dsimp [z]; fun_prop) (fun q hq => hq)).snd
  · have he : e.symm (z (0,x)) = p := by
      rw [hzp, ← hef]
      exact e.left_inv hep
    exact congrArg Prod.snd he
  · intro q hq
    have he : flowIntegralMap V hV.continuous (e.symm (z q)) = z q := by
      rw [← hef]
      exact e.right_inv (hWt hq)
    have he1 : (e.symm (z q)).1 = q := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change (e.symm (z q)).2 - ContinuousMap.const unitInterval (e.symm (z q)).1.2 -
      (e.symm (z q)).1.1 • volterra (superposition V hV.continuous (e.symm (z q)).2) = 0 at he2
    rw [he1] at he2
    simpa only [sub_eq_zero, eq_sub_iff_add_eq, sub_eq_iff_eq_add, add_comm, zero_add] using he2


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_IntegralPathSolution
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_path_eq_solution {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {y : E} {t ε : ℝ} (ht : |t| < ε) (u : C(unitInterval, E))
    (hu : u = ContinuousMap.const unitInterval y + t • volterra (superposition V hV.continuous u))
    (α : ℝ → E) (hα0 : α 0 = y)
    (hα : ∀ r ∈ Ioo (-ε) ε, HasDerivAt α (V (α r)) r) :
    ∀ s : unitInterval, u s = α (t * (s : ℝ)) := by
  let w := superposition V hV.continuous u
  let β : ℝ → E := fun s => y + t • ∫ r in 0..s, pathExtension w r
  have hβeq (s : unitInterval) : β s = u s := by
    have hh := congrArg (fun v : C(unitInterval,E) => v s) hu
    exact hh.symm
  have hts (s : ℝ) (hs : s ∈ Icc 0 1) : t*s ∈ Ioo (-ε) ε := by
    have h : |t*s| ≤ |t| := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hs.2
    exact abs_lt.mp (h.trans_lt ht)
  have hβd (s : ℝ) : HasDerivAt β (t • pathExtension w s) s := by
    exact (hasDerivAt_volterra_extension w s).const_smul t |>.const_add y
  have hβc : Continuous β := continuous_iff_continuousAt.mpr fun s => (hβd s).continuousAt
  have hγd (s : ℝ) (hs : s ∈ Icc 0 1) :
      HasDerivAt (fun r => α (t*r)) (t • V (α (t*s))) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hα _ (hts s hs)).scomp s ((hasDerivAt_id s).const_mul t)
  have hγc : ContinuousOn (fun r => α (t*r)) (Icc 0 1) :=
    fun s hs => (hγd s hs).continuousAt.continuousWithinAt
  have he := ODE_solution_unique (v := fun _ z => t • V z)
    (fun _ => (t • ContinuousLinearMap.id ℝ E).lipschitz.comp hV) hβc.continuousOn
    (fun s hs => ?_) hγc (fun s hs => (hγd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (show β 0 = α (t*0) by simp [β,hα0])
  · intro s
    rw [← hβeq s]
    exact he s.property
  · have hs' : s ∈ Icc 0 1 := Ico_subset_Icc_self hs
    have hw : pathExtension w s = V (β s) := by
      rw [← (show (⟨s,hs'⟩ : unitInterval).val = s from rfl), pathExtension_coe, hβeq]
      rfl
    have hh := hβd s
    rw [hw] at hh
    exact hh.hasDerivWithinAt
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.dualNorm
attribute [local instance] OAI.YauCounterexamples.dualSpace
theorem isOpen_quadraticPlaneFull : IsOpen {p : CoordinateForm E × E | quadraticPlaneFull p.1 p.2} := by
  let S : Set E := sphere 0 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let B : Set ((CoordinateForm E × E) × S) := {p | inner ℝ p.1.2 (p.2 : E) = 0 ∧
    p.1.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : ((CoordinateForm E × E) × S) => p.1.1) := continuous_fst.fst
  have hv : Continuous (fun p : ((CoordinateForm E × E) × S) => (p.2 : E)) := continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.snd.inner (continuous_subtype_val.comp continuous_snd)) continuous_const
    · exact isClosed_le
        ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, B]
  constructor
  · intro hp
    rintro ⟨y,hy,hyp⟩
    subst p
    exact (not_le_of_gt (hp y.2 (by simpa only [S, mem_sphere_zero_iff_norm] using y.2.property) hy.1)) hy.2
  · intro hp v hv hav
    by_contra hh
    apply hp
    exact ⟨(p,⟨v,by simpa [S,mem_sphere_zero_iff_norm] using hv⟩),⟨hav,not_lt.mp hh⟩,rfl⟩

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneFull_pos {T : CoordinateForm E} {q v : E}
    (h : quadraticPlaneFull T q) (hv : v ≠ 0) (hqv : inner ℝ q v = 0) : 0 < T v v := by
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hvn]
  have hqw : inner ℝ q w = 0 := by simp [w,inner_smul_right,hqv]
  have hp := h w hw hqw
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hvn]
  have heq : T v v = ‖v‖^2 * T w w := by
    conv_lhs => rw [←hvw]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [heq]
  exact mul_pos (sq_pos_of_ne_zero hvn) hp

omit [FiniteDimensional ℝ E] in
lemma twoCoframeForm_apply (D : E →L[ℝ] (ℝ × ℝ)) (v : E) :
    twoCoframeForm D v v = (D v).1^2+(D v).2^2 := by
  change (D v).1*(D v).1+(D v).2*(D v).2 = _
  ring

local instance planeMapNorm_rd036f4_1 : NormedAddCommGroup (E →L[ℝ] (ℝ × ℝ)) := inferInstance
local instance planeMapSpace_rd036f4_1 : NormedSpace ℝ (E →L[ℝ] (ℝ × ℝ)) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma continuous_twoCoframeForm : Continuous (twoCoframeForm :
    (E →L[ℝ] (ℝ × ℝ)) → CoordinateForm E) := by
  have hl : Continuous (fun D : E →L[ℝ] (ℝ × ℝ) => (ContinuousLinearMap.fst ℝ ℝ ℝ).comp D) :=
    continuous_const.clm_comp continuous_id
  have hr : Continuous (fun D : E →L[ℝ] (ℝ × ℝ) => (ContinuousLinearMap.snd ℝ ℝ ℝ).comp D) :=
    continuous_const.clm_comp continuous_id
  exact ((isBoundedBilinearMap_smulRight.continuous).comp (hl.prodMk hl)).add
    ((isBoundedBilinearMap_smulRight.continuous).comp (hr.prodMk hr))

omit [FiniteDimensional ℝ E] in
lemma scaledSubForm_apply (B C : CoordinateForm E) (v : E) :
    scaledSubForm B C v v = 4*B v v-C v v := by
  simp only [scaledSubForm,sub_apply,smul_apply,smul_eq_mul]

omit [FiniteDimensional ℝ E] in
lemma continuousAt_scaledSubForm {X : Type*} [TopologicalSpace X]
    {B C : X → CoordinateForm E} {p : X} (hB : ContinuousAt B p) (hC : ContinuousAt C p) :
    ContinuousAt (fun x => scaledSubForm (B x) (C x)) p :=
  (hB.const_smul (4:ℝ)).sub hC

theorem twoCoframe_bounds_eventually {X : Type*} [TopologicalSpace X]
    (B : X → CoordinateForm E) (q : X → E) (D : X → E →L[ℝ] (ℝ × ℝ)) {p : X}
    (hB : ContinuousAt B p) (hq : ContinuousAt q p) (hD : ContinuousAt D p)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B p v v)
    (hup : ∀ v, twoCoframeForm (D p) v v ≤ B p v v)
    (heq : ∀ v, inner ℝ (q p) v = 0 → twoCoframeForm (D p) v v = B p v v) :
    ∀ᶠ x in 𝓝 p, (∀ v, twoCoframeForm (D x) v v ≤ 4*B x v v) ∧
      ∀ v, inner ℝ (q x) v = 0 → B x v v ≤ 4*twoCoframeForm (D x) v v := by
  let U : X → CoordinateForm E := fun x => scaledSubForm (B x) (twoCoframeForm (D x))
  let L : X → CoordinateForm E := fun x => scaledSubForm (twoCoframeForm (D x)) (B x)
  have hUc : ContinuousAt U p := continuousAt_scaledSubForm hB (continuous_twoCoframeForm.continuousAt.comp hD)
  have hLc : ContinuousAt L p := continuousAt_scaledSubForm (continuous_twoCoframeForm.continuousAt.comp hD) hB
  have hUf : quadraticPlaneFull (U p) (0:E) := by
    intro v hv _
    have hp := hpos v (norm_ne_zero_iff.mp (by rw [hv]; norm_num))
    dsimp only [U]
    rw [scaledSubForm_apply]
    linarith [hup v]
  have hLf : quadraticPlaneFull (L p) (q p) := by
    intro v hv hqv
    have hp := hpos v (norm_ne_zero_iff.mp (by rw [hv]; norm_num))
    dsimp only [L]
    rw [scaledSubForm_apply]
    rw [heq v hqv]
    linarith
  have hUe : ∀ᶠ x in 𝓝 p, quadraticPlaneFull (U x) (0:E) :=
    (hUc.prodMk continuousAt_const).eventually (isOpen_quadraticPlaneFull.mem_nhds hUf)
  have hLe : ∀ᶠ x in 𝓝 p, quadraticPlaneFull (L x) (q x) :=
    (hLc.prodMk hq).eventually (isOpen_quadraticPlaneFull.mem_nhds hLf)
  filter_upwards [hUe,hLe] with x hUx hLx
  constructor
  · intro v
    by_cases hv : v = 0
    · simp [hv]
    have hh := quadraticPlaneFull_pos hUx hv (by simp)
    dsimp only [U] at hh
    rw [scaledSubForm_apply] at hh
    linarith
  · intro v hqv
    by_cases hv : v = 0
    · simp [hv]
    have hh := quadraticPlaneFull_pos hLx hv hqv
    dsimp only [L] at hh
    rw [scaledSubForm_apply] at hh
    linarith

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

lemma metricGradient_self (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    (NormedSpace.fromTangentSpace (𝕜:=ℝ) x) (metricGradient g u x) =
      (selfMetricFlat g x).inverse (fderiv ℝ u x) := by
  symm
  apply (selfMetricFlat_invertible g x).inverse_apply_eq.mpr
  ext v
  have h := (metricGradient_pairing g u x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v)).symm
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ u x v = g.inner x (metricGradient g u x) ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v) at h
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using h


end

section
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coordinateMetricGradient_eq (g : SmoothMetric E E) (ψ : E → ℝ) (x : E) :
    coordinateMetricGradient g ψ x =
      (NormedSpace.fromTangentSpace (𝕜:=ℝ) x) (metricGradient g ψ x) :=
  (metricGradient_self g ψ x).symm

attribute [local instance] OAI.YauCounterexamples.actualDualNorm
attribute [local instance] OAI.YauCounterexamples.actualDualSpace
lemma contDiff_coordinateMetricGradient (g : SmoothMetric E E) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (coordinateMetricGradient g ψ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  exact hGi.clm_apply (hψ.fderiv_right (m:=∞) (by simp))


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < actualCoordinateNorm g x v := Real.sqrt_pos.mpr (selfMetricFlat_pos g x hv)

attribute [local instance] OAI.YauCounterexamples.globalPrepDualNorm
attribute [local instance] OAI.YauCounterexamples.globalPrepDualSpace
local instance globalPrepInvNorm_rd036f4_1 : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance globalPrepInvSpace_rd036f4_1 : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma continuous_actualCoordinateNorm (g : SmoothMetric E E) {v : E → E}
    (hv : Continuous v) : Continuous (fun x => actualCoordinateNorm g x (v x)) :=
  (((contDiff_selfMetricFlat g).continuous.clm_apply hv).clm_apply hv).sqrt

lemma continuous_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileSpeed g u) :=
  continuous_actualCoordinateNorm g (contDiff_coordinateMetricGradient g hu).continuous

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FlowInitialFderiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem smooth_local_flow_of_lipschitz {V : E → E} (hV : ContDiff ℝ ∞ V)
    {K : ℝ≥0} (hLip : LipschitzWith K V) (x : E) :
    ∃ (O : Set (ℝ × E)) (φ : ℝ × E → E),
      IsOpen O ∧ (0,x) ∈ O ∧ ContDiffOn ℝ ∞ φ O ∧
      (∀ q ∈ O, φ (0,q.2) = q.2) ∧
      ∀ q ∈ O, HasDerivAt (fun t => φ (t,q.2)) (V (φ q)) q.1 := by
  obtain ⟨O₀, u, hO₀, hx₀, hus, hu0, hu⟩ := smooth_integral_paths hV x
  obtain ⟨r, hr, ε, hε, hcurves⟩ :=
    ((hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp)).contDiffAt (x := x)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  let O := (O₀ ∩ (fun q : ℝ × E => (0,q.2)) ⁻¹' O₀) ∩ Ioo (-ε) ε ×ˢ ball x r
  have hOo : IsOpen O := (hO₀.inter (hO₀.preimage (by fun_prop))).inter (isOpen_Ioo.prod isOpen_ball)
  let φ : ℝ × E → E := fun p => u p 1
  have heq (p : ℝ × E) (hp : p ∈ O) (α : ℝ → E) (hα0 : α 0 = p.2)
      (hα : ∀ t ∈ Ioo (-ε) ε, HasDerivAt α (V (α t)) t) : φ p = α p.1 := by
    have hh := integral_path_eq_solution hLip (abs_lt.mpr hp.2.1) (u p) (hu p hp.1.1) α hα0 hα 1
    simpa [φ] using hh
  refine ⟨O, φ, hOo, ⟨⟨hx₀,hx₀⟩, ⟨by simpa using hε, hε⟩, mem_ball_self hr⟩, ?_, ?_, ?_⟩
  · exact (ContinuousMap.evalCLM ℝ (1 : unitInterval)).contDiff.comp_contDiffOn (hus.mono (show O ⊆ O₀ from fun q hq => hq.1.1))
  · intro q hq
    have hq' : (0,q.2) ∈ O₀ := hq.1.2
    have hh := hu (0,q.2) hq'
    simp only [zero_smul, add_zero] at hh
    exact congrArg (fun v : C(unitInterval,E) => v 1) hh
  · intro q hq
    obtain ⟨α,hα0,hα⟩ := hcurves q.2 (ball_subset_closedBall hq.2.2)
    simp only [zero_sub, zero_add] at hα
    have hev : (fun t => φ (t,q.2)) =ᶠ[𝓝 q.1] α := by
      have hh : ∀ᶠ t in 𝓝 q.1, (t,q.2) ∈ O :=
        (continuous_id.prodMk continuous_const).continuousAt.eventually (hOo.mem_nhds hq)
      filter_upwards [hh] with t ht
      exact heq (t,q.2) ht α hα0 hα
    have hd := (hα q.1 hq.2.1).congr_of_eventuallyEq hev
    rw [← heq q hq α hα0 hα] at hd
    exact hd

end

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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma flow_initial_fderiv {O : Set (ℝ × E)} (hO : IsOpen O)
    {φ : ℝ × E → E} (hφ : ContDiffOn ℝ ∞ φ O) {x v : E} (hx : (0,x) ∈ O)
    (h0 : ∀ q ∈ O, φ (0,q.2) = q.2)
    (ht : HasDerivAt (fun t => φ (t,x)) v 0) (a : ℝ) (b : E) :
    fderiv ℝ φ (0,x) (a,b) = a • v + b := by
  have hd := ((hφ _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have htime : fderiv ℝ φ (0,x) (1,0) = v := by
    have hh := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    exact hh.unique ht
  have hspace : (fderiv ℝ φ (0,x)).comp (ContinuousLinearMap.inr ℝ ℝ E) = ContinuousLinearMap.id ℝ E := by
    have hh := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (0 : ℝ) x)
    have he : (fun y => φ (0,y)) =ᶠ[𝓝 x] id := by
      have hN : ∀ᶠ y in 𝓝 x, (0,y) ∈ O :=
        (continuous_const.prodMk continuous_id).continuousAt.eventually (hO.mem_nhds hx)
      filter_upwards [hN] with y hy
      exact h0 (0,y) hy
    exact (hh.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id x)
  have hs : fderiv ℝ φ (0,x) (0,b) = b := congrArg (fun A : E →L[ℝ] E => A b) hspace
  have hab : (a,b) = a • (1,0) + (0,b) := by simp
  rw [hab, map_add, map_smul, htime, hs]

omit [FiniteDimensional ℝ E] in
lemma flow_fderiv_time {O : Set (ℝ × E)} (hO : IsOpen O)
    {φ : ℝ × E → E} (hφ : ContDiffOn ℝ ∞ φ O) {V : E → E}
    (ht : ∀ q ∈ O, HasDerivAt (fun t => φ (t,q.2)) (V (φ q)) q.1)
    {q : ℝ × E} (hq : q ∈ O) : fderiv ℝ φ q (1,0) = V (φ q) := by
  have hd := ((hφ _ hq).contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  exact hh.unique (ht q hq)

theorem smooth_flowbox_of_lipschitz {V : E → E} (hV : ContDiff ℝ ∞ V)
    {K : ℝ≥0} (hLip : LipschitzWith K V) {x : E} (hv : V x ≠ 0) :
    ∃ (W : Set E) (σ : E → E), IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ ∞ σ W ∧
      σ x = 0 ∧ fderiv ℝ σ x = ContinuousLinearMap.id ℝ E ∧
      ∀ y ∈ W, fderiv ℝ σ y (V y) = V x := by
  obtain ⟨O,φ,hO,hx,hφ,h0,ht⟩ := smooth_local_flow_of_lipschitz hV hLip x
  obtain ⟨l, _, hl⟩ := exists_dual_vector ℝ (V x) (norm_ne_zero_iff.mpr hv)
  let L : E →L[ℝ] ℝ := ‖V x‖⁻¹ • l
  have hL : L (V x) = 1 := by simp [L,hl, norm_ne_zero_iff.mpr hv]
  let Q : E → ℝ × E := fun z => (L z, x + (z - L z • V x))
  let A : E →L[ℝ] (ℝ × E) := L.prod (ContinuousLinearMap.id ℝ E - L.smulRight (V x))
  have hQ : ∀ z, HasFDerivAt Q A z := by
    intro z
    exact L.hasFDerivAt.prodMk ((hasFDerivAt_id z).sub
      (L.hasFDerivAt.smul_const (V x)) |>.const_add x)
  have hQc : ContDiff ℝ ∞ Q := by dsimp [Q]; fun_prop
  have hQ0 : Q 0 = (0,x) := by simp [Q]
  have hAv : A (V x) = (1,0) := by simp [A,hL]
  let U := Q ⁻¹' O
  have hUo : IsOpen U := hO.preimage hQc.continuous
  have h0U : (0 : E) ∈ U := by simpa [U,hQ0] using hx
  let F : E → E := φ ∘ Q
  have hFs : ContDiffOn ℝ ∞ F U := hφ.comp hQc.contDiffOn (fun _ h => h)
  have hF0 : F 0 = x := by simpa [F,hQ0] using h0 (0,x) hx
  have hFd : HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0 := by
    have hd := ((hφ _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hd' := hd.hasFDerivAt
    rw [← hQ0] at hd'
    have hh := hd'.comp 0 (hQ 0)
    rw [hQ0] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    change z = fderiv ℝ φ (0,x) (L z, z - L z • V x)
    rw [flow_initial_fderiv hO hφ hx h0 (by simpa [h0 (0,x) hx] using ht (0,x) hx)]
    abel
  obtain ⟨G,hGs,hFG⟩ := smooth_extension_near_compact (isCompact_singleton (x := (0 : E)))
    hUo (by simpa using h0U) hFs
  have hFG' : F =ᶠ[𝓝 (0 : E)] G := by simpa only [nhdsSet_singleton] using hFG
  have hG0 : G 0 = x := hFG'.eq_of_nhds.symm.trans hF0
  have hGd := hFd.congr_of_eventuallyEq hFG'.symm
  obtain ⟨e,T,hef,he0,hTo,hGT,hT,hTs⟩ := smooth_inverse_on hGs 0
    (ContinuousLinearEquiv.refl ℝ E) hGd
  have he0t : e.symm x = 0 := by rw [← hG0, ← hef]; exact e.left_inv he0
  obtain ⟨B,hBsub,hBo,hB0⟩ := _root_.mem_nhds_iff.mp (hFG'.and (hUo.mem_nhds h0U))
  let W := T ∩ e.symm ⁻¹' B
  have hxT : x ∈ T := hG0 ▸ hGT
  have hWo : IsOpen W := (e.continuousOn_symm.mono hT).isOpen_inter_preimage hTo hBo
  have hxW : x ∈ W := ⟨hxT, by simpa [he0t] using hB0⟩
  have hσs : ContDiffOn ℝ ∞ e.symm W := hTs.mono inter_subset_left
  have hsx : HasFDerivAt e.symm (ContinuousLinearMap.id ℝ E) x := by
    have hh := e.hasFDerivAt_symm (f' := ContinuousLinearEquiv.refl ℝ E) (hT hxT) (by simpa [he0t,hef] using hGd)
    simpa using hh
  refine ⟨W,e.symm,hWo,hxW,hσs,he0t,hsx.fderiv,?_⟩
  intro y hy
  have hyt := hT hy.1
  have hyB : e.symm y ∈ B := hy.2
  have hyU : e.symm y ∈ U := (hBsub hyB).2
  have hFGe : F =ᶠ[𝓝 (e.symm y)] G :=
    Filter.Eventually.mono (hBo.mem_nhds hyB) (fun z hz => (hBsub hz).1)
  have hGv : fderiv ℝ G (e.symm y) (V x) = V y := by
    have hdφ := ((hφ _ hyU).contDiffAt (hO.mem_nhds hyU)).differentiableAt (by simp)
    have hdF := hdφ.hasFDerivAt.comp (e.symm y) (hQ _)
    have heval : F (e.symm y) = y := by
      rw [hFGe.eq_of_nhds, ← hef]
      exact e.right_inv hyt
    rw [← hFGe.fderiv_eq, hdF.fderiv]
    change fderiv ℝ φ (Q (e.symm y)) (A (V x)) = V y
    rw [hAv, flow_fderiv_time hO hφ ht hyU]
    exact congrArg V heval
  have hdG := hGs.differentiable (by simp) (e.symm y)
  have hdσ := ((hσs _ hy).contDiffAt (hWo.mem_nhds hy)).differentiableAt (by simp)
  have hinv : (fun z => e.symm (G z)) =ᶠ[𝓝 (e.symm y)] id := by
    filter_upwards [e.open_source.mem_nhds (e.map_target hyt)] with z hz
    rw [← hef]
    exact e.left_inv hz
  have hGy : G (e.symm y) = y := by rw [← hef]; exact e.right_inv hyt
  have hdσ' := hdσ.hasFDerivAt
  rw [← hGy] at hdσ'
  have hid := (hdσ'.comp (e.symm y) hdG.hasFDerivAt).congr_of_eventuallyEq hinv.symm
  rw [hGy] at hid
  have heq := hid.unique (hasFDerivAt_id (e.symm y))
  have heqv := congrArg (fun D : E →L[ℝ] E => D (V x)) heq
  simpa only [ContinuousLinearMap.comp_apply, hGv, ContinuousLinearMap.id_apply] using heqv

theorem smooth_flowbox {V : E → E} (hV : ContDiff ℝ ∞ V) {x : E} (hv : V x ≠ 0) :
    ∃ (W : Set E) (σ : E → E), IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ ∞ σ W ∧
      σ x = 0 ∧ fderiv ℝ σ x = ContinuousLinearMap.id ℝ E ∧
      ∀ y ∈ W, fderiv ℝ σ y (V y) = V x := by
  let χ : ContDiffBump x := ⟨1,2,zero_lt_one,by norm_num⟩
  let Z : E → E := fun y => χ y • V y
  have hZ : ContDiff ℝ ∞ Z := χ.contDiff.smul hV
  have hZc : HasCompactSupport Z := χ.hasCompactSupport.smul_right
  obtain ⟨K,hLip⟩ := hZ.lipschitzWith_of_hasCompactSupport hZc (by simp)
  have he (y : E) (hy : y ∈ ball x 1) : Z y = V y := by
    simp only [Z, χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
  have hx : x ∈ ball x 1 := mem_ball_self zero_lt_one
  obtain ⟨W,σ,hWo,hWx,hσ,hσx,hσd,hrect⟩ := smooth_flowbox_of_lipschitz hZ hLip (he x hx ▸ hv)
  refine ⟨W ∩ ball x 1,σ,hWo.inter isOpen_ball,⟨hWx,hx⟩,hσ.mono inter_subset_left,hσx,hσd,?_⟩
  intro y hy
  simpa only [he y hy.2, he x hx] using hrect y hy.1



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section


section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem exists_transverse_two_coframe (hd : Module.finrank ℝ E = 3)
    {a : E} (ha : a ≠ 0) :
    ∃ D : E →L[ℝ] (ℝ × ℝ), D a = 0 ∧
      (∀ v, Real.sqrt ((D v).1^2+(D v).2^2) ≤ ‖v‖) ∧
      ∀ v, inner ℝ a v = 0 → Real.sqrt ((D v).1^2+(D v).2^2) = ‖v‖ := by
  let : Fact (Module.finrank ℝ E = 2+1) := ⟨hd⟩
  let K := (ℝ ∙ a)ᗮ
  let b : OrthonormalBasis (Fin 2) ℝ K := OrthonormalBasis.fromOrthogonalSpanSingleton 2 ha
  let D : E →L[ℝ] (ℝ × ℝ) :=
    (InnerProductSpace.toDual ℝ E (b 0 : E)).prod (InnerProductSpace.toDual ℝ E (b 1 : E))
  have hD (v : E) : (D v).1^2+(D v).2^2 = ‖K.orthogonalProjectionOnto v‖^2 := by
    have hh := b.sum_sq_inner_right (K.orthogonalProjectionOnto v)
    simpa only [Fin.sum_univ_two,
      K.inner_orthogonalProjectionOnto_eq_of_mem_left, D,
      ContinuousLinearMap.prod_apply,InnerProductSpace.toDual_apply_apply] using hh
  have hDa : D a = 0 := by
    ext
    · change inner ℝ (b 0 : E) a = 0
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property
    · change inner ℝ (b 1 : E) a = 0
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 1).property
  refine ⟨D,hDa,?_,?_⟩
  · intro v
    rw [hD,Real.sqrt_sq (norm_nonneg _)]
    exact K.norm_orthogonalProjectionOnto_apply_le v
  · intro v hv
    rw [hD,Real.sqrt_sq (norm_nonneg _)]
    exact K.norm_orthogonalProjectionOnto_apply
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv)

theorem exists_metric_two_coframe (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) (ψ : E → ℝ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ D : E →L[ℝ] (ℝ × ℝ), D (coordinateMetricGradient g ψ p) = 0 ∧
      (∀ v, twoCoframeForm D v v ≤ selfMetricFlat g p v v) ∧
      ∀ v, fderiv ℝ ψ p v = 0 → twoCoframeForm D v v = selfMetricFlat g p v v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) p
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) p) := Module.Finite.equiv j.symm.toLinearEquiv
  have hg : metricGradient g ψ p ≠ 0 := by
    intro hh
    apply ha
    rw [coordinateMetricGradient_eq,hh,map_zero]
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ,E) p) = 3 :=
    (j.toLinearEquiv.finrank_eq).trans hd
  obtain ⟨D,hDa,hDu,hDe⟩ := exists_transverse_two_coframe hdim hg
  let D₀ := D.comp j.symm.toContinuousLinearMap
  have hnorm (v : E) : selfMetricFlat g p v v = ‖j.symm v‖^2 := by
    have hn := real_inner_self_eq_norm_sq (j.symm v : TangentSpace 𝓘(ℝ,E) p)
    change g.inner p (j.symm v) (j.symm v) = ‖j.symm v‖^2 at hn
    simpa only [j,selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe,NormedSpace.fromTangentSpace] using hn
  have hsq (v : E) : (Real.sqrt ((D (j.symm v)).1^2+(D (j.symm v)).2^2))^2 =
      twoCoframeForm D₀ v v := by
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),twoCoframeForm_apply]
    rfl
  refine ⟨D₀,?_,?_,?_⟩
  · rw [coordinateMetricGradient_eq]
    simpa only [D₀,j,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hDa
  · intro v
    rw [hnorm,←hsq]
    exact sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _) |>.mpr (hDu _)
  · intro v hv
    have hor : inner ℝ (metricGradient g ψ p) (j.symm v) = 0 := by
      change g.inner p (metricGradient g ψ p) (j.symm v) = 0
      rw [metricGradient_pairing,mfderiv_eq_fderiv]
      exact hv
    rw [hnorm,←hsq,hDe _ hor]

local instance radialCoframeDualNorm_rd036f4_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialCoframeDualSpace_rd036f4_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
theorem exists_local_metric_coframe (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ (W : Set E) (y : E → ℝ × ℝ), IsOpen W ∧ p ∈ W ∧ ContDiff ℝ ∞ y ∧
      ∀ x ∈ W, fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
        (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
        ∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v := by
  obtain ⟨D,hDa,hDu,hDe⟩ := exists_metric_two_coframe hd g ψ ha
  obtain ⟨O,σ,hOo,hOp,hσ,hσp,hσd,hrect⟩ :=
    smooth_flowbox (contDiff_coordinateMetricGradient g hψ) ha
  obtain ⟨σ',hσ',he⟩ := smooth_extension_near_compact isCompact_singleton hOo
    (singleton_subset_iff.mpr hOp) hσ
  have he' : σ =ᶠ[𝓝 p] σ' := by simpa only [nhdsSet_singleton] using he
  let y := D ∘ σ'
  have hy : ContDiff ℝ ∞ y := D.contDiff.comp hσ'
  have hyd (x : E) : fderiv ℝ y x = D.comp (fderiv ℝ σ' x) := by
    exact (D.hasFDerivAt.comp x (hσ'.differentiable (by simp) x).hasFDerivAt).fderiv
  have hydp : fderiv ℝ y p = D := by
    rw [hyd,←he'.fderiv_eq (𝕜:=ℝ),hσd,ContinuousLinearMap.comp_id]
  have hf : ∀ᶠ x in 𝓝 p, fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 := by
    filter_upwards [he'.fderiv (𝕜:=ℝ),hOo.mem_nhds hOp] with x hx hxO
    rw [hyd,←hx,ContinuousLinearMap.comp_apply,hrect x hxO,hDa]
  let q : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ x)
  have hq : Continuous q := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hψ.continuous_fderiv (by simp))
  have hqv (x v : E) : inner ℝ (q x) v = fderiv ℝ ψ x v := InnerProductSpace.toDual_symm_apply
  have hb := twoCoframe_bounds_eventually (selfMetricFlat g) q (fderiv ℝ y)
    (contDiff_selfMetricFlat g).continuous.continuousAt hq.continuousAt
    (hy.continuous_fderiv (by simp)).continuousAt
    (fun v hv => selfMetricFlat_pos g p hv)
    (fun v => by rw [hydp]; exact hDu v)
    (fun v hv => by rw [hydp]; exact hDe v ((hqv p v).symm.trans hv))
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.mem_nhds_iff.mp (hf.and hb)
  refine ⟨W,y,hWo,hWp,hy,?_⟩
  intro x hx
  obtain ⟨hf,hb₁,hb₂⟩ := hW hx
  exact ⟨hf,hb₁,fun v hv => hb₂ v ((hqv x v).trans hv)⟩

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_local_metric_radial_patch_oai (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ (W : Set E) (y : E → ProfilePlane) (A : ℝ), IsOpen W ∧ p ∈ W ∧
      ContDiff ℝ ∞ y ∧ 0 < A ∧ ∀ x ∈ W,
      fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
      (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
      (∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v) ∧
      A ≤ 2*actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x/2 ≤ A := by
  obtain ⟨O,y,hOo,hOp,hy,hdata⟩ := exists_local_metric_coframe hdim g hψ ha
  let A := actualProfileSpeed g ψ p
  have hA : 0 < A := actualCoordinateNorm_pos g p ha
  let W := O ∩ {x | A/2 < actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x < 2*A}
  have hc := continuous_actualProfileSpeed g hψ
  have hWo : IsOpen W := hOo.inter ((isOpen_lt continuous_const hc).inter
    (isOpen_lt hc continuous_const))
  refine ⟨W,y,A,hWo,⟨hOp,by dsimp only [A]; constructor <;> linarith⟩,hy,hA,?_⟩
  intro x hx
  obtain ⟨hf,hU,hL⟩ := hdata x hx.1
  exact ⟨hf,hU,hL,by linarith [hx.2.1],by linarith [hx.2.2]⟩

end
end YauCounterexamples

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.exists_local_metric_radial_patch_oai.{u_1} := @OAI.YauCounterexamples.exists_local_metric_radial_patch_oai.{u_1}
