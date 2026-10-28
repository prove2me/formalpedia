-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_actual_preparation_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:05:31.587104+00:00
-- url     : https://prove2.me/submissions/0dba4c97-22e4-4d62-b6b8-1a0c4bf6144e

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactFullProfileMargin
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
section ProfileForms
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma continuous_profileTrace : Continuous (fun p : (ProfileForm E × E) × E =>
    profileTrace p.1.1 p.1.2 p.2) := by
  have hH : Continuous (fun p : (ProfileForm E × E) × E => p.1.1) := continuous_fst.fst
  have ha : Continuous (fun p : (ProfileForm E × E) × E => p.1.2) := continuous_fst.snd
  have hv : Continuous (fun p : (ProfileForm E × E) × E => p.2) := continuous_snd
  exact (hH.clm_apply ha |>.clm_apply ha).add
    ((continuous_const.add (ha.norm.pow 2)).mul (hH.clm_apply hv |>.clm_apply hv))

end ProfileForms

variable {X : Type*} [TopologicalSpace X]

theorem compact_positive_linear_penalty {K : Set X} (hK : IsCompact K)
    {A B : X → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hAn : ∀ x, 0 ≤ A x) (hker : ∀ x ∈ K, A x = 0 → 0 < B x) :
    ∃ n : ℕ, ∀ x ∈ K, 0 < B x + n * A x := by
  let U : ℕ → Set X := fun n => {x | 0 < B x + n * A x}
  have ho : ∀ n, IsOpen (U n) := fun n => isOpen_lt continuous_const (hB.add (continuous_const.mul hA))
  have hc : K ⊆ ⋃ n, U n := by
    intro x hx
    by_cases ha : A x = 0
    · exact mem_iUnion.mpr ⟨0,by simpa [U,ha] using hker x hx ha⟩
    · have hap : 0 < A x := lt_of_le_of_ne (hAn x) (Ne.symm ha)
      obtain ⟨n,hn⟩ := exists_nat_gt ((-B x) / A x)
      refine mem_iUnion.mpr ⟨n,?_⟩
      change 0 < B x + n * A x
      have hh := (div_lt_iff₀ hap).mp hn
      linarith
  have hd : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j,?_,?_⟩ <;> intro x hx
    · change 0 < B x + i * A x at hx
      change 0 < B x + (max i j : ℕ) * A x
      have hh : (i : ℝ) * A x ≤ (max i j : ℕ) * A x := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left i j) (hAn x)
      linarith
    · change 0 < B x + j * A x at hx
      change 0 < B x + (max i j : ℕ) * A x
      have hh : (j : ℝ) * A x ≤ (max i j : ℕ) * A x := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right i j) (hAn x)
      linarith
  exact hK.elim_directed_cover U ho hc hd

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma profileTrace_add_rankOne (H : ProfileForm E) (a v : E)
    (l : E →L[ℝ] ℝ) (c : ℝ) :
    profileTrace (H + c • profileRankOne l) a v =
      profileTrace H a v + c * ((l a)^2 + (1 + ‖a‖^2) * (l v)^2) := by
  change H a a + c * (l a * l a) + (1 + ‖a‖^2) * (H v v + c * (l v * l v)) =
    H a a + (1 + ‖a‖^2) * H v v + c * ((l a)^2 + (1 + ‖a‖^2) * (l v)^2)
  ring

omit [FiniteDimensional ℝ E] in
lemma profileStrict_rankOne (H : ProfileForm E) (a : E) (l : E →L[ℝ] ℝ)
    (ha : l a = 0) (hv : ∃ v, ‖v‖ = 1 ∧ inner ℝ a v = 0 ∧ l v = 0 ∧
      0 < profileTrace H a v) (c : ℝ) : profileStrict (H + c • profileRankOne l) a := by
  obtain ⟨v,hv,hav,hlv,hpos⟩ := hv
  refine ⟨v,hv,hav,?_⟩
  simpa [profileTrace_add_rankOne,ha,hlv] using hpos

theorem preparation_rankOne_full {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (H : X → ProfileForm E) (a : X → E)
    (l : X → E →L[ℝ] ℝ) (hH : Continuous H) (ha : Continuous a) (hl : Continuous l)
    (hker : ∀ x ∈ K, ∀ v, ‖v‖ = 1 → inner ℝ (a x) v = 0 → l x v = 0 →
      0 < profileTrace (H x) (a x) v) :
    ∃ C : ℕ, ∀ x ∈ K, ∀ c : ℝ, C ≤ c → profileFull (H x + c • profileRankOne (l x)) (a x) := by
  let S : Set (X × E) := {p | p.1 ∈ K ∧ ‖p.2‖ = 1 ∧ inner ℝ (a p.1) p.2 = 0}
  have hS : IsCompact S := by
    have heq : S = (K ×ˢ sphere (0 : E) 1) ∩ {p | inner ℝ (a p.1) p.2 = 0} := by
      ext p
      simp only [S,mem_ofPred_eq,mem_inter_iff, mem_prod,mem_sphere_zero_iff_norm]
      tauto
    rw [heq]
    exact (hK.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq ((ha.comp continuous_fst).inner continuous_snd) continuous_const)
  let A : X × E → ℝ := fun p => (l p.1 (a p.1))^2 + (1 + ‖a p.1‖^2) * (l p.1 p.2)^2
  let B : X × E → ℝ := fun p => profileTrace (H p.1) (a p.1) p.2
  have hA : Continuous A := by
    exact (((hl.comp continuous_fst).clm_apply (ha.comp continuous_fst)).pow 2).add
      ((continuous_const.add ((ha.comp continuous_fst).norm.pow 2)).mul
        (((hl.comp continuous_fst).clm_apply continuous_snd).pow 2))
  have hB : Continuous B := continuous_profileTrace.comp
    (((hH.prodMk ha).comp continuous_fst).prodMk continuous_snd)
  have hAn : ∀ p, 0 ≤ A p := by intro p; dsimp [A]; positivity
  have hAk : ∀ p ∈ S, A p = 0 → 0 < B p := by
    intro p hp heq
    have hsq : (l p.1 p.2)^2 = 0 := by
      have hh : 0 < 1 + ‖a p.1‖^2 := by positivity
      dsimp [A] at heq
      nlinarith [sq_nonneg (l p.1 (a p.1)),sq_nonneg (l p.1 p.2)]
    exact hker p.1 hp.1 p.2 hp.2.1 hp.2.2 (sq_eq_zero_iff.mp hsq)
  obtain ⟨C,hC⟩ := compact_positive_linear_penalty hS hA hB hAn hAk
  refine ⟨C,?_⟩
  intro x hx c hc v hv hav
  rw [profileTrace_add_rankOne]
  have hh := hC (x,v) ⟨hx,hv,hav⟩
  have hm := mul_le_mul_of_nonneg_right hc (hAn (x,v))
  change 0 < B (x,v) + c * A (x,v)
  linarith

end

open Set Filter Function Metric
open scoped Topology
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ExistsPreparationCovector
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
namespace YauCounterexamples
open Set Filter Submodule
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_preparation_covector (hd : Module.finrank ℝ E = 3)
    {a : E} (ha : a ≠ 0) {H : ProfileForm E} (hs : profileStrict H a) :
    ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ l a = 0 ∧
      (∀ c : ℝ, profileStrict (H + c • profileRankOne l) a) ∧
      ∃ C : ℕ, ∀ c : ℝ, C ≤ c → profileFull (H + c • profileRankOne l) a := by
  obtain ⟨w,hw,haw,hpos⟩ := hs
  let K := (ℝ ∙ a)ᗮ
  let wK : K := ⟨w,mem_orthogonal_singleton_iff_inner_right.mpr haw⟩
  have hwK : wK ≠ 0 := by
    intro h
    have hh := congrArg (fun z : K => ‖(z:E)‖) h
    simp [wK,hw] at hh
  let : Fact (Module.finrank ℝ E = 2+1) := ⟨hd⟩
  have hK : Module.finrank ℝ K = 2 := finrank_orthogonal_span_singleton ha
  let : Fact (Module.finrank ℝ K = 1+1) := ⟨hK⟩
  let L := (ℝ ∙ wK)ᗮ
  have hL : Module.finrank ℝ L = 1 := finrank_orthogonal_span_singleton hwK
  let b : OrthonormalBasis (Fin 1) ℝ L := OrthonormalBasis.fromOrthogonalSpanSingleton 1 hwK
  let e : K := b 0
  have hen : e ≠ 0 := by
    intro h
    have hh : ‖b 0‖ = 0 := by change ‖e‖ = 0; rw [h,norm_zero]
    rw [b.norm_eq_one] at hh
    norm_num at hh
  have heL : e ∈ L := (b 0).property
  have hspan : L = ℝ ∙ e := eq_span_singleton_of_mem_of_finrank_eq_one hL heL hen
  let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E (e:E)
  have hla : l a = 0 := by
    change inner ℝ (e:E) a = 0
    rw [real_inner_comm]
    exact mem_orthogonal_singleton_iff_inner_right.mp e.property
  have hlw : l w = 0 := by
    change inner ℝ (e:E) w = 0
    have hh := mem_orthogonal_singleton_iff_inner_right.mp heL
    rw [real_inner_comm]
    exact hh
  have hlne : l ≠ 0 := by
    intro h
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f (e:E)) h
    change inner ℝ (e:E) (e:E) = 0 at hh
    exact hen (Subtype.ext (inner_self_eq_zero.mp hh))
  have hker : ∀ v, ‖v‖ = 1 → inner ℝ a v = 0 → l v = 0 →
      0 < profileTrace H a v := by
    intro v hv hav hlv
    let vK : K := ⟨v,mem_orthogonal_singleton_iff_inner_right.mpr hav⟩
    have hvL : vK ∈ Lᗮ := by
      apply (L.mem_orthogonal vK).mpr
      intro z hz
      rw [hspan] at hz
      obtain ⟨c,rfl⟩ := mem_span_singleton.mp hz
      simp only [inner_smul_left,conj_trivial]
      change c * l v = 0
      rw [hlv,mul_zero]
    have hvspan : vK ∈ ℝ ∙ wK := by
      simpa only [L,orthogonal_orthogonal] using hvL
    obtain ⟨c,hc⟩ := mem_span_singleton.mp hvspan
    have hcv : c • w = v := congrArg (fun z : K => (z:E)) hc
    have hcn : |c| = 1 := by simpa only [←hcv,norm_smul,Real.norm_eq_abs,hw,mul_one] using hv
    have hcsq : c*c = 1 := by nlinarith [sq_abs c]
    rw [←hcv]
    unfold profileTrace
    simp only [map_smul,smul_apply,smul_eq_mul]
    have heq : c*(c*H w w) = H w w := by rw [←mul_assoc,hcsq,one_mul]
    rw [heq]
    exact hpos
  have hfull := preparation_rankOne_full (show IsCompact ({()} : Set Unit) from isCompact_singleton) (fun _ : Unit => H)
    (fun _ : Unit => a) (fun _ : Unit => l) continuous_const continuous_const continuous_const
    (fun _ _ => hker)
  obtain ⟨C,hC⟩ := hfull
  exact ⟨l,hlne,hla,profileStrict_rankOne H a l hla ⟨w,hw,haw,hlw,hpos⟩,
    C,fun c hc => hC () (mem_singleton ()) c hc⟩

end YauCounterexamples

end

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

theorem smooth_first_integral {V : E → E} (hV : ContDiff ℝ ∞ V) {x : E} (hv : V x ≠ 0)
    (l : E →L[ℝ] ℝ) (hl : l ≠ 0) (hlv : l (V x) = 0) :
    ∃ (W : Set E) (s : E → ℝ), IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ ∞ s W ∧
      s x = 0 ∧ fderiv ℝ s x = l ∧
      ∀ y ∈ W, fderiv ℝ s y ≠ 0 ∧ fderiv ℝ s y (V y) = 0 := by
  obtain ⟨W,σ,hWo,hWx,hσ,hσx,hσd,hrect⟩ := smooth_flowbox hV hv
  let s := l ∘ σ
  have hs : ContDiffOn ℝ ∞ s W := l.contDiff.comp_contDiffOn hσ
  have hsd (y : E) (hy : y ∈ W) : fderiv ℝ s y = l.comp (fderiv ℝ σ y) := by
    exact (l.hasFDerivAt.comp y (((hσ y hy).contDiffAt (hWo.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hsdx : fderiv ℝ s x = l := by rw [hsd x hWx,hσd,ContinuousLinearMap.comp_id]
  have hn : ∀ᶠ y in 𝓝 x, fderiv ℝ s y ≠ 0 := by
    apply ((hs.continuousOn_fderiv_of_isOpen hWo (by simp)) x hWx).continuousAt (hWo.mem_nhds hWx) |>.eventually_ne
    rwa [hsdx]
  obtain ⟨B,hB,hBo,hBx⟩ := _root_.mem_nhds_iff.mp (hn.and (hWo.mem_nhds hWx))
  refine ⟨B,s,hBo,hBx,hs.mono (fun y hy => (hB hy).2),?_,hsdx,?_⟩
  · simp [s,hσx]
  · intro y hy
    refine ⟨(hB hy).1,?_⟩
    rw [hsd y (hB hy).2, ContinuousLinearMap.comp_apply, hrect y (hB hy).2, hlv]



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

omit [FiniteDimensional ℝ E] in
lemma metricProfileTraceForm_apply (B H : CoordinateForm E) (a v : E) :
    metricProfileTraceForm B H a v v = B v v*H a a+(1+B a a)*H v v := by
  simp only [metricProfileTraceForm,add_apply,smul_apply,smul_eq_mul]
  ring

attribute [local instance] OAI.YauCounterexamples.dualNorm
attribute [local instance] OAI.YauCounterexamples.dualSpace
omit [FiniteDimensional ℝ E] in

theorem quadraticPlaneStrict_eventually {H : CoordinateForm E} {a : E} (ha : a ≠ 0)
    (hs : quadraticPlaneStrict H a) : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), quadraticPlaneStrict p.1 p.2 := by
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w : CoordinateForm E × E → E := fun p => v - (inner ℝ p.2 v / ‖p.2‖ ^ 2) • p.2
  have han : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hsnd : Continuous (fun p : CoordinateForm E × E => p.2) := continuous_snd
  have hw : ContinuousAt w (H,a) := by
    exact continuousAt_const.sub (((hsnd.inner continuous_const).continuousAt.div
      (hsnd.norm.pow 2).continuousAt han).smul hsnd.continuousAt)
  have hwa : w (H,a) = v := by simp [w,hav]
  let z : CoordinateForm E × E → E := fun p => ‖w p‖⁻¹ • w p
  have hz : ContinuousAt z (H,a) :=
    (hw.norm.inv₀ (by rw [hwa,hv]; norm_num)).smul hw
  have hza : z (H,a) = v := by simp [z,hwa,hv]
  have hp : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), 0 < p.1 (z p) (z p) := by
    have hc : ContinuousAt (fun p : CoordinateForm E × E => p.1 (z p) (z p)) (H,a) :=
      (continuousAt_fst.clm_apply hz).clm_apply hz
    apply hc.eventually (Ioi_mem_nhds ?_)
    simpa [hza] using hpos
  have hane : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), p.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually_ne ha
  have hwne : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), w p ≠ 0 :=
    hw.eventually_ne (by rw [hwa]; exact norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  filter_upwards [hp,hane,hwne] with p hp hpa hpw
  refine ⟨z p,?_,?_,hp⟩
  · simp [z,norm_smul,norm_ne_zero_iff.mpr hpw]
  · have hpn : ‖p.2‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hpa)
    have hwperp : inner ℝ p.2 (w p) = 0 := by
      simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    simp [z,inner_smul_right,hwperp]

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

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

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
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance genericHessMapNorm_r1d770e_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_r1d770e_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_r1d770e_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_iff_nonzero (T : CoordinateForm E) (q : E) :
    quadraticPlaneStrict T q ↔ ∃ v, v ≠ 0 ∧ inner ℝ q v = 0 ∧ 0 < T v v := by
  constructor
  · rintro ⟨v,hv,hq,hp⟩
    exact ⟨v,norm_ne_zero_iff.mp (by rw [hv]; norm_num),hq,hp⟩
  · rintro ⟨v,hv,hq,hp⟩
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v,?_,?_,?_⟩
    · simp [norm_smul,ne_of_gt hn]
    · simp [inner_smul_right,hq]
    · simpa only [map_smul,smul_apply,smul_eq_mul] using
        mul_pos (inv_pos.mpr hn) (mul_pos (inv_pos.mpr hn) hp)

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneFull_iff_nonzero (T : CoordinateForm E) (q : E) :
    quadraticPlaneFull T q ↔ ∀ v, v ≠ 0 → inner ℝ q v = 0 → 0 < T v v := by
  constructor
  · intro h v hv hq
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hp := h (‖v‖⁻¹ • v)
      (by simp [norm_smul,ne_of_gt hn])
      (by simp [inner_smul_right,hq])
    simp only [map_smul,smul_apply,smul_eq_mul] at hp
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
      ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)
  · intro h v hv hq
    exact h v (norm_ne_zero_iff.mp (by rw [hv]; norm_num)) hq

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

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_metric_norm (g : SmoothMetric E E) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ v : TangentSpace 𝓘(ℝ,E) x,
      selfMetricFlat g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
        ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = ‖v‖^2 := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro v
  have hn := real_inner_self_eq_norm_sq v
  change g.inner x v v = ‖v‖^2 at hn
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hn

omit [FiniteDimensional ℝ E] in
lemma profileStrict_iff_quadratic (H : ProfileForm E) (a : E) :
    profileStrict H a ↔ quadraticPlaneStrict (metricProfileTraceForm (innerSL ℝ) H a) a := by
  have ht (v : E) (hv : ‖v‖ = 1) :
      metricProfileTraceForm (innerSL ℝ) H a v v = profileTrace H a v := by
    rw [metricProfileTraceForm_apply]
    change inner ℝ v v * H a a + (1+inner ℝ a a)*H v v = profileTrace H a v
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,one_mul,profileTrace]
  constructor
  · rintro ⟨v,hv,hav,hp⟩
    exact ⟨v,hv,hav,by rwa [ht v hv]⟩
  · rintro ⟨v,hv,hav,hp⟩
    exact ⟨v,hv,hav,by rwa [ht v hv] at hp⟩

omit [FiniteDimensional ℝ E] in
lemma profileFull_iff_quadratic (H : ProfileForm E) (a : E) :
    profileFull H a ↔ quadraticPlaneFull (metricProfileTraceForm (innerSL ℝ) H a) a := by
  have ht (v : E) (hv : ‖v‖ = 1) :
      metricProfileTraceForm (innerSL ℝ) H a v v = profileTrace H a v := by
    rw [metricProfileTraceForm_apply]
    change inner ℝ v v * H a a + (1+inner ℝ a a)*H v v = profileTrace H a v
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,one_mul,profileTrace]
  constructor <;> intro h v hv hav
  · rw [ht v hv]
    exact h v hv hav
  · rw [←ht v hv]
    exact h v hv hav

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_transport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (j : V ≃L[ℝ] E) (T : CoordinateForm E) (S : CoordinateForm V)
    (q : E) (a : V) (hT : ∀ v, T (j v) (j v) = S v v)
    (hq : ∀ v, inner ℝ q (j v) = inner ℝ a v) :
    quadraticPlaneStrict T q ↔ quadraticPlaneStrict S a := by
  rw [quadraticPlaneStrict_iff_nonzero,quadraticPlaneStrict_iff_nonzero]
  constructor
  · rintro ⟨v,hv,hqv,hp⟩
    refine ⟨j.symm v,by simpa using hv,?_,?_⟩
    · rw [←hq,j.apply_symm_apply]
      exact hqv
    · rwa [←hT,j.apply_symm_apply]
  · rintro ⟨v,hv,hqv,hp⟩
    exact ⟨j v,by simpa using hv,(hq v).trans hqv,by rwa [hT]⟩

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneFull_transport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (j : V ≃L[ℝ] E) (T : CoordinateForm E) (S : CoordinateForm V)
    (q : E) (a : V) (hT : ∀ v, T (j v) (j v) = S v v)
    (hq : ∀ v, inner ℝ q (j v) = inner ℝ a v) :
    quadraticPlaneFull T q ↔ quadraticPlaneFull S a := by
  rw [quadraticPlaneFull_iff_nonzero,quadraticPlaneFull_iff_nonzero]
  constructor
  · intro h v hv hqv
    rw [←hT]
    exact h (j v) (by simpa using hv) ((hq v).trans hqv)
  · intro h v hv hqv
    have horth : inner ℝ a (j.symm v) = 0 := by
      rw [←hq,j.apply_symm_apply]
      exact hqv
    have hp := h (j.symm v) (by simpa using hv) horth
    simpa only [←hT,j.apply_symm_apply] using hp

lemma coordinateProfileStrict_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (H₀ : CoordinateForm E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    quadraticPlaneStrict (metricProfileTraceForm (selfMetricFlat g x) H₀ (coordinateMetricGradient g u x))
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ↔ profileStrict
      (H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  rw [profileStrict_iff_quadratic]
  apply quadraticPlaneStrict_transport j
  · intro v
    rw [metricProfileTraceForm_apply,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
    rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
    change ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
      (1+‖metricGradient g u x‖^2)*H v v =
      inner ℝ v v*H (metricGradient g u x) (metricGradient g u x) +
      (1+inner ℝ (metricGradient g u x) (metricGradient g u x))*H v v
    simp only [real_inner_self_eq_norm_sq]
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    change fderiv ℝ u x (j v) = g.inner x (metricGradient g u x) v
    rw [metricGradient_pairing,mfderiv_eq_fderiv]
    rfl

lemma coordinateProfileFull_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (H₀ : CoordinateForm E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    quadraticPlaneFull (metricProfileTraceForm (selfMetricFlat g x) H₀ (coordinateMetricGradient g u x))
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ↔ profileFull
      (H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  rw [profileFull_iff_quadratic]
  apply quadraticPlaneFull_transport j
  · intro v
    rw [metricProfileTraceForm_apply,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
    rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
    change ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
      (1+‖metricGradient g u x‖^2)*H v v =
      inner ℝ v v*H (metricGradient g u x) (metricGradient g u x) +
      (1+inner ℝ (metricGradient g u x) (metricGradient g u x))*H v v
    simp only [real_inner_self_eq_norm_sq]
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    change fderiv ℝ u x (j v) = g.inner x (metricGradient g u x) v
    rw [metricGradient_pairing,mfderiv_eq_fderiv]
    rfl

lemma actualProfileStrict_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    actualProfileStrict g u x ↔ profileStrict
      ((actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) :=
  coordinateProfileStrict_iff_tangent g u x (actualCoordinateHessian g u x)

theorem exists_actual_preparation_covector (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (ha : coordinateMetricGradient g u x ≠ 0) (hs : actualProfileStrict g u x) :
    ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ l (coordinateMetricGradient g u x) = 0 ∧
      (∀ c : ℝ, quadraticPlaneStrict
        (metricProfileTraceForm (selfMetricFlat g x) (actualCoordinateHessian g u x+c • profileRankOne l)
          (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
      ∃ C : ℕ, ∀ c : ℝ, C ≤ c → quadraticPlaneFull
        (metricProfileTraceForm (selfMetricFlat g x) (actualCoordinateHessian g u x+c • profileRankOne l)
          (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := (actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ,E) x) = 3 :=
    j.toLinearEquiv.finrank_eq.trans hd
  have ha' : metricGradient g u x ≠ 0 := by
    intro h
    apply ha
    rw [coordinateMetricGradient_eq,h,map_zero]
  obtain ⟨l,hl,hla,hlS,C,hlF⟩ := exists_preparation_covector hdim ha'
    ((actualProfileStrict_iff_tangent g u x).mp hs)
  let l₀ := l.comp j.symm.toContinuousLinearMap
  have hform (c : ℝ) :
      (actualCoordinateHessian g u x+c • profileRankOne l₀).bilinearComp
        j.toContinuousLinearMap j.toContinuousLinearMap = H+c • profileRankOne l := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply,add_apply,
      smul_apply,profileRankOne,ContinuousLinearMap.smulRight_apply,
      l₀,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply,smul_eq_mul,H]
  refine ⟨l₀,?_,?_,?_,C,?_⟩
  · intro h
    apply hl
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (j v)) h
    simpa only [l₀,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply,zero_apply] using hh
  · rw [coordinateMetricGradient_eq]
    simpa only [l₀,j,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hla
  · intro c
    apply (coordinateProfileStrict_iff_tangent g u x _).mpr
    rw [hform]
    exact hlS c
  · intro c hc
    apply (coordinateProfileFull_iff_tangent g u x _).mpr
    rw [hform]
    exact hlF c hc


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.prepDualNorm
attribute [local instance] OAI.YauCounterexamples.prepDualSpace
local instance prepFormNorm_r1d770e_1 : NormedAddCommGroup (CoordinateForm E) := inferInstance
attribute [local instance] OAI.YauCounterexamples.prepFormSpace
omit [FiniteDimensional ℝ E] in
lemma continuous_profileRankOne {X : Type*} [TopologicalSpace X]
    {l : X → E →L[ℝ] ℝ} (hl : Continuous l) : Continuous (fun x => profileRankOne (l x)) :=
  ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hl).clm_apply hl

omit [FiniteDimensional ℝ E] in
lemma continuous_metricProfileTraceForm_comp {X : Type*} [TopologicalSpace X]
    {B H : X → CoordinateForm E} {a : X → E}
    (hB : Continuous B) (hH : Continuous H) (ha : Continuous a) :
    Continuous (fun x => metricProfileTraceForm (B x) (H x) (a x)) := by
  unfold metricProfileTraceForm
  exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
    ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

lemma coordinateMetricGradient_ne_zero_dual (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (ha : coordinateMetricGradient g u x ≠ 0) :
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 := by
  intro h
  have hd : fderiv ℝ u x = 0 := (InnerProductSpace.toDual ℝ E).symm.injective
    (by simpa only [map_zero] using h)
  apply ha
  simp only [coordinateMetricGradient,hd,map_zero]

theorem exists_actual_preparation_neighborhood_oai (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {p : E}
    (ha : coordinateMetricGradient g u p ≠ 0) (hs : actualProfileStrict g u p) :
    ∃ (W : Set E) (s : E → ℝ) (C : ℝ), IsOpen W ∧ p ∈ W ∧
      ContDiff ℝ ∞ s ∧ 0 < C ∧ ∀ x ∈ W,
        fderiv ℝ s x ≠ 0 ∧ fderiv ℝ s x (coordinateMetricGradient g u x) = 0 ∧
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0) ∧
        (∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
        (∀ c ∈ Icc C (2*C), quadraticPlaneFull
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) := by
  obtain ⟨l,hl,hla,hlS,C₀,hlF⟩ := exists_actual_preparation_covector hd g u p ha hs
  obtain ⟨O,s₀,hOo,hOp,hs₀,hs₀p,hs₀d,hfirst⟩ :=
    smooth_first_integral (contDiff_coordinateMetricGradient g hu) ha l hl hla
  obtain ⟨s,hs,he⟩ := smooth_extension_near_compact isCompact_singleton hOo
    (singleton_subset_iff.mpr hOp) hs₀
  have he' : s₀ =ᶠ[𝓝 p] s := by simpa only [nhdsSet_singleton] using he
  have hsp : fderiv ℝ s p = l := by rw [←he'.fderiv_eq (𝕜:=ℝ),hs₀d]
  have hf : ∀ᶠ x in 𝓝 p, fderiv ℝ s x ≠ 0 ∧
      fderiv ℝ s x (coordinateMetricGradient g u x) = 0 := by
    filter_upwards [he'.fderiv (𝕜:=ℝ),hOo.mem_nhds hOp] with x hx hxO
    simpa only [←hx] using hfirst x hxO
  let C : ℝ := C₀+1
  have hC : 0 < C := by dsimp [C]; positivity
  let q : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
  have hq : Continuous q := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hu.continuous_fderiv (by simp))
  have hqn : q p ≠ 0 := coordinateMetricGradient_ne_zero_dual g u p ha
  let T : E × ℝ → CoordinateForm E := fun z => metricProfileTraceForm
    (selfMetricFlat g z.1) (actualCoordinateHessian g u z.1+z.2 • profileRankOne (fderiv ℝ s z.1))
    (coordinateMetricGradient g u z.1)
  have hH : Continuous (actualCoordinateHessian g u) :=
    continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hu
  have hT : Continuous T := continuous_metricProfileTraceForm_comp
    ((contDiff_selfMetricFlat g).continuous.comp continuous_fst)
    ((hH.comp continuous_fst).add (continuous_snd.smul
      (continuous_profileRankOne ((hs.continuous_fderiv (by simp)).comp continuous_fst))))
    ((contDiff_coordinateMetricGradient g hu).continuous.comp continuous_fst)
  have hmap : Continuous (fun z : E × ℝ => (T z,q z.1)) := hT.prodMk (hq.comp continuous_fst)
  have hstrict : ∀ᶠ x in 𝓝 p, ∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict (T (x,c)) (q x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro c hc
    have hp : quadraticPlaneStrict (T (p,c)) (q p) := by
      dsimp only [T,q]
      rw [hsp]
      exact hlS c
    exact (quadraticPlaneStrict_eventually hqn hp).filter_mono hmap.continuousAt
  have hfull : ∀ᶠ x in 𝓝 p, ∀ c ∈ Icc C (2*C), quadraticPlaneFull (T (x,c)) (q x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro c hc
    have hp : quadraticPlaneFull (T (p,c)) (q p) := by
      dsimp only [T,q]
      rw [hsp]
      apply hlF c
      have hh : (C₀:ℝ) < C := by dsimp [C]; linarith
      exact hh.le.trans hc.1
    exact (hmap.continuousAt (x:=(p,c))).eventually (isOpen_quadraticPlaneFull.mem_nhds hp)
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.mem_nhds_iff.mp
    (hf.and ((hq.continuousAt.eventually_ne hqn).and (hstrict.and hfull)))
  exact ⟨W,s,C,hWo,hWp,hs,hC,fun x hx =>
    ⟨(hW hx).1.1,(hW hx).1.2,(hW hx).2.1,(hW hx).2.2.1,(hW hx).2.2.2⟩⟩

end YauCounterexamples

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.exists_actual_preparation_neighborhood_oai.{u_1} := @OAI.YauCounterexamples.exists_actual_preparation_neighborhood_oai.{u_1}
