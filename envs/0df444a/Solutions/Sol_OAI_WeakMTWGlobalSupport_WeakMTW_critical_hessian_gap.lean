-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.critical_hessian_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:05:50.944983+00:00
-- url     : https://prove2.me/submissions/4184ed2f-f054-4e09-b88d-c309a903f40f

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_critical_jensen
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_minimizing_vector
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exp_coordinates_local_inverse
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_initialCost_geometry
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_radialSplitAction_smooth

section
-- module Solutions.OAIQW_WeakMTW.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem curveState_continuous {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ) :
    Continuous (curveState (E := E) γ) := by
  have h := hγ.continuous_tangentMap (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hs : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  exact h.comp hs

end

 theorem intrinsic_germ_unique {γ η : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η)
    {a C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (γ s) (γ t) = C * |s - t|)
    (hdDist : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (η s) (η t) = D * |s - t|)
    (he : curveState (E := E) γ a = curveState (E := E) η a) : γ =ᶠ[𝓝 a] η := by
  let x := γ a
  let e := chartAt E x
  have hpoint : γ a = η a := congrArg TotalSpace.proj he
  have hγa : γ a ∈ e.source := mem_chart_source E (γ a)
  have hηa : η a ∈ e.source := by rw [← hpoint]; exact hγa
  obtain ⟨ε, hε, hcs⟩ := hcDist
  obtain ⟨δ, hδ, hds⟩ := hdDist
  let U : Set ℝ := Metric.ball a ε ∩ Metric.ball a δ ∩
    (γ ⁻¹' e.source ∩ η ⁻¹' e.source)
  have hU : IsOpen U := (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
    ((e.open_source.preimage hγ.continuous).inter (e.open_source.preimage hη.continuous))
  have ha : a ∈ U := ⟨⟨Metric.mem_ball_self hε, Metric.mem_ball_self hδ⟩, hγa, hηa⟩
  let c : ℝ → E := e ∘ γ
  let d : ℝ → E := e ∘ η
  have hc : ContDiffOn ℝ ∞ c U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hγ.contMDiffOn (fun t ht => ht.2.1))
  have hd : ContDiffOn ℝ ∞ d U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hη.contMDiffOn (fun t ht => ht.2.2))
  have hct : ∀ t ∈ U, c t ∈ e.target := fun t ht => e.map_source ht.2.1
  have hdt : ∀ t ∈ U, d t ∈ e.target := fun t ht => e.map_source ht.2.2
  have he' : deriv c a = deriv d a := by
    rw [curveState_chart_deriv x (hγ.mdifferentiable (by simp) a) hγa,
      curveState_chart_deriv x (hη.mdifferentiable (by simp) a) hηa, he]
  have hh := coordinate_germ_unique x hU hc hd hct hdt ha hC hD
    (fun s hs t ht => by
      change dist (e.symm (e (γ s))) (e.symm (e (γ t))) = _
      rw [e.left_inv hs.2.1, e.left_inv ht.2.1]
      exact hcs s hs.1.1 t ht.1.1)
    (fun s hs t ht => by
      change dist (e.symm (e (η s))) (e.symm (e (η t))) = _
      rw [e.left_inv hs.2.2, e.left_inv ht.2.2]
      exact hds s hs.1.2 t ht.1.2)
    (congrArg e hpoint) he'
  filter_upwards [hh, hU.mem_nhds ha] with t ht htU
  have hh' := congrArg e.symm ht
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh'
  rwa [e.left_inv htU.2.1, e.left_inv htU.2.2] at hh'

 theorem intrinsic_global_unique {γ η : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∀ a, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (γ s) (γ t) = C * |s - t|)
    (hdDist : ∀ a, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (η s) (η t) = D * |s - t|)
    {a : ℝ} (he : curveState (E := E) γ a = curveState (E := E) η a) : γ = η := by
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  let A : Set ℝ := {t | curveState (E := E) γ t = curveState (E := E) η t}
  have hclosed : IsClosed A := isClosed_eq (curveState_continuous hγ) (curveState_continuous hη)
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hg := intrinsic_germ_unique hγ hη hC hD (hcDist t) (hdDist t) ht
    exact hg.eventuallyEq_nhds.mono (fun s hs => curveState_congr hs)
  have huniv : A = univ := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ ⟨a, he⟩
  funext t
  have h : t ∈ A := by rw [huniv]; exact mem_univ t
  exact congrArg TotalSpace.proj h
end
end RiemannianLocal

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem completeGeodesic_unique {x : M} {v : TangentSpace (model n) x} {γ η : ℝ → M}
    (hγ : CompleteGeodesicWithInitialData x v γ)
    (hη : CompleteGeodesicWithInitialData x v η) : γ = η := by
  obtain ⟨hγs, hγx, hγv, hγd⟩ := hγ
  obtain ⟨hηs, hηx, hηv, hηd⟩ := hη
  apply intrinsic_global_unique hγs hηs (norm_nonneg v) (norm_nonneg v) hγd hηd
    (a := 0)
  refine TotalSpace.ext (hγx.trans hηx.symm) ?_
  dsimp only [curveState]
  exact (eqRec_heq_iff.mp (heq_of_eq hγv)).trans
    (eqRec_heq_iff.mp (heq_of_eq hηv)).symm
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_TangentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
open ChartMetric CoordinateGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

 theorem stateChart_source (x : M) (p : TangentBundle 𝓘(ℝ, E) M) :
    p ∈ (stateChart x).source ↔ p.1 ∈ (chartAt E x).source :=
  TangentBundle.mem_chart_source_iff _ _

 theorem stateChart_target (x : M) (q : E × E) :
    q ∈ (stateChart x).target ↔ q.1 ∈ (chartAt E x).target :=
  TangentBundle.mem_chart_target_iff _ _

 theorem stateChart_symm (x : M) {q : E × E} (hq : q.1 ∈ (chartAt E x).target) :
    (stateChart x).symm q =
      (⟨(chartAt E x).symm q.1,chartLift x q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M) := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : (chartAt E x).symm q.1 ∈ e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet] using (chartAt E x).map_target hq
  change e.toOpenPartialHomeomorph.symm ((chartAt E x).symm q.1,q.2) = _
  change e.toOpenPartialHomeomorph.symm ((chartAt E x).symm q.1,q.2) =
    (⟨(chartAt E x).symm q.1,e.symmL ℝ ((chartAt E x).symm q.1) q.2⟩ : TangentBundle 𝓘(ℝ, E) M)
  rw [e.symmL_apply hb,e.mk_symm hb]

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

 theorem stateChart_energy (x : M) {q : E × E} (hq : q.1 ∈ (chartAt E x).target) :
    Real.sqrt (metric x q.1 q.2 q.2) = ‖((stateChart x).symm q).2‖ := by
  rw [stateChart_symm x hq,metric_apply,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

 theorem coordinate_curve_state_chart (x : M) {q : ℝ → E × E} {t : ℝ}
    (ht : (q t).1 ∈ (chartAt E x).target)
    (hq : HasDerivAt q (geodesicSpray (metric x) (q t)) t) :
    curveState (E := E) (fun s => (chartAt E x).symm (q s).1) t =
      (stateChart x).symm (q t) := by
  rw [coordinate_curve_state x ht hq,stateChart_symm x ht]

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
open ChartMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

 theorem stateChart_pairing (x y : M) (hy : y ∈ (chartAt E x).source)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    metric x (chartAt E x y) (stateChart x ⟨y,v⟩).2 (stateChart x ⟨y,w⟩).2 = inner ℝ v w := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : y ∈ e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet] using hy
  rw [metric_apply]
  change inner ℝ (e.symmL ℝ ((chartAt E x).symm (chartAt E x y)) (e ⟨y,v⟩).2)
    (e.symmL ℝ ((chartAt E x).symm (chartAt E x y)) (e ⟨y,w⟩).2) = inner ℝ v w
  rw [(chartAt E x).left_inv hy]
  simp only [e.symmL_apply hb, e.symm_apply_apply_mk hb]

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_PairNormalDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry NormalCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

 theorem normal_zero (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (x, (0 : E)) ∈ N.normal.source) : N.normal (x,0) = (x,x) := by
  apply Prod.ext
  · simp only [N.normal_apply]
  · exact N.normalAt_zero hS hG hpos hx

 theorem normal_inverse_hasFDerivAt_center (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (x, (0 : E)) ∈ N.normal.source) :
    HasFDerivAt N.normal.symm
      ((normalShear (E := E) N.time N.time_pos.ne').symm : E × E →L[ℝ] E × E) (x,x) := by
  have he := N.normal_zero hS hG hpos hx
  have hmem : (x,x) ∈ N.normal.target := he ▸ N.normal.map_source hx
  have hi : N.normal.symm (x,x) = (x,0) := by rw [← he, N.normal.left_inv hx]
  have hd := hasFDerivAt_normalMap_zero hS hG hpos N.domain_open N.flow_smooth
    N.initial N.ode (N.base_mem hx) N.time_pos (N.source_stays (x,0) hx)
  have hd' : HasFDerivAt N.normal
      (normalShear (E := E) N.time N.time_pos.ne' : E × E →L[ℝ] E × E)
      (N.normal.symm (x,x)) := by
    rw [hi]
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall N.normal_apply)
  exact N.normal.hasFDerivAt_symm hmem hd'
end
end NormalNeighborhood.NormalFlow

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem eventually_dist_normal_pair (x z₀ : M) (hz₀ : z₀ ∈ (chartAt E x).source)
    (N : NormalFlow (metric x) (chartAt E x).target (chartAt E x z₀)) :
    ∀ᶠ q : M × M in 𝓝 (z₀,z₀), dist q.1 q.2 = N.time *
      Real.sqrt (metric x (chartAt E x q.1)
        (N.normal.symm (chartAt E x q.1, chartAt E x q.2)).2
        (N.normal.symm (chartAt E x q.1, chartAt E x q.2)).2) := by
  let c := chartAt E x
  have hc : ContinuousAt c z₀ := c.continuousAt hz₀
  have hcc : ContinuousAt (fun q : M × M => (c q.1,c q.2)) (z₀,z₀) :=
    (hc.comp continuousAt_fst).prodMk (hc.comp continuousAt_snd)
  have he := N.normal_zero c.open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) N.center_mem
  have ht : (c z₀,c z₀) ∈ N.normal.target := he ▸ N.normal.map_source N.center_mem
  have hi : N.normal.symm (c z₀,c z₀) = (c z₀,0) := by rw [← he, N.normal.left_inv N.center_mem]
  obtain ⟨ε,r,hε,hr,hball⟩ := uniform_normal_radius x z₀ hz₀ N
  let ν : M × M → E := fun q => (N.normal.symm (c q.1,c q.2)).2
  have hν : ContinuousAt ν (z₀,z₀) := ((N.normal.continuousOn_symm _ ht).continuousAt
     (N.normal.open_target.mem_nhds ht)).comp
       (f := fun q : M × M => (c q.1,c q.2)) hcc |>.snd
  have hG : ContinuousAt (fun q : M × M => metric x (c q.1)) (z₀,z₀) := by
    apply ContinuousAt.comp (g := metric x) (f := fun q : M × M => c q.1)
    · exact (metric_smooth x).continuousOn.continuousAt
        (c.open_target.mem_nhds (c.map_source hz₀))
    · exact hc.comp continuousAt_fst
  have hlen : ContinuousAt (fun q : M × M => N.time * Real.sqrt (metric x (c q.1) (ν q) (ν q)))
      (z₀,z₀) := continuousAt_const.mul ((hG.clm_apply hν).clm_apply hν).sqrt
  have hsmall : ∀ᶠ q : M × M in 𝓝 (z₀,z₀), N.time * Real.sqrt (metric x (c q.1) (ν q) (ν q)) < r := by
    apply hlen.eventually_lt_const
    simpa [ν,hi] using hr
  have hnear : ∀ᶠ q : M × M in 𝓝 (z₀,z₀), q.1 ∈ Metric.ball z₀ ε ∧ q.2 ∈ c.source ∧
      (c q.1,c q.2) ∈ N.normal.target :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
      (inter_mem (continuousAt_snd.preimage_mem_nhds (c.open_source.mem_nhds hz₀))
        (hcc.preimage_mem_nhds (N.normal.open_target.mem_nhds ht)))
  filter_upwards [hnear,hsmall] with q hq hqs
  obtain ⟨hz,hzero,hrs⟩ := hball q.1 hq.1
  have hqt : q.2 ∈ (normalChart x q.1 N).target := ⟨hq.2.1,hq.2.2⟩
  have hh := normal_distance_of_ball x q.1 N hz hzero hr hrs
    ((normalChart x q.1 N).map_target hqt) hqs
  rw [(normalChart x q.1 N).right_inv hqt] at hh
  exact hh
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_TwoPointSpeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 omit [FiniteDimensional ℝ E] in
 theorem varying_quadratic_speed_eq {B : ℝ → MetricTensor E} {v : ℝ → E} {w : E} {a K : ℝ}
    (hB : ContinuousAt B a) (hd : HasDerivAt v w a) (hzero : v a = 0)
    (he : ∀ᶠ t in 𝓝[>] a, B t (v t) (v t) = K * (t-a)^2) : B a w w = K := by
  have hc : Continuous (fun q : MetricTensor E × E => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hBt : Tendsto B (𝓝[≠] a) (𝓝 (B a)) := hB.tendsto.mono_left nhdsWithin_le_nhds
  have hl := hc.tendsto (B a,w) |>.comp (hBt.prodMk_nhds hd.tendsto_slope)
  have hl' : Tendsto (fun t => B t (slope v a t) (slope v a t)) (𝓝[>] a) (𝓝 (B a w w)) :=
    hl.mono_left (nhdsWithin_mono _ (fun _ ht => ne_of_gt ht))
  have he' : (fun t => B t (slope v a t) (slope v a t)) =ᶠ[𝓝[>] a] (fun _ => K) := by
    filter_upwards [he,self_mem_nhdsWithin] with t ht hta
    have hne : t-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hta)
    simp only [slope,hzero,vsub_eq_sub,sub_zero,map_smul,smul_apply,smul_eq_mul]
    rw [ht]
    field_simp
  exact tendsto_nhds_unique hl' (tendsto_const_nhds.congr' he'.symm)
end
end CoordinateGeometry

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry NormalCoordinates

 theorem two_point_coordinate_speed (x : M) {a b : ℝ → E} {u v : E} {C : ℝ}
    (ha : HasDerivAt a u 0) (hb : HasDerivAt b v 0) (hab : a 0 = b 0)
    (hat : a 0 ∈ (chartAt E x).target)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      dist ((chartAt E x).symm (a t)) ((chartAt E x).symm (b t)) = C*t) :
    metric x (a 0) (v-u) (v-u) = C ^ 2 := by
  let c := chartAt E x
  let z := c.symm (a 0)
  have hz : z ∈ c.source := c.map_target hat
  have hcz : c z = a 0 := c.right_inv hat
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) (c.map_source hz)
  have hzero : (a 0, (0 : E)) ∈ N.normal.source := by
    simpa only [hcz] using N.center_mem
  let ν : ℝ → E := fun t => (N.normal.symm (a t,b t)).2
  have hd : HasDerivAt ν (N.time⁻¹ • (v-u)) 0 := by
    have hD := N.normal_inverse_hasFDerivAt_center c.open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) hzero
    have hD' : HasFDerivAt N.normal.symm
        ((normalShear (E := E) N.time N.time_pos.ne').symm : E × E →L[ℝ] E × E) (a 0,b 0) := by
      simpa only [← hab] using hD
    have hh := hD'.comp_hasDerivAt 0 (ha.prodMk hb)
    have hh' := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt 0 hh
    exact hh'

  have hν₀ : ν 0 = 0 := by
    have hh := N.normal.left_inv hzero
    rw [N.normal_zero c.open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) hzero] at hh
    simpa only [ν,hab] using congrArg Prod.snd hh
  have hγa : ContinuousAt (fun t => c.symm (a t)) 0 := (c.symm.continuousAt hat).comp ha.continuousAt
  have hγb : ContinuousAt (fun t => c.symm (b t)) 0 :=
    (c.symm.continuousAt (hab ▸ hat)).comp hb.continuousAt
  have hp : Tendsto (fun t => (c.symm (a t),c.symm (b t))) (𝓝 (0 : ℝ)) (𝓝 (z,z)) := by
    simpa only [← hab, z] using (hγa.prodMk hγb).tendsto
  have hpair : ∀ᶠ t in 𝓝 (0 : ℝ), dist (c.symm (a t)) (c.symm (b t)) = N.time *
      Real.sqrt (metric x (c (c.symm (a t)))
        (N.normal.symm (c (c.symm (a t)),c (c.symm (b t)))).2
        (N.normal.symm (c (c.symm (a t)),c (c.symm (b t)))).2) :=
    hp (eventually_dist_normal_pair x z hz N)
  have hG : ContinuousAt (fun t => metric x (a t)) 0 :=
    ((metric_smooth x).continuousOn.continuousAt (c.open_target.mem_nhds hat)).comp ha.continuousAt
  have hnearA : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ c.target :=
    ha.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds hat)
  have hnearB : ∀ᶠ t in 𝓝 (0 : ℝ), b t ∈ c.target :=
    hb.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds (hab ▸ hat))
  have hquad : ∀ᶠ t in 𝓝[>] (0 : ℝ), metric x (a t) (ν t) (ν t) = (C/N.time)^2 * (t-0)^2 := by
    filter_upwards [he,hpair.filter_mono nhdsWithin_le_nhds,
      hnearA.filter_mono nhdsWithin_le_nhds, hnearB.filter_mono nhdsWithin_le_nhds]
      with t het hpt hat' hbt'
    change dist (c.symm (a t)) (c.symm (b t)) = _ at hpt
    rw [c.right_inv hat', c.right_inv hbt'] at hpt
    have hpos : 0 ≤ metric x (a t) (ν t) (ν t) := by
      by_cases hv : ν t = 0
      · simp [hv]
      · exact (metric_positive x hat' hv).le
    have hs : Real.sqrt (metric x (a t) (ν t) (ν t)) = C*t/N.time := by
      apply (eq_div_iff N.time_pos.ne').mpr
      nlinarith [hpt,het]
    have hsq := Real.sq_sqrt hpos
    rw [hs] at hsq
    rw [← hsq]
    ring
  have hh := varying_quadratic_speed_eq hG hd hν₀ hquad
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hT := N.time_pos.ne'
  field_simp at hh
  nlinarith
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
 theorem curveState_comp_affine {γ : ℝ → M} {t a b : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (a*t+b)) :
    curveState (E := E) (fun s => γ (a*s+b)) t = mulState a (curveState (E := E) γ (a*t+b)) := by
  refine TotalSpace.ext ?_ ?_
  · rfl
  apply heq_of_eq
  dsimp only [curveState, mulState]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ fun s => a*s+b) t 1 = _
  have hd : HasDerivAt (fun s : ℝ => a*s+b) a t := by
    simpa using ((hasDerivAt_id t).const_mul a).add_const b
  have hs := mdifferentiableAt_iff_differentiableAt.mpr hd.differentiableAt
  rw [mfderiv_comp t hγ hs]
  simp only [mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (a*t+b) (fderiv ℝ (fun s : ℝ => a*s+b) t 1) = _
  rw [fderiv_apply_one_eq_deriv, hd.deriv]
  let derivative : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (γ (a*t+b)) :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (a*t+b)
  change derivative a = a • derivative 1
  simpa only [smul_eq_mul, mul_one] using derivative.map_smul a (1 : ℝ)

 theorem intrinsic_affine_dist {γ : ℝ → M} {C a b : ℝ}
    (hγ : ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
      dist (γ s) (γ r) = C * |s-r|) :
    ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
      dist (γ (a*s+b)) (γ (a*r+b)) = (|a| * C) * |s-r| := by
  intro t
  obtain ⟨ε, hε, hh⟩ := hγ (a*t+b)
  have ha : 0 < |a|+1 := by positivity
  refine ⟨ε/(|a|+1), div_pos hε ha, ?_⟩
  have hm : ∀ s ∈ Metric.ball t (ε/(|a|+1)), a*s+b ∈ Metric.ball (a*t+b) ε := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs ⊢
    have hs' := (lt_div_iff₀ ha).mp hs
    rw [show a*s+b-(a*t+b) = a*(s-t) by ring, abs_mul]
    nlinarith [abs_nonneg (s-t)]
  intro s hs r hr
  rw [hh _ (hm s hs) _ (hm r hr), show a*s+b-(a*r+b) = a*(s-r) by ring, abs_mul]
  ring
end
end RiemannianLocal

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] in
 theorem completeGeodesic_iff_state (x : M) (v : TangentSpace (model n) x) (γ : ℝ → M) :
    CompleteGeodesicWithInitialData x v γ ↔
      ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ γ ∧ curveState (E := Model n) γ 0 = ⟨x,v⟩ ∧
      ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
        dist (γ s) (γ r) = ‖v‖ * |s-r| := by
  constructor
  · rintro ⟨hγ, hx, hv, hd⟩
    refine ⟨hγ, TotalSpace.ext hx ?_, hd⟩
    exact eqRec_heq_iff.mp (heq_of_eq hv)
  · rintro ⟨hγ, hs, hd⟩
    have hp := TotalSpace.ext_iff.mp hs
    exact ⟨hγ, hp.1, eq_of_heq (eqRec_heq_iff.mpr hp.2), hd⟩

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] in
 theorem completeGeodesic_comp_mul {x : M} {v : TangentSpace (model n) x} {γ : ℝ → M}
    (hγ : CompleteGeodesicWithInitialData x v γ) (a : ℝ) :
    CompleteGeodesicWithInitialData x (a • v) (fun t => γ (a*t)) := by
  obtain ⟨hγs, hγ₀, hγd⟩ := (completeGeodesic_iff_state x v γ).mp hγ
  apply (completeGeodesic_iff_state _ _ _).mpr
  refine ⟨hγs.comp (contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)), ?_, ?_⟩
  · have hh := curveState_comp_affine (E := Model n) (γ := γ) (a := a) (b := 0) (t := 0)
      (hγs.mdifferentiable (by simp) _)
    simp only [add_zero, mul_zero] at hh
    rw [hγ₀] at hh
    exact hh
  · simpa only [add_zero, norm_smul, Real.norm_eq_abs] using
      (intrinsic_affine_dist (a := a) (b := 0) hγd)

 theorem exp_eq_of_complete {x : M} {v : TangentSpace (model n) x} {γ : ℝ → M}
    (hγ : CompleteGeodesicWithInitialData x v γ) : exp x v = γ 1 := by
  classical
  have hx : ∃ y, ExpEndpoint x v y := ⟨γ 1, γ, hγ, rfl⟩
  unfold exp
  rw [dite_eq_left hx]
  obtain ⟨η, hη, he⟩ := Classical.choose_spec hx
  rw [← he, completeGeodesic_unique hη hγ]

 theorem exp_mul_eq_of_complete {x : M} {v : TangentSpace (model n) x} {γ : ℝ → M}
    (hγ : CompleteGeodesicWithInitialData x v γ) (a : ℝ) : exp x (a • v) = γ a := by
  simpa only [mul_one] using exp_eq_of_complete (completeGeodesic_comp_mul hγ a)

variable [CompactSpace M]

 theorem geodesic_complete (p : TangentBundle (model n) M) :
    CompleteGeodesicWithInitialData p.1 p.2 (geodesic p) :=
  Classical.choose_spec (completeGeodesic_exists p.1 p.2)

 theorem geodesic_smooth (p : TangentBundle (model n) M) :
    ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ (geodesic p) := (geodesic_complete p).1

 theorem geodesic_state_zero (p : TangentBundle (model n) M) :
    curveState (E := Model n) (geodesic p) 0 = p :=
  ((completeGeodesic_iff_state _ _ _).mp (geodesic_complete p)).2.1

 theorem geodesic_dist (p : TangentBundle (model n) M) :
    ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
      dist (geodesic p s) (geodesic p r) = ‖p.2‖ * |s-r| :=
  ((completeGeodesic_iff_state _ _ _).mp (geodesic_complete p)).2.2

 theorem geodesic_zero (p : TangentBundle (model n) M) : geodesic p 0 = p.1 :=
  congrArg TotalSpace.proj (geodesic_state_zero p)

 theorem exp_eq_geodesic (x : M) (v : TangentSpace (model n) x) :
    exp x v = geodesic ⟨x,v⟩ 1 := exp_eq_of_complete (geodesic_complete _)

 theorem exp_mul_eq_geodesic (p : TangentBundle (model n) M) (t : ℝ) :
    exp p.1 (t • p.2) = geodesic p t := exp_mul_eq_of_complete (geodesic_complete p) t

 theorem exp_zero (x : M) : exp x (0 : TangentSpace (model n) x) = x := by
  simpa only [zero_smul, geodesic_zero] using exp_mul_eq_geodesic (⟨x,0⟩ : TangentBundle (model n) M) 0

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GeodesicFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesic_intrinsic (p : TangentBundle (model n) M) :
    IsIntrinsicGeodesicOn (E := Model n) (geodesic p) ‖p.2‖ univ :=
  ⟨(geodesic_smooth p).contMDiffOn, fun t _ => geodesic_dist p t⟩

 theorem geodesicFlow_zero (p : TangentBundle (model n) M) : geodesicFlow 0 p = p := geodesic_state_zero p

 theorem geodesicFlow_norm (t : ℝ) (p : TangentBundle (model n) M) :
    ‖(geodesicFlow t p).2‖ = ‖p.2‖ :=
  intrinsic_state_norm isOpen_univ (norm_nonneg p.2) (geodesic_intrinsic p) (mem_univ t)

 theorem geodesicFlow_continuous_time (p : TangentBundle (model n) M) :
    Continuous (fun t => geodesicFlow t p) := curveState_continuous (geodesic_smooth p)

 theorem geodesic_shift_complete (t : ℝ) (p : TangentBundle (model n) M) :
    CompleteGeodesicWithInitialData (geodesicFlow t p).1 (geodesicFlow t p).2
      (fun s => geodesic p (s+t)) := by
  apply (completeGeodesic_iff_state _ _ _).mpr
  refine ⟨(geodesic_smooth p).comp (contMDiff_iff_contDiff.mpr (contDiff_id.add contDiff_const)), ?_, ?_⟩
  · have hh := curveState_comp_affine (E := Model n) (γ := geodesic p) (a := 1) (b := t) (t := 0)
      ((geodesic_smooth p).mdifferentiable (by simp) _)
    simp only [one_mul, zero_add] at hh
    simpa [mulState, geodesicFlow] using hh
  · rw [geodesicFlow_norm]
    simpa only [one_mul, abs_one] using (intrinsic_affine_dist (a := 1) (b := t) (geodesic_dist p))

 theorem geodesic_shift (t : ℝ) (p : TangentBundle (model n) M) :
    geodesic (geodesicFlow t p) = fun s => geodesic p (s+t) :=
  completeGeodesic_unique (geodesic_complete _) (geodesic_shift_complete t p)

 theorem geodesicFlow_add (s t : ℝ) (p : TangentBundle (model n) M) :
    geodesicFlow (s+t) p = geodesicFlow s (geodesicFlow t p) := by
  change curveState (E := Model n) (geodesic p) (s+t) =
    curveState (E := Model n) (geodesic (geodesicFlow t p)) s
  rw [geodesic_shift]
  have hh := curveState_comp_affine (E := Model n) (γ := geodesic p) (a := 1) (b := t) (t := s)
    ((geodesic_smooth p).mdifferentiable (by simp) _)
  simp only [one_mul] at hh
  simpa [mulState] using hh.symm

 theorem geodesicFlow_sub (s t : ℝ) (p : TangentBundle (model n) M) :
    geodesicFlow (s-t) (geodesicFlow t p) = geodesicFlow s p := by
  rw [← geodesicFlow_add, sub_add_cancel]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_LocalFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesicFlow_smooth_near_zero (p : TangentBundle (model n) M) :
    ∃ V : Set (ℝ × TangentBundle (model n) M), IsOpen V ∧ (0,p) ∈ V ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ((model n).prod (model n))) ((model n).prod (model n)) ∞
        (fun z => geodesicFlow z.1 z.2) V := by
  let x := p.1
  let c := chartAt (Model n) x
  let d := stateChart (E := Model n) x
  have hps : p ∈ d.source := (stateChart_source x p).mpr (mem_chart_source (Model n) x)
  let q₀ := d p
  have hq₀ : q₀.1 ∈ c.target := (stateChart_target x q₀).mp (d.map_source hps)
  obtain ⟨U, Φ, hU, h0, hΦ, hzero, hode⟩ := SmoothFlow.exists_smooth_local_flow
    (c.open_target.prod isOpen_univ) (contDiffOn_geodesicSpray c.open_target (metric_smooth x)
      (fun y hy v hv => metric_positive x hy hv)) (x₀ := q₀) ⟨hq₀, mem_univ _⟩
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let ε := R/2
  let J := Ioo (-ε) ε
  let W := Metric.ball q₀ ε
  have hε : 0 < ε := half_pos hR
  have hJU : ∀ t ∈ J, ∀ q ∈ W, (t,q) ∈ U := by
    intro t ht q hq
    apply hRU
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
    have hεR : ε < R := half_lt_self hR
    exact ⟨(abs_lt.mpr ht).trans hεR, hq.trans hεR⟩
  let B := d.source ∩ d ⁻¹' W
  have hB : IsOpen B := d.continuousOn.isOpen_inter_preimage d.open_source Metric.isOpen_ball
  have hpB : p ∈ B := ⟨hps, Metric.mem_ball_self hε⟩
  have h0J : (0 : ℝ) ∈ J := ⟨by linarith, hε⟩
  let V := J ×ˢ B
  refine ⟨V, isOpen_Ioo.prod hB, ⟨h0J, hpB⟩, ?_⟩
  have heq : ∀ z ∈ V, geodesicFlow z.1 z.2 = d.symm (Φ (z.1, d z.2)) := by
    intro z hz
    let q : ℝ → Model n × Model n := fun t => Φ (t, d z.2)
    have hqs : ContDiffOn ℝ ∞ q J := hΦ.comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => hJU t ht _ hz.2.2)
    have hqe : ∀ t ∈ J, (q t).1 ∈ c.target ∧ HasDerivAt q (geodesicSpray (metric x) (q t)) t :=
      fun t ht => ⟨(hode _ (hJU t ht _ hz.2.2)).1.1, (hode _ (hJU t ht _ hz.2.2)).2⟩
    have hqzero : q 0 = d z.2 := hzero _ (hJU 0 h0J _ hz.2.2)
    have hγ := coordinate_intrinsic x isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected hqs hqe h0J
    rw [hqzero] at hγ
    have hsqrt := stateChart_energy x ((stateChart_target x (d z.2)).mp (d.map_source hz.2.1))
    rw [d.left_inv hz.2.1] at hsqrt
    rw [hsqrt] at hγ
    have hγ₀ := coordinate_curve_state_chart x (hqe 0 h0J).1 (hqe 0 h0J).2
    rw [hqzero, d.left_inv hz.2.1] at hγ₀
    have hh := intrinsic_unique_on isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected
      (norm_nonneg z.2.2) (norm_nonneg z.2.2)
      ((geodesic_intrinsic z.2).mono (subset_univ J)) hγ h0J
      ((geodesic_state_zero z.2).trans hγ₀.symm)
    have hst : curveState (E := Model n) (geodesic z.2) z.1 =
        curveState (E := Model n) (fun t => c.symm (q t).1) z.1 := by
      apply curveState_congr
      filter_upwards [isOpen_Ioo.mem_nhds hz.1] with t ht
      exact hh ht
    rw [show geodesicFlow z.1 z.2 = curveState (E := Model n) (geodesic z.2) z.1 by rfl,
      hst, coordinate_curve_state_chart x (hqe z.1 hz.1).1 (hqe z.1 hz.1).2]
  have hd : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞ d d.source :=
    contMDiffOn_extChartAt (I := (model n).prod (model n)) (x := (⟨x,0⟩ : TangentBundle (model n) M))
  have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod ((model n).prod (model n)))
      𝓘(ℝ, ℝ × (Model n × Model n)) ∞ (fun z : ℝ × TangentBundle (model n) M => (z.1, d z.2)) V :=
    (contMDiffOn_prod_module_iff _).mpr ⟨contMDiffOn_fst,
      hd.comp contMDiffOn_snd (fun _ hz => hz.2.1)⟩
  have hf := (contMDiffOn_iff_contDiffOn.mpr hΦ).comp hc (fun z hz => hJU z.1 hz.1 _ hz.2.2)
  have hinv : ContMDiffOn 𝓘(ℝ, Model n × Model n) ((model n).prod (model n)) ∞ d.symm d.target :=
    by
      convert contMDiffOn_extChartAt_symm (I := (model n).prod (model n)) (n := ∞)
        (⟨x,0⟩ : TangentBundle (model n) M) using 1
      all_goals try rfl
      all_goals
        ext q
        simp [extChartAt, model, OpenPartialHomeomorph.extend, d, stateChart]
        rfl
  exact (hinv.comp hf (fun z hz => (stateChart_target x _).mpr
    (hode _ (hJU z.1 hz.1 _ hz.2.2)).1.1)).congr heq

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GlobalFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesicFlow_smooth_fixed (t : ℝ) :
    ContMDiff ((model n).prod (model n)) ((model n).prod (model n)) ∞
      (geodesicFlow (n := n) (M := M) t) := by
  intro p
  let P : ℝ → ℝ → Prop := fun a b =>
    ContMDiffAt ((model n).prod (model n)) ((model n).prod (model n)) ∞
      (geodesicFlow (b-a)) (geodesicFlow a p)
  have hlocal : ∀ a : ℝ, ∀ᶠ b in 𝓝 a, P a b ∧ P b a := by
    intro a
    obtain ⟨V, hV, hmem, hs⟩ := geodesicFlow_smooth_near_zero (geodesicFlow a p)
    have h1 : Continuous (fun b : ℝ => (b-a, geodesicFlow a p)) :=
      (continuous_id.sub continuous_const).prodMk continuous_const
    have h2 : Continuous (fun b : ℝ => (a-b, geodesicFlow b p)) :=
      (continuous_const.sub continuous_id).prodMk (geodesicFlow_continuous_time p)
    have h1' : ∀ᶠ b in 𝓝 a, (b-a, geodesicFlow a p) ∈ V := by
      apply h1.continuousAt.preimage_mem_nhds
      simpa only [sub_self] using hV.mem_nhds hmem
    have h2' : ∀ᶠ b in 𝓝 a, (a-b, geodesicFlow b p) ∈ V := by
      apply h2.continuousAt.preimage_mem_nhds
      simpa only [sub_self] using hV.mem_nhds hmem
    filter_upwards [h1', h2'] with b hb1 hb2
    constructor
    · exact ((hs _ hb1).contMDiffAt (hV.mem_nhds hb1)).comp _
        (contMDiffAt_const.prodMk contMDiffAt_id)
    · exact ((hs _ hb2).contMDiffAt (hV.mem_nhds hb2)).comp _
        (contMDiffAt_const.prodMk contMDiffAt_id)
  have htrans : IsTrans ℝ P := by
    refine ⟨?_⟩
    intro a b c hab hbc
    have hbc' : ContMDiffAt ((model n).prod (model n)) ((model n).prod (model n)) ∞
        (geodesicFlow (c-b)) (geodesicFlow (b-a) (geodesicFlow a p)) := by
      simpa only [geodesicFlow_sub] using hbc
    have hh := hbc'.comp _ hab
    convert hh using 1
    funext z
    dsimp only [Function.comp_def]
    rw [← geodesicFlow_add]
    congr 1
    ring
  have hh := PreconnectedSpace.induction₂' P hlocal htrans 0 t
  simpa only [P, sub_zero, geodesicFlow_zero] using hh

 theorem exp_total_smooth :
    ContMDiff ((model n).prod (model n)) (model n) ∞
      (fun p : TangentBundle (model n) M => exp p.1 p.2) := by
  have hh := (contMDiff_proj (TangentSpace (model n))).comp (geodesicFlow_smooth_fixed (n := n) (M := M) 1)
  convert hh using 1
  funext p
  exact exp_eq_geodesic p.1 p.2

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_FiberSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem fibre_inclusion_smooth (x : M) :
    ContMDiff 𝓘(ℝ, TangentSpace (model n) x) ((model n).prod (model n)) ∞
      (fun v : TangentSpace (model n) x => (⟨x,v⟩ : TangentBundle (model n) M)) := by
  let e := trivializationAt (Model n) (TangentSpace (model n)) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) x
  apply e.contMDiff_iff (fun _ => hx) |>.mpr
  refine ⟨contMDiff_const,?_⟩
  have hh : ContDiff ℝ ∞ (e.continuousLinearMapAt ℝ x) := ContinuousLinearMap.contDiff _
  apply (contMDiff_iff_contDiff.mpr hh).congr
  intro v
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hx v).symm

 theorem exp_fibre_smooth (x : M) :
    ContMDiff 𝓘(ℝ, TangentSpace (model n) x) (model n) ∞ (exp (n := n) x) :=
  (exp_total_smooth (n := n) (M := M)).comp (fibre_inclusion_smooth x)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GeodesicDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesic_pathELength (p : TangentBundle (model n) M) (a b : ℝ) :
    pathELength (model n) (geodesic p) a b = ENNReal.ofReal (‖p.2‖ * (b-a)) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have heq : (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) (model n) (geodesic p) t 1‖ₑ) =
      fun _ : ℝ => ENNReal.ofReal ‖p.2‖ := by
    funext t
    rw [← ofReal_norm]
    congr 1
    exact geodesicFlow_norm t p
  rw [heq, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, ← ENNReal.ofReal_mul (norm_nonneg _)]

 theorem geodesic_dist_le (p : TangentBundle (model n) M) (a b : ℝ) :
    dist (geodesic p a) (geodesic p b) ≤ ‖p.2‖ * |b-a| := by
  wlog hab : a ≤ b generalizing a b
  · rw [dist_comm, abs_sub_comm]
    exact this b a (le_of_not_ge hab)
  have hh := riemannianEDist_le_pathELength (I := model n) (γ := geodesic p)
    ((geodesic_smooth p).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn rfl rfl hab
  rw [← IsRiemannianManifold.out (I := model n), geodesic_pathELength, edist_dist] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hab))).mp hh

 theorem dist_exp_le (x : M) (v : TangentSpace (model n) x) :
    dist x (exp x v) ≤ ‖v‖ := by
  have hh := geodesic_dist_le (⟨x,v⟩ : TangentBundle (model n) M) 0 1
  have hz := congrArg TotalSpace.proj (geodesic_state_zero (⟨x,v⟩ : TangentBundle (model n) M))
  simpa only [show geodesic (⟨x,v⟩ : TangentBundle (model n) M) 0 = x from hz,
    ← exp_eq_geodesic, sub_zero, abs_one, mul_one] using hh

 theorem minimizing_radial {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ minimizingDomain x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • v ∈ minimizingDomain x := by
  change dist x (exp x (t • v)) = ‖t • v‖
  apply le_antisymm (dist_exp_le x _)
  have hh := geodesic_dist_le (⟨x,v⟩ : TangentBundle (model n) M) t 1
  rw [← exp_eq_geodesic, ← exp_mul_eq_geodesic] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr ht.2)] at hh
  have htri := dist_triangle x (exp x (t • v)) (exp x v)
  change dist x (exp x v) = ‖v‖ at hv
  rw [hv] at htri
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  nlinarith

 theorem injectivity_subset_minimizing (x : M) : injectivityDomain (n := n) x ⊆ minimizingDomain (n := n) x := by
  rintro v ⟨a,ha,he⟩
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have hmin : a • v ∈ minimizingDomain x := by
    change dist x (exp x (a • v)) = ‖a • v‖
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hapos]
  have hh := minimizing_radial hmin (t := a⁻¹) ⟨inv_nonneg.mpr hapos.le, (inv_le_one₀ hapos).mpr ha.le⟩
  simpa only [smul_smul, inv_mul_cancel₀ hapos.ne', one_smul] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_NoCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open ChartMetric CoordinateGeometry

 theorem coordinate_corner_deriv_eq (x : M) {c d : ℝ → E} {u v : E} {C : ℝ}
    (hc : HasDerivAt c u 0) (hd : HasDerivAt d v 0) (h0 : c 0 = d 0)
    (ht : c 0 ∈ (chartAt E x).target)
    (hu : metric x (c 0) u u = C ^ 2) (hv : metric x (c 0) v v = C ^ 2)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      dist ((chartAt E x).symm (c (-t))) ((chartAt E x).symm (d t)) = 2*C*t) : u = v := by
  have hc' : HasDerivAt (fun t => c (-t)) (-u) 0 := by
    simpa only [neg_zero,neg_smul,one_smul,Function.comp_def] using hc.scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
  have H := two_point_coordinate_speed x hc' hd (by simpa only [neg_zero] using h0)
    (by simpa only [neg_zero] using ht) he
  simp only [neg_zero, sub_neg_eq_add] at H
  have hsym := metric_symmetric x (c 0) u v
  have hz : metric x (c 0) (u-v) (u-v) = 0 := by
    simp only [map_add,add_apply] at H
    simp only [map_sub,sub_apply]
    nlinarith
  by_contra hne
  have hp := metric_positive x ht (sub_ne_zero.mpr hne)
  linarith

 theorem intrinsic_no_corner {γ η : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η)
    {C : ℝ} (hC : 0 ≤ C)
    (hγd : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball 0 ε, ∀ t ∈ Metric.ball 0 ε,
      dist (γ s) (γ t) = C * |s-t|)
    (hηd : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball 0 ε, ∀ t ∈ Metric.ball 0 ε,
      dist (η s) (η t) = C * |s-t|)
    (h0 : γ 0 = η 0)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (γ (-t)) (η t) = 2*C*t) :
    curveState (E := E) γ 0 = curveState (E := E) η 0 := by
  let x := γ 0
  let e := chartAt E x
  have hγ₀ : γ 0 ∈ e.source := mem_chart_source E (γ 0)
  have hη₀ : η 0 ∈ e.source := by rw [← h0]; exact hγ₀
  obtain ⟨ε,hε,hγdist⟩ := hγd
  obtain ⟨δ,hδ,hηdist⟩ := hηd
  let U : Set ℝ := Metric.ball 0 ε ∩ Metric.ball 0 δ ∩ (γ ⁻¹' e.source ∩ η ⁻¹' e.source)
  have hU : IsOpen U := (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
    ((e.open_source.preimage hγ.continuous).inter (e.open_source.preimage hη.continuous))
  have h0U : (0 : ℝ) ∈ U := ⟨⟨Metric.mem_ball_self hε,Metric.mem_ball_self hδ⟩,hγ₀,hη₀⟩
  let c := e ∘ γ
  let d := e ∘ η
  have hc : ContDiffOn ℝ ∞ c U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hγ.contMDiffOn (fun t ht => ht.2.1))
  have hd : ContDiffOn ℝ ∞ d U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hη.contMDiffOn (fun t ht => ht.2.2))
  have hcd : HasDerivAt c (deriv c 0) 0 :=
    (((hc 0 h0U).contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt
  have hdd : HasDerivAt d (deriv d 0) 0 :=
    (((hd 0 h0U).contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt
  have hct : ∀ t ∈ U, c t ∈ e.target := fun t ht => e.map_source ht.2.1
  have hdt : ∀ t ∈ U, d t ∈ e.target := fun t ht => e.map_source ht.2.2
  have hdistc : ∀ s ∈ U, ∀ t ∈ U, dist (e.symm (c s)) (e.symm (c t)) = C*|s-t| := by
    intro s hs t ht
    change dist (e.symm (e (γ s))) (e.symm (e (γ t))) = _
    rw [e.left_inv hs.2.1,e.left_inv ht.2.1]
    exact hγdist s hs.1.1 t ht.1.1
  have hdistd : ∀ s ∈ U, ∀ t ∈ U, dist (e.symm (d s)) (e.symm (d t)) = C*|s-t| := by
    intro s hs t ht
    change dist (e.symm (e (η s))) (e.symm (e (η t))) = _
    rw [e.left_inv hs.2.2,e.left_inv ht.2.2]
    exact hηdist s hs.1.2 t ht.1.2
  have hu := coordinate_speed_of_local_distance x hcd (hct 0 h0U) hC (by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [hdistc 0 h0U t ht,abs_sub_comm])
  have hv := coordinate_speed_of_local_distance x hdd (hdt 0 h0U) hC (by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [hdistd 0 h0U t ht,abs_sub_comm])
  have hcd0 : c 0 = d 0 := congrArg e h0
  rw [← hcd0] at hv
  have hec : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (e.symm (c (-t))) (e.symm (d t)) = 2*C*t := by
    have hneg : ∀ᶠ t in 𝓝 (0 : ℝ), -t ∈ U :=
      (continuous_neg.continuousAt.preimage_mem_nhds (by simpa only [neg_zero] using hU.mem_nhds h0U))
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ U := hU.mem_nhds h0U
    filter_upwards [he,hneg.filter_mono nhdsWithin_le_nhds,hmem.filter_mono nhdsWithin_le_nhds]
      with t ht hn hm
    change dist (e.symm (e (γ (-t)))) (e.symm (e (η t))) = _
    rwa [e.left_inv hn.2.1,e.left_inv hm.2.2]
  have hdereq := coordinate_corner_deriv_eq x hcd hdd hcd0 (hct 0 h0U) hu hv hec
  have hgerm := coordinate_germ_unique x hU hc hd hct hdt h0U hC hC hdistc hdistd hcd0 hdereq
  apply curveState_congr
  filter_upwards [hgerm,hU.mem_nhds h0U] with t ht htU
  have hh := congrArg e.symm ht
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh
  rwa [e.left_inv htU.2.1,e.left_inv htU.2.2] at hh
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_MinimizingCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesic_no_corner {p q : TangentBundle (model n) M}
    {C : ℝ} (hp : ‖p.2‖ = C) (hq : ‖q.2‖ = C) (h0 : p.1 = q.1)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (geodesic p (-t)) (geodesic q t) = 2*C*t) : p = q := by
  have hh := intrinsic_no_corner (geodesic_smooth p) (geodesic_smooth q)
    (hp ▸ norm_nonneg p.2) (hp ▸ geodesic_dist p 0) (hq ▸ geodesic_dist q 0)
    (by simpa only [geodesic_zero] using h0) he
  simpa only [geodesic_state_zero] using hh

 theorem minimizing_broken_eq {p q : TangentBundle (model n) M}
    {C : ℝ} (hp : ‖p.2‖ = C) (hq : ‖q.2‖ = C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hjoin : geodesic p a = q.1)
    (hd : dist p.1 (geodesic q b) = C * (a+b)) : geodesicFlow a p = q := by
  apply geodesic_no_corner (by rw [geodesicFlow_norm,hp]) hq hjoin
  have htpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hta : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a :=
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  have htb : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < b :=
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [htpos,hta,htb] with t ht hta htb
  rw [geodesic_shift]
  change dist (geodesic p (-t+a)) (geodesic q t) = 2*C*t
  have h1 := geodesic_dist_le p 0 (-t+a)
  have h2 := geodesic_dist_le p (-t+a) a
  have h3 := geodesic_dist_le q 0 t
  have h4 := geodesic_dist_le q t b
  rw [hp,geodesic_zero,sub_zero,abs_of_nonneg (by linarith)] at h1
  rw [hp,show a-(-t+a)=t by ring,abs_of_pos ht,hjoin] at h2
  rw [hq,geodesic_zero,sub_zero,abs_of_pos ht] at h3
  rw [hq,abs_of_pos (sub_pos.mpr htb)] at h4
  have hlo := dist_triangle p.1 (geodesic p (-t+a)) (geodesic q b)
  have hlo' := dist_triangle (geodesic p (-t+a)) (geodesic q t) (geodesic q b)
  rw [hd] at hlo
  have hhi := dist_triangle (geodesic p (-t+a)) q.1 (geodesic q t)
  linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_InjectivityUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_vector_unique_of_injectivity {x : M} {v w : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (hw : w ∈ minimizingDomain x)
    (he : exp x v = exp x w) : v = w := by
  have hvm := injectivity_subset_minimizing x hv
  have hn : ‖w‖ = ‖v‖ := by
    change dist x (exp x v) = ‖v‖ at hvm
    change dist x (exp x w) = ‖w‖ at hw
    rw [← he] at hw
    exact hw.symm.trans hvm
  obtain ⟨a,ha,hae⟩ := hv
  let p : TangentBundle (model n) M := ⟨x,v⟩
  let q : TangentBundle (model n) M := ⟨x,w⟩
  have hjoin : geodesic q 1 = (geodesicFlow 1 p).1 := by
    change geodesic q 1 = geodesic p 1
    simpa only [exp_eq_geodesic] using he.symm
  have hend : geodesic (geodesicFlow 1 p) (a-1) = exp x (a • v) := by
    simp only [geodesic_shift,sub_add_cancel]
    exact (exp_mul_eq_geodesic p a).symm
  have hd : dist q.1 (geodesic (geodesicFlow 1 p) (a-1)) = ‖v‖ * (1+(a-1)) := by
    rw [hend]
    change dist x (exp x (a • v)) = _
    rw [hae]
    ring
  have hs := minimizing_broken_eq (p := q) (q := geodesicFlow 1 p) hn
    (geodesicFlow_norm 1 p) zero_lt_one (sub_pos.mpr ha) hjoin hd
  have hs' := congrArg (geodesicFlow (-1)) hs
  rw [← geodesicFlow_add,← geodesicFlow_add] at hs'
  simp only [neg_add_cancel,geodesicFlow_zero] at hs'
  have hh : HEq w v := (TotalSpace.ext_iff.mp hs').2
  exact (eq_of_heq hh).symm

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_MinimizingSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_segment_dist (p : TangentBundle (model n) M) {L a b : ℝ}
    (hL : dist p.1 (geodesic p L) = L * ‖p.2‖)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    dist (geodesic p a) (geodesic p b) = (b-a) * ‖p.2‖ := by
  have h₁ := geodesic_dist_le p 0 a
  have h₂ := geodesic_dist_le p a b
  have h₃ := geodesic_dist_le p b L
  rw [geodesic_zero,sub_zero,abs_of_nonneg ha] at h₁
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h₂
  rw [abs_of_nonneg (sub_nonneg.mpr hb)] at h₃
  have ht := dist_triangle4 p.1 (geodesic p a) (geodesic p b) (geodesic p L)
  rw [hL] at ht
  nlinarith

end
end WeakMTW

namespace DiscreteVariational
 theorem weighted_two_sq (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (x+y)^2/(a+b) ≤ x^2/a + y^2/b := by
  have hsq := sq_nonneg (b*x-a*y)
  apply (div_le_iff₀ (add_pos ha hb)).mpr
  have he : (x^2/a+y^2/b)*(a+b) =
      ((x+y)^2*(a*b)+(b*x-a*y)^2)/(a*b) := by
    field_simp
    ring
  rw [he]
  exact (le_div_iff₀ (mul_pos ha hb)).mpr (le_add_of_nonneg_right hsq)

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_DiscreteVariationalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational

 theorem scalar_second_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hn' : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hM := isLocalMax_of_deriv_deriv_neg hn' hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm,hM] with y hy hy'
    exact le_antisymm hy' hy
  have hde : deriv f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [he.deriv] with y hy
    simpa using hy
  have hh := hde.deriv_eq
  simp only [deriv_const] at hh
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem line_second {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  have he : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 0]
      (fun t => fderiv ℝ f (x + t • v) v) := by
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using (hline 0).continuousAt.tendsto
    filter_upwards [ht (hf.eventually (by norm_num))] with t ht'
    change ContDiffAt ℝ 2 f (x+t • v) at ht'
    exact ((ht'.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [he.deriv_eq]
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have haa := hd.clm_apply (hasFDerivAt_const v x)
  have haa' : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((fderiv ℝ f x).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) x).flip v) (x+(0 : ℝ) • v) := by
    simpa using haa
  have hh := haa'.comp_hasDerivAt (0 : ℝ) (hline 0)
  simpa [Function.comp_def] using hh.deriv

 theorem hessian_nonneg {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hm : IsLocalMin f x) (v : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  rw [← line_second hf v]
  have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hm' : IsLocalMin (fun t : ℝ => f (x + t • v)) 0 := by
    have hm' : IsLocalMin f (x+(0 : ℝ) • v) := by simpa using hm
    exact IsLocalMin.comp_continuous (g := fun t : ℝ => x+t • v) hm' hc
  exact scalar_second_nonneg hm' (hf.continuousAt.comp_of_eq hc (by simp))

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_HessianNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem bilinear_psd_null_sum (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) {v : E} (hv : B v v = 0) (w : E) :
    B v w + B w v = 0 := by
  by_contra hn
  let c := B v w + B w v
  have hc : c ≠ 0 := hn
  have hh := hB (w - ((B w w + 1)/c) • v)
  simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,hv,mul_zero,sub_zero] at hh
  have he' : B w w - ((B w w+1)/c) * B w v - ((B w w+1)/c) * B v w = -1 := by
    field_simp [hc]
    dsimp [c]
    ring
  linarith

 theorem hessian_null_pair {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hm : IsLocalMin f x) {v : E} (hv : fderiv ℝ (fderiv ℝ f) x v v = 0) (w : E) :
    fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  have hh := bilinear_psd_null_sum (fderiv ℝ (fderiv ℝ f) x) (hessian_nonneg hf hm) hv w
  have hs := (hf.isSymmSndFDerivAt (by norm_num)).eq v w
  linarith

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_MinimizerCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizingDomain_closed (x : M) : IsClosed (minimizingDomain (n := n) x) :=
  isClosed_eq (continuous_const.dist (exp_fibre_smooth x).continuous) continuous_norm

 theorem minimizingDomain_compact (x : M) : IsCompact (minimizingDomain (n := n) x) := by
  let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  apply (isCompact_closedBall (0 : TangentSpace (model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
    (minimizingDomain_closed x)
  intro v hv
  rw [Metric.mem_closedBall,dist_zero_right]
  change dist x (exp x v) = ‖v‖ at hv
  rw [← hv]
  exact Metric.dist_le_diam_of_mem (isCompact_univ.isBounded) (mem_univ _) (mem_univ _)

 theorem minimizing_vectors_near_unique {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) {U : Set (TangentSpace (model n) x)}
    (hU : IsOpen U) (hvU : v ∈ U) :
    ∀ᶠ y in 𝓝 (exp x v), ∀ w ∈ minimizingDomain x, exp x w = y → w ∈ U := by
  let K := minimizingDomain (n := n) x \ U
  have hK : IsCompact K := (minimizingDomain_compact x).diff hU
  have hC := (hK.image (exp_fibre_smooth x).continuous).isClosed
  have hy : exp x v ∉ (exp x) '' K := by
    rintro ⟨w,hw,he⟩
    have hh := minimizing_vector_unique_of_injectivity hv hw.1 he.symm
    exact hw.2 (hh ▸ hvU)
  filter_upwards [hC.isOpen_compl.mem_nhds hy] with y hy
  intro w hw he
  by_contra hn
  exact hy ⟨w,⟨hw,hn⟩,he⟩

 theorem injectivity_mem_interior_minimizing {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : v ∈ interior (minimizingDomain x) := by
  let y := exp x v
  obtain ⟨e,he,hev,hes,_⟩ := exp_coordinates_local_inverse x y hv (mem_chart_source (Model n) y)
  have hn := minimizing_vectors_near_unique hv e.open_source hev
  have hn' := (exp_fibre_smooth x v).continuousAt.tendsto hn
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hn',e.open_source.mem_nhds hev] with w hw hwe
  obtain ⟨u,heu,hnu⟩ := exists_minimizing_vector (n := n) x (exp x w)
  have hum : u ∈ minimizingDomain x := by change dist x (exp x u) = ‖u‖; rw [heu,hnu]
  have hue : u ∈ e.source := hw u hum heu
  have hwu : w = u := e.injOn hwe hue (by rw [he w,he u,heu])
  exact hwu ▸ hum

 theorem zero_mem_injectivity (x : M) : (0 : TangentSpace (model n) x) ∈ injectivityDomain x := by
  exact ⟨2,by norm_num,by simp [exp_zero]⟩

 theorem strict_radial_mem_injectivity {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ minimizingDomain x) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) :
    t • v ∈ injectivityDomain x := by
  by_cases ht0 : t = 0
  · simpa only [ht0,zero_smul] using zero_mem_injectivity x
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  refine ⟨t⁻¹,(one_lt_inv₀ htp).mpr ht₁,?_⟩
  rw [smul_smul,inv_mul_cancel₀ ht0,one_smul]
  rw [show dist x (exp x v) = ‖v‖ from hv,norm_smul,Real.norm_eq_abs,abs_of_pos htp]
  field_simp

 theorem injectivity_extend {x : M} {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : ∃ t : ℝ, 1 < t ∧ t • v ∈ injectivityDomain x := by
  obtain ⟨a,ha,he⟩ := hv
  have hap : 0 < a := lt_trans zero_lt_one ha
  obtain ⟨t,ht,hta⟩ := exists_between ha
  have ht₀ : 0 ≤ t/a := div_nonneg (zero_lt_one.trans ht).le hap.le
  have ht₁ : t/a < 1 := (div_lt_one hap).mpr hta
  have ham : a • v ∈ minimizingDomain x := by
    change dist x (exp x (a•v)) = ‖a•v‖
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hap]
  have hh := strict_radial_mem_injectivity ham ht₀ ht₁
  exact ⟨t,ht,by simpa only [smul_smul,div_mul_cancel₀ _ hap.ne'] using hh⟩

 theorem injectivityDomain_open (x : M) : IsOpen (injectivityDomain (n := n) x) := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  obtain ⟨t,ht,htv⟩ := injectivity_extend hv
  have hm := mem_interior_iff_mem_nhds.mp (injectivity_mem_interior_minimizing htv)
  have hn := (continuous_const_smul t).continuousAt.preimage_mem_nhds hm
  filter_upwards [hn] with w hw
  refine ⟨t,ht,?_⟩
  change dist x (exp x (t•w)) = ‖t•w‖ at hw
  rwa [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans ht)] at hw

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_ActionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentChartLinear_eq (x : M) (v : TangentSpace (model n) x) :
    tangentChartLinear x v = (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)).2 := by
  have hh := congrArg (fun p : TangentBundle (model n) (Model n) => p.2)
    (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle (model n) M))
      (q := (⟨x,v⟩ : TangentBundle (model n) M)) (mem_chart_source (Model n) x))
  exact hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_MajorantHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem hessian_affine_pullback (L : E →L[ℝ] F) (c : F) {f : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (c+L x)) (v : E) :
    fderiv ℝ (fderiv ℝ (fun u => f (c+L u))) x v v =
      fderiv ℝ (fderiv ℝ f) (c+L x) (L v) (L v) := by
  have hcomp : ContDiffAt ℝ 2 (fun u => f (c+L u)) x :=
    hf.comp x (contDiffAt_const.add L.contDiff.contDiffAt)
  rw [← line_second hcomp v,← line_second hf (L v)]
  congr 2
  funext t
  simp only [map_add,map_smul,add_assoc]

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_HessianLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hessian_split {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (s t C : ℝ) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun z => f z / s + C - g z / t)) x ξ ξ =
      fderiv ℝ (fderiv ℝ f) x ξ ξ / s - fderiv ℝ (fderiv ℝ g) x ξ ξ / t := by
  let F : ℝ → ℝ := fun u => f (x+u•ξ)
  let G : ℝ → ℝ := fun u => g (x+u•ξ)
  have hline : ContDiff ℝ 2 (fun u : ℝ => x+u•ξ) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hF : ContDiffAt ℝ 2 F 0 := by
    have hh : ContDiffAt ℝ 2 f (x+(0 : ℝ)•ξ) := by simpa using hf
    exact hh.comp 0 hline.contDiffAt
  have hG : ContDiffAt ℝ 2 G 0 := by
    have hh : ContDiffAt ℝ 2 g (x+(0 : ℝ)•ξ) := by simpa using hg
    exact hh.comp 0 hline.contDiffAt
  have hcombo := ((hf.div_const s).add (contDiffAt_const (c := C))).sub (hg.div_const t)
  rw [← line_second hcombo ξ,← line_second hf ξ,← line_second hg ξ]
  have hh := iteratedDeriv_sub (n := 2)
    (((contDiffAt_const (c := C)).add (hF.div_const s))) (hG.div_const t)
  rw [iteratedDeriv_const_add (by norm_num),iteratedDeriv_div_const,iteratedDeriv_div_const] at hh
  have heq : ((fun u : ℝ => C + F u / s) - fun u => G u / t) =
      (fun u : ℝ => f (x+u•ξ)/s+C-g (x+u•ξ)/t) := by
    funext u
    simp only [Pi.sub_apply,F,G]
    ring
  rw [heq] at hh
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def,F,G] using hh

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_CostSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 omit [CompactSpace M] in
 theorem cost_triangle_split (x m y : M) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    cost x y / (s+t) ≤ cost x m / s + cost m y / t := by
  have htri := dist_triangle x m y
  have hsqr : dist x y ^ 2 ≤ (dist x m+dist m y)^2 :=
    pow_le_pow_left₀ dist_nonneg htri 2
  have hsq := DiscreteVariational.weighted_two_sq (dist x m) (dist m y) s t hs ht
  dsimp only [cost]
  have he₁ : dist x y^2/2/(s+t) = (dist x y^2/(s+t))/2 := by ring
  have he₂ : dist x m^2/2/s+dist m y^2/2/t = (dist x m^2/s+dist m y^2/t)/2 := by ring
  rw [he₁,he₂]
  exact div_le_div_of_nonneg_right
    ((div_le_div_of_nonneg_right hsqr (add_pos hs ht).le).trans hsq) (by norm_num)

 theorem minimizing_shortened_dist {x : M} {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    dist (exp x (s•a)) (exp x (t•a)) = (t-s)*‖a‖ := by
  let p : TangentBundle (model n) M := ⟨x,a⟩
  have hray : dist p.1 (geodesic p 1) = 1*‖p.2‖ := by
    change dist x (geodesic (⟨x,a⟩ : TangentBundle (model n) M) 1) = 1*‖a‖
    rw [← exp_eq_geodesic,one_mul]
    exact ha
  rw [exp_mul_eq_geodesic p s,exp_mul_eq_geodesic p t]
  exact minimizing_segment_dist p hray hs hst ht

 theorem minimizing_shortened_cost {x : M} {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s : ℝ} (hs : 0 ≤ s) (hs₁ : s ≤ 1) :
    cost x (exp x (s•a)) = s^2*‖a‖^2/2 := by
  have hd := minimizing_shortened_dist ha (s := 0) (t := s) (le_refl 0) hs hs₁
  simp only [zero_smul,exp_zero,sub_zero] at hd
  dsimp only [cost]
  rw [hd,mul_pow]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingFocalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem derivative_hessian_along_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → ℝ} {c : ℝ → V} {k : V}
    (hF : ContDiffAt ℝ 2 F (c 0)) (hc : HasDerivAt c k 0) (w : V) :
    HasDerivAt (fun t => fderiv ℝ F (c t) w)
      (fderiv ℝ (fderiv ℝ F) (c 0) k w) 0 := by
  have hd := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp := hd.hasFDerivAt.comp_hasDerivAt 0 hc
  have hh := hp.clm_apply (hasDerivAt_const (0 : ℝ) w)
  convert! hh using 1
  simp

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_RadialComparisonCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem fderiv_partial_fst {f : E × F → ℝ} {a : E} {b : F}
    (hf : DifferentiableAt ℝ f (a,b)) (ξ : E) :
    fderiv ℝ (fun z : E => f (z,b)) a ξ = fderiv ℝ f (a,b) (ξ,0) := by
  have hc : HasFDerivAt (fun z : E => (z,b))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] F)) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const (c := b) a)
  change fderiv ℝ (f ∘ (fun z : E => (z,b))) a ξ = _
  rw [(hf.hasFDerivAt.comp a hc).fderiv]
  rfl

 theorem horizontal_hessian_positive {f : E × F → ℝ} {a : E} {b : F}
    (hf : ContDiffAt ℝ 2 f (a,b)) (hm : IsLocalMin f (a,b))
    (ξ : E) (κ : F) {c : ℝ} (hc : c ≠ 0)
    (hcross : HasDerivAt (fun t : ℝ => fderiv ℝ f (a,b+t•κ) (ξ,0)) c 0) :
    0 < fderiv ℝ (fderiv ℝ (fun z : E => f (z,b))) a ξ ξ := by
  let L : E →L[ℝ] E × F := (ContinuousLinearMap.id ℝ E).prod 0
  have hd : fderiv ℝ (fderiv ℝ (fun z : E => f (z,b))) a ξ ξ =
      fderiv ℝ (fderiv ℝ f) (a,b) (ξ,0) (ξ,0) := by
    have hf' : ContDiffAt ℝ 2 f ((0,b)+L a) := by simpa [L] using hf
    convert hessian_affine_pullback L ((0,b) : E × F) hf' ξ using 1 <;> simp [L]
  rw [hd]
  have hnonneg := hessian_nonneg hf hm ((ξ,0) : E × F)
  by_contra hn
  have hzero := le_antisymm (not_lt.mp hn) hnonneg
  have hnull := hessian_null_pair hf hm hzero ((0,κ) : E × F)
  have hcurve : HasDerivAt (fun t : ℝ => (a,b+t•κ)) ((0,κ) : E × F) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) a).prodMk (((hasDerivAt_id (0 : ℝ)).smul_const κ).const_add b) using 1
    simp
  have hf' : ContDiffAt ℝ 2 f (a,b+(0 : ℝ)•κ) := by simpa using hf
  have he := (derivative_hessian_along_curve hf' hcurve ((ξ,0) : E × F)).unique hcross
  simp only [zero_smul,add_zero] at he
  rw [(hf.isSymmSndFDerivAt (by norm_num)).eq (0,κ) (ξ,0),hnull] at he
  exact hc he.symm

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_RadialSplitAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 omit [IsManifold (model n) ∞ M]
   [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem radialSplitAction_nonneg (x : M) (a : TangentSpace (model n) x)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (q : Model n × TangentSpace (model n) x) :
    0 ≤ radialSplitAction x a s t q := by
  have hh := cost_triangle_split ((chartAt (Model n) x).symm q.1)
    (exp x (s•a+q.2)) (exp x (t•a)) hs (sub_pos.mpr hst)
  rw [add_sub_cancel] at hh
  exact sub_nonneg.mpr hh

 theorem radialSplitAction_contact (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    radialSplitAction x a s t (chartAt (Model n) x x,0) = 0 := by
  unfold radialSplitAction
  simp only [add_zero,(chartAt (Model n) x).left_inv (mem_chart_source (Model n) x)]
  rw [minimizing_shortened_cost ha hs.le (hst.trans ht).le,
    minimizing_shortened_cost ha (hs.trans hst).le ht.le]
  have htail := minimizing_shortened_dist ha hs.le hst.le ht.le
  change s^2*‖a‖^2/2/s+(dist (exp x (s•a)) (exp x (t•a)))^2/2/(t-s)-t^2*‖a‖^2/2/t=0
  rw [htail]
  field_simp [hs.ne', (hs.trans hst).ne', (sub_pos.mpr hst).ne']
  ring

 theorem radialSplitAction_min (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    IsLocalMin (radialSplitAction x a s t) (chartAt (Model n) x x,0) := by
  filter_upwards [] with q
  rw [radialSplitAction_contact x ha hs hst ht]
  exact radialSplitAction_nonneg x a hs hst q

 theorem radialSplitAction_initial_derivative (x : M) (a u : TangentSpace (model n) x)
    (s t : ℝ) (hu : s•a+u ∈ injectivityDomain x) (ht : t•a ∈ injectivityDomain x)
    (hf : DifferentiableAt ℝ (radialSplitAction x a s t) (chartAt (Model n) x x,u))
    (w : Model n) :
    fderiv ℝ (radialSplitAction x a s t) (chartAt (Model n) x x,u) (w,0) =
      -(metric x (chartAt (Model n) x x) (tangentChartLinear x (s•a+u)) w) / s +
      (metric x (chartAt (Model n) x x) (tangentChartLinear x (t•a)) w) / t := by
  rw [← DiscreteVariational.fderiv_partial_fst hf]
  have hf₁ := ((initialCost_geometry x hu).1.differentiableAt (by simp)).hasFDerivAt
  have hf₃ := ((initialCost_geometry x ht).1.differentiableAt (by simp)).hasFDerivAt
  have hd := ((hf₁.mul_const s⁻¹).add_const (cost (exp x (s•a+u)) (exp x (t•a)) / (t-s))).sub (hf₃.mul_const t⁻¹)
  change fderiv ℝ (fun z => initialCost x (exp x (s•a+u)) z / s +
    cost (exp x (s•a+u)) (exp x (t•a)) / (t-s) - initialCost x (exp x (t•a)) z / t)
      (chartAt (Model n) x x) w = _
  simp only [div_eq_mul_inv]
  have hde : fderiv ℝ (fun z => initialCost x (exp x (s•a+u)) z * s⁻¹ +
      cost (exp x (s•a+u)) (exp x (t•a)) / (t-s) -
      initialCost x (exp x (t•a)) z * t⁻¹) (chartAt (Model n) x x) =
      s⁻¹ • fderiv ℝ (initialCost x (exp x (s•a+u))) (chartAt (Model n) x x) -
      t⁻¹ • fderiv ℝ (initialCost x (exp x (t•a))) (chartAt (Model n) x x) := hd.fderiv
  simp only [div_eq_mul_inv] at hde
  rw [hde]
  simp only [sub_apply,smul_apply,smul_eq_mul]
  rw [(initialCost_geometry x hu).2.1,(initialCost_geometry x ht).2.1]
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_RadialComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem radialSplitAction_cross (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (ξ : TangentSpace (model n) x) :
    HasDerivAt (fun r : ℝ => fderiv ℝ (radialSplitAction x a s t)
      (chartAt (Model n) x x,r•ξ) (tangentChartLinear x ξ,0)) (-inner ℝ ξ ξ / s) 0 := by
  have hsI := strict_radial_mem_injectivity ha hs.le (hst.trans ht)
  have htI := strict_radial_mem_injectivity ha (hs.trans hst).le ht
  have hF : ContDiffAt ℝ 2 (radialSplitAction x a s t) (chartAt (Model n) x x,0) :=
    (radialSplitAction_smooth x ha hs hst ht).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hevent : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ),
      s•a+r•ξ ∈ injectivityDomain x ∧
      DifferentiableAt ℝ (radialSplitAction x a s t) (chartAt (Model n) x x,r•ξ) := by
    have h₁ : Tendsto (fun r : ℝ => s•a+r•ξ) (𝓝 0) (𝓝 (s•a)) := by
      simpa only [zero_smul,add_zero] using
        (show Continuous (fun r : ℝ => s•a+r•ξ) from continuous_const.add (continuous_id.smul continuous_const)).continuousAt.tendsto (x := (0 : ℝ))
    have h₂ : Tendsto (fun r : ℝ => (chartAt (Model n) x x,r•ξ)) (𝓝 0) (𝓝 (chartAt (Model n) x x,0)) := by
      simpa only [zero_smul] using
        (show Continuous (fun r : ℝ => (chartAt (Model n) x x,r•ξ)) from continuous_const.prodMk (continuous_id.smul continuous_const)).continuousAt.tendsto (x := (0 : ℝ))
    filter_upwards [h₁ ((injectivityDomain_open x).mem_nhds hsI),
      h₂ ((hF.eventually (by norm_num)).mono (fun _ hh => hh.differentiableAt (by norm_num)))] with r hr₁ hr₂
    exact ⟨hr₁,hr₂⟩
  have heq : (fun r : ℝ => fderiv ℝ (radialSplitAction x a s t)
      (chartAt (Model n) x x,r•ξ) (tangentChartLinear x ξ,0)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => (-inner ℝ ξ ξ / s)*r) := by
    filter_upwards [hevent] with r hr
    rw [radialSplitAction_initial_derivative x a (r•ξ) s t hr.1 htI hr.2]
    simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
    have hmetric (u v : TangentSpace (model n) x) :
        metric x (chartAt (Model n) x x) (tangentChartLinear x u) (tangentChartLinear x v) = inner ℝ u v := by
      rw [tangentChartLinear_eq,tangentChartLinear_eq]
      exact stateChart_pairing x x (mem_chart_source (Model n) x) u v
    rw [hmetric a ξ,hmetric ξ ξ]
    field_simp [hs.ne',(hs.trans hst).ne']
    ring
  simpa only [mul_one] using (((hasDerivAt_id (0 : ℝ)).const_mul (-inner ℝ ξ ξ / s))).congr_of_eventuallyEq heq

 theorem radialSplitAction_hessian (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (ξ : TangentSpace (model n) x) :
    fderiv ℝ (fderiv ℝ (fun z => radialSplitAction x a s t (z,0)))
      (chartAt (Model n) x x) (tangentChartLinear x ξ) (tangentChartLinear x ξ) =
        actionHessian x (s•a) ξ ξ / s - actionHessian x (t•a) ξ ξ / t := by
  have hsI := strict_radial_mem_injectivity ha hs.le (hst.trans ht)
  have htI := strict_radial_mem_injectivity ha (hs.trans hst).le ht
  have hf : ContDiffAt ℝ 2 (initialCost x (exp x (s•a))) (chartAt (Model n) x x) :=
    (initialCost_geometry x hsI).1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiffAt ℝ 2 (initialCost x (exp x (t•a))) (chartAt (Model n) x x) :=
    (initialCost_geometry x htI).1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have heq : (fun z => radialSplitAction x a s t (z,0)) = (fun z =>
      initialCost x (exp x (s•a)) z / s + cost (exp x (s•a)) (exp x (t•a)) / (t-s) -
      initialCost x (exp x (t•a)) z / t) := by
    funext z
    simp only [radialSplitAction,add_zero,initialCost]
  rw [heq,DiscreteVariational.hessian_split hf hg]
  change _ = (fderiv ℝ (fderiv ℝ (initialCost x (exp x (s•a)))) (chartAt (Model n) x x)
    (tangentChartLinear x ξ) (tangentChartLinear x ξ) +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x (s•a))) / s -
    (fderiv ℝ (fderiv ℝ (initialCost x (exp x (t•a)))) (chartAt (Model n) x x)
    (tangentChartLinear x ξ) (tangentChartLinear x ξ) +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x (t•a))) / t
  simp only [map_smul,smul_eq_mul]
  field_simp [hs.ne',(hs.trans hst).ne']
  ring

 theorem radial_hessian_strict (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    {ξ : TangentSpace (model n) x} (hξ : ξ ≠ 0) :
    actionHessian x (s•a) ξ ξ / s > actionHessian x (t•a) ξ ξ / t := by
  have hf : ContDiffAt ℝ 2 (radialSplitAction x a s t) (chartAt (Model n) x x,0) :=
    (radialSplitAction_smooth x ha hs hst ht).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hcross := radialSplitAction_cross x ha hs hst ht ξ
  have hc : -inner ℝ ξ ξ / s ≠ 0 := div_ne_zero (neg_ne_zero.mpr (real_inner_self_pos.mpr hξ).ne') hs.ne'
  have hp := DiscreteVariational.horizontal_hessian_positive hf
    (radialSplitAction_min x ha hs hst ht) (tangentChartLinear x ξ) ξ hc
    (by simpa only [zero_add] using hcross)
  rw [radialSplitAction_hessian x ha hs hst ht ξ] at hp
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CriticalHessianGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem critical_hessian_gap_oai (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    {ξ : TangentSpace (model n) x} (hξ : ξ ≠ 0)
    {S : Set (TangentSpace (model n) x)} (hS : Convex ℝ S)
    {s ℓ : ℝ} (hs : 0 < s) (hsℓ : s < ℓ) (hℓ : ℓ < 1)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ S, r•a ∈ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (haM : ∀ i, a i ∈ minimizingDomain x)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (hB : stateChart x (⟨x,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    0 < ∑ i, θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) := by
  classical
  have hJ := critical_jensen hMTW x ξ hS hs hbelow a θ hb ha hθ hsum hbary horth
    (fun i => strict_radial_mem_injectivity (haM i) hs.le (hsℓ.trans hℓ)) B hB
  have hgap (i : κ) : 0 < actionHessian x (s•a i) ξ ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ := by
    have hh := (div_lt_div_iff₀ (hs.trans hsℓ) hs).mp
      (radial_hessian_strict x (haM i) hs hsℓ hℓ hξ)
    have ht := (div_lt_iff₀ (hs.trans hsℓ)).mpr hh
    have ht' : (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ < actionHessian x (s•a i) ξ ξ := by
      calc
        (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ =
            (actionHessian x (ℓ•a i) ξ ξ * s)/ℓ := by ring
        _ < actionHessian x (s•a i) ξ ξ := ht
    linarith
  have hex : ∃ i, 0 < θ i := by
    by_contra! hn
    have hz : ∑ i, θ i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i,hi⟩ := hex
  have hpos : 0 < ∑ i, θ i * (actionHessian x (s•a i) ξ ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hθ i) (hgap i).le)
      ⟨i,Finset.mem_univ i,mul_pos hi (hgap i)⟩
  have heq : (∑ i, θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ)) =
      branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      ∑ i, θ i*((s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hsum,one_mul]
  rw [heq]
  simp only [mul_sub,Finset.sum_sub_distrib] at hpos
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.critical_hessian_gap_oai.{u_1, u_2} := @OAI.WeakMTWGlobalSupport.WeakMTW.critical_hessian_gap_oai.{u_1, u_2}
