-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:12:07.39046+00:00
-- url     : https://prove2.me/submissions/1b0600ba-ab33-4263-931e-2858d98971e6

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003

section
-- module Solutions.OAIQW_WeakMTW.Variations_CurveVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace VariationCalculus
open Set Filter
open scoped Topology ContDiff
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem parameter_variation_hasDerivAt {Φ Ψ : ℝ × P → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (htime : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (Ψ q) q.1)
    {T : ℝ} {x w : P} (hTx : (T, x) ∈ U)
    (hΨ : DifferentiableAt ℝ Ψ (T, x)) :
    HasDerivAt (fun t => fderiv ℝ Φ (t, x) (0, w))
      (fderiv ℝ Ψ (T, x) (0, w)) T := by
  have hc := (hΦ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) (T, x) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hdD.hasFDerivAt.clm_apply (hasFDerivAt_const (1, 0) (T, x))
  have heq : (fun q => fderiv ℝ Φ q (1, 0)) =ᶠ[𝓝 (T, x)] Ψ := by
    filter_upwards [hU.mem_nhds hTx] with q hq
    exact (hasDerivAt_time_slice (((hΦ q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by norm_num))).unique (htime q hq)
  have he := congrArg (fun L : (ℝ × P) →L[ℝ] F => L (0, w))
    (hA.unique (hΨ.hasFDerivAt.congr_of_eventuallyEq heq))
  have hs := hc.isSymmSndFDerivAt (by simp) (1, 0) (0, w)
  have hd := ((hasDerivAt_time_slice hdD).hasFDerivAt.clm_apply (hasFDerivAt_const (0, w) T)).hasDerivAt
  convert! hd using 1
  simpa [hs] using he.symm

end VariationCalculus

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_FirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace FirstVariation
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem geodesic_pairing_hasDerivAt {G : E → MetricTensor E}
    {c V J : ℝ → E} {t : ℝ} {W : E}
    (hG : DifferentiableAt ℝ G (c t))
    (hpos : ∀ v : E, v ≠ 0 → 0 < G (c t) v v)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun r => G (c r) (V r) (J r))
      (fderiv ℝ G (c t) (J t) (V t) (V t) / 2 + G (c t) (V t) W) t := by
  have hd := hasDerivAt_metric_pairing hG hc hV hJ
  have hm := metric_christoffel hpos (V t) (V t) (J t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

omit [FiniteDimensional ℝ E] in
theorem parameter_hasDerivAt {c : ℝ × ℝ → E} {t s : ℝ}
    (hc : DifferentiableAt ℝ c (t, s)) :
    HasDerivAt (fun r => c (t, r)) (fderiv ℝ c (t, s) (0, 1)) s := by
  convert! hc.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)) using 1

end
end FirstVariation

end

end WeakMTWGlobalSupport

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

 omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
 theorem curveState_chart_deriv' (x : M) {γ : ℝ → M} {a : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ a)
    (ha : γ a ∈ (chartAt E x).source) :
    deriv ((chartAt E x) ∘ γ) a = (stateChart x (curveState (E := E) γ a)).2 := by
  rw [curveState_chart_deriv x hγ ha, tangentMap_chart (p := (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M)) ha]
  rfl

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
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoordinateIdentification
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
 theorem geodesic_eq_coordinate (x : M) {U : Set ℝ} (hU : IsOpen U) (hpre : IsPreconnected U)
    {q : ℝ → Model n × Model n} (hqs : ContDiffOn ℝ ∞ q U)
    (hqe : ∀ t ∈ U, (q t).1 ∈ (chartAt (Model n) x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t) (h0 : (0 : ℝ) ∈ U) :
    EqOn (geodesic ((stateChart (E := Model n) x).symm (q 0)))
      (fun t => (chartAt (Model n) x).symm (q t).1) U := by
  let p := (stateChart (E := Model n) x).symm (q 0)
  have hγ := coordinate_intrinsic x hU hpre hqs hqe h0
  have hn : Real.sqrt (metric x (q 0).1 (q 0).2 (q 0).2) = ‖p.2‖ :=
    stateChart_energy x (q := q 0) (hqe 0 h0).1
  rw [hn] at hγ
  have hγ₀ := coordinate_curve_state_chart x (hqe 0 h0).1 (hqe 0 h0).2
  exact intrinsic_unique_on hU hpre (norm_nonneg p.2) (norm_nonneg p.2)
    ((geodesic_intrinsic p).mono (subset_univ U)) hγ h0
    ((geodesic_state_zero p).trans hγ₀.symm)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoordinateEquation
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

 theorem geodesic_coordinate_equation_zero (x : M) (p : TangentBundle (model n) M)
    (hp : p.1 ∈ (chartAt (Model n) x).source) :
    HasDerivAt (fun t => (stateChart (E := Model n) x) (geodesicFlow t p))
      (geodesicSpray (metric x) (stateChart (E := Model n) x p)) 0 := by
  let c := chartAt (Model n) x
  let d := stateChart (E := Model n) x
  let q₀ := d p
  have hps : p ∈ d.source := (stateChart_source x p).mpr hp
  have hq₀ : q₀.1 ∈ c.target := (stateChart_target x q₀).mp (d.map_source hps)
  let A := metric x q₀.1 q₀.2 q₀.2
  obtain ⟨ε,hε,V,_hV,hmem,_hVS,hex⟩ := uniform_local_geodesics c.open_target
    (metric_smooth x) (fun y hy v hv => metric_positive x hy hv) hq₀ (1+|A|)
  have hbound : metric x q₀.1 q₀.2 q₀.2 ≤ (1+|A|)^2 := by
    dsimp only [A] at *
    nlinarith [le_abs_self (metric x q₀.1 q₀.2 q₀.2),sq_nonneg |metric x q₀.1 q₀.2 q₀.2|]
  obtain ⟨q,hqzero,hqs,hqe⟩ := hex q₀.1 hmem q₀.2 hbound
  have h0 : (0 : ℝ) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have he := geodesic_eq_coordinate x Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected
    hqs hqe h0
  rw [hqzero] at he
  change EqOn (geodesic (d.symm (d p))) _ _ at he
  rw [d.left_inv hps] at he
  have hstate : ∀ t ∈ Metric.ball (0 : ℝ) ε, d (geodesicFlow t p) = q t := by
    intro t ht
    have hh : geodesicFlow t p = d.symm (q t) := by
      change curveState (E := Model n) (geodesic p) t = _
      rw [← coordinate_curve_state_chart x (hqe t ht).1 (hqe t ht).2]
      apply curveState_congr
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
      exact he hs
    rw [hh,d.right_inv ((stateChart_target x _).mpr (hqe t ht).1)]
  have hd := (hqe 0 h0).2
  rw [hqzero] at hd
  exact hd.congr_of_eventuallyEq (by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    exact hstate t ht)

 theorem geodesic_coordinate_equation (x : M) (p : TangentBundle (model n) M) (t : ℝ)
    (hp : geodesic p t ∈ (chartAt (Model n) x).source) :
    HasDerivAt (fun s => (stateChart (E := Model n) x) (geodesicFlow s p))
      (geodesicSpray (metric x) (stateChart (E := Model n) x (geodesicFlow t p))) t := by
  have hh := geodesic_coordinate_equation_zero x (geodesicFlow t p) hp
  have hd : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
  have he := hh.scomp_of_eq t hd (by simp)
  simpa only [Function.comp_def,one_smul,geodesicFlow_sub] using he
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

 theorem geodesicFlow_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod ((model n).prod (model n))) ((model n).prod (model n)) ∞
      (fun z : ℝ × TangentBundle (model n) M => geodesicFlow z.1 z.2) := by
  rintro ⟨t,p⟩
  obtain ⟨V, hV, hmem, hs⟩ := geodesicFlow_smooth_near_zero (geodesicFlow t p)
  have hzero := (hs _ hmem).contMDiffAt (hV.mem_nhds hmem)
  have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod ((model n).prod (model n)))
      (𝓘(ℝ, ℝ).prod ((model n).prod (model n))) ∞
      (fun z : ℝ × TangentBundle (model n) M => (z.1-t, geodesicFlow t z.2)) (t,p) :=
    ((contMDiff_fst.sub contMDiff_const).prodMk
      ((geodesicFlow_smooth_fixed (n := n) (M := M) t).comp contMDiff_snd)) (t,p)
  have hzero' : ContMDiffAt (𝓘(ℝ, ℝ).prod ((model n).prod (model n))) ((model n).prod (model n)) ∞
      (fun z : ℝ × TangentBundle (model n) M => geodesicFlow z.1 z.2) (t-t, geodesicFlow t p) := by
    simpa only [sub_self] using hzero
  have hh := hzero'.comp (t,p) hpair
  simpa only [Function.comp_def, geodesicFlow_sub] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_FanCoordinates
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

 theorem fanCoordinates_ode (x : M) (P : ℝ → TangentBundle (model n) M)
    {z : ℝ × ℝ} (hz : z ∈ fanDomain x P) :
    (fanCoordinates x P z).1 ∈ (chartAt (Model n) x).target ∧
      HasDerivAt (fun t => fanCoordinates x P (t,z.2))
        (geodesicSpray (metric x) (fanCoordinates x P z)) z.1 := by
   have hm : geodesic (P z.2) z.1 ∈ (chartAt (Model n) x).source :=
     (stateChart_source x _).mp hz
   exact ⟨(chartAt (Model n) x).map_source hm, geodesic_coordinate_equation x (P z.2) z.1 hm⟩

 theorem fanCoordinates_energy (x : M) (P : ℝ → TangentBundle (model n) M)
    {z : ℝ × ℝ} (hz : z ∈ fanDomain x P) :
    metric x (fanCoordinates x P z).1 (fanCoordinates x P z).2 (fanCoordinates x P z).2 =
      ‖(P z.2).2‖ ^ 2 := by
   have hm : (geodesicFlow z.1 (P z.2)).1 ∈ (chartAt (Model n) x).source :=
     (stateChart_source x _).mp hz
   have hh := stateChart_pairing x (geodesicFlow z.1 (P z.2)).1 hm
     (geodesicFlow z.1 (P z.2)).2 (geodesicFlow z.1 (P z.2)).2
   change metric x (fanCoordinates x P z).1 (fanCoordinates x P z).2
     (fanCoordinates x P z).2 = _ at hh
   rw [hh, real_inner_self_eq_norm_sq, geodesicFlow_norm]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_FlowVariationInjective
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

 theorem chart_flow_smooth (x b : M) (t : ℝ) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hb : geodesicFlow t ((stateChart x).symm q) ∈ (stateChart b).source) :
    ContDiffAt ℝ ∞ (fun r => stateChart b (geodesicFlow t ((stateChart x).symm r))) q := by
  have hs : ContMDiffOn 𝓘(ℝ, Model n × Model n) ((model n).prod (model n)) ∞
      (stateChart x).symm (stateChart (E := Model n) x).target :=
    by
      rw [modelWithCornersSelf_prod]
      exact contMDiffOn_chart_symm (I := (model n).prod (model n))
        (x := (⟨x,0⟩ : TangentBundle (model n) M))
  have hch : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
      (stateChart b) (stateChart (E := Model n) b).source :=
    contMDiffOn_extChartAt (I := (model n).prod (model n))
      (x := (⟨b,0⟩ : TangentBundle (model n) M))
  exact contMDiffAt_iff_contDiffAt.mp
    (((hch _ hb).contMDiffAt ((stateChart b).open_source.mem_nhds hb)).comp q
      (((geodesicFlow_smooth_fixed t) _).comp q
        ((hs _ hq).contMDiffAt ((stateChart x).open_target.mem_nhds hq))))

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_EnergyFirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace FirstVariation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem energy_pairing_hasDerivAt {G : E → MetricTensor E} {c V : ℝ × ℝ → E}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : ContDiffOn ℝ 2 c U)
    (hct : ∀ z ∈ U, HasDerivAt (fun r => c (r,z.2)) (V z) z.1)
    {t : ℝ} (ht : (t,0) ∈ U) (hV : DifferentiableAt ℝ V (t,0))
    (hDG : DifferentiableAt ℝ G (c (t,0)))
    (hsym : ∀ v w, G (c (t,0)) v w = G (c (t,0)) w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G (c (t,0)) v v)
    (hVt : HasDerivAt (fun r => V (r,0)) (-christoffel G (c (t,0)) (V (t,0)) (V (t,0))) t)
    {e : ℝ → ℝ} (he : (fun s => G (c (t,s)) (V (t,s)) (V (t,s))) =ᶠ[𝓝 (0 : ℝ)] e) :
    HasDerivAt (fun r => G (c (r,0)) (V (r,0)) (fderiv ℝ c (r,0) (0,1)))
      (deriv e 0 / 2) t := by
  have hcd := ((hc _ ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdJ := VariationCalculus.parameter_variation_hasDerivAt (w := (1 : ℝ)) hU hc hct ht hV
  have hpair := geodesic_pairing_hasDerivAt (G := G) (c := fun r => c (r,0)) (V := fun r => V (r,0)) (J := fun r => fderiv ℝ c (r,0) (0,1)) hDG hpos (hct _ ht) hVt hdJ
  have hde := hasDerivAt_metric_pairing hDG
    (parameter_hasDerivAt hcd) (parameter_hasDerivAt hV) (parameter_hasDerivAt hV)
  have hev := hde.deriv.symm.trans he.deriv_eq
  rw [hsym (fderiv ℝ V (t,0) (0,1)) (V (t,0))] at hev
  convert! hpair using 1
  linarith
end
end FirstVariation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_LocalFanVariation
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

 theorem geodesicFan_smooth_on {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P S) :
    ContMDiffOn 𝓘(ℝ,ℝ × ℝ) ((model n).prod (model n)) ∞ (geodesicFan P) (Prod.snd ⁻¹' S) := by
  have ht : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ) ∞ Prod.fst :=
    contMDiff_iff_contDiff.mpr contDiff_fst
  have hs : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ) ∞ Prod.snd :=
    contMDiff_iff_contDiff.mpr contDiff_snd
  exact geodesicFlow_smooth.comp_contMDiffOn
    (ht.contMDiffOn.prodMk (hP.comp hs.contMDiffOn (fun _ hz => hz)))

 theorem localFanDomain_open (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) :
    IsOpen ((Prod.snd ⁻¹' S) ∩ fanDomain x P) :=
  (geodesicFan_smooth_on hP).continuousOn.isOpen_inter_preimage
    (hS.preimage continuous_snd) (stateChart x).open_source

 theorem fanCoordinates_smooth_on (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) :
    ContDiffOn ℝ ∞ (fanCoordinates x P) ((Prod.snd ⁻¹' S) ∩ fanDomain x P) := by
  have hd : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
      (stateChart x) (stateChart (E := Model n) x).source :=
    contMDiffOn_extChartAt (I := (model n).prod (model n))
      (x := (⟨x,0⟩ : TangentBundle (model n) M))
  exact contMDiffOn_iff_contDiffOn.mp (hd.comp
    ((geodesicFan_smooth_on hP).mono inter_subset_left) (fun _ hz => hz.2))

 theorem fanMomentum_coord_on (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) {t : ℝ}
    (ht : (t,0) ∈ fanDomain x P) :
    fanMomentum P t = metric x (fanCoordinates x P (t,0)).1
      (fanCoordinates x P (t,0)).2
      (fderiv ℝ (fun z => (fanCoordinates x P z).1) (t,0) (0,1)) := by
  have hm₀ : (t,0) ∈ (Prod.snd ⁻¹' S) ∩ fanDomain x P := ⟨h₀,ht⟩
  have hq := ((fanCoordinates_smooth_on x hP _ hm₀).contDiffAt
    ((localFanDomain_open x hS hP).mem_nhds hm₀)).differentiableAt (by simp)
  have hγ : ContMDiffAt 𝓘(ℝ,ℝ) (model n) ∞ (fun s => geodesic (P s) t) 0 :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).contMDiffAt.comp 0
      ((geodesicFlow_smooth_fixed t).contMDiffAt.comp 0 ((hP 0 h₀).contMDiffAt (hS.mem_nhds h₀)))
  have hm : geodesic (P 0) t ∈ (chartAt (Model n) x).source := (stateChart_source x _).mp ht
  have hd := curveState_chart_deriv' x (hγ.mdifferentiableAt (by simp)) hm
  have hp := (FirstVariation.parameter_hasDerivAt hq.fst).deriv
  change deriv (fun s => (fanCoordinates x P (t,s)).1) 0 = _ at hp
  change deriv (fun s => (fanCoordinates x P (t,s)).1) 0 = _ at hd
  rw [← hp,hd]
  exact (stateChart_pairing x (geodesic (P 0) t) hm
    (geodesicFlow t (P 0)).2
    (mfderiv 𝓘(ℝ,ℝ) (model n) (fun s => geodesic (P s) t) 0 (1 : ℝ))).symm

 theorem fanMomentum_hasDerivAt_on {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) (t : ℝ) :
    HasDerivAt (fanMomentum P) (deriv (fun s => ‖(P s).2‖^2) 0 / 2) t := by
  let x := geodesic (P 0) t
  let U := (Prod.snd ⁻¹' S) ∩ fanDomain x P
  let q := fanCoordinates x P
  let c : ℝ × ℝ → Model n := fun z => (q z).1
  let V : ℝ × ℝ → Model n := fun z => (q z).2
  have hU : IsOpen U := localFanDomain_open x hS hP
  have ht : (t,0) ∈ U := ⟨h₀,(stateChart_source x _).mpr (mem_chart_source (Model n) x)⟩
  have hq : ContDiffOn ℝ ∞ q U := fanCoordinates_smooth_on x hP
  have hc : ContDiffOn ℝ 2 c U := hq.fst.of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hdq := ((hq _ ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
  have hdt := (fanCoordinates_ode x P ht.2).2
  have hm := (fanCoordinates_ode x P ht.2).1
  have hDG := ((metric_smooth x _ hm).contDiffAt
    ((chartAt (Model n) x).open_target.mem_nhds hm)).differentiableAt (by simp)
  have he : (fun s => metric x (c (t,s)) (V (t,s)) (V (t,s))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ‖(P s).2‖^2) := by
    have hh : ∀ᶠ s in 𝓝 (0 : ℝ), (t,s) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
    filter_upwards [hh] with s hs
    exact fanCoordinates_energy x P hs.2
  have hpair := FirstVariation.energy_pairing_hasDerivAt (G := metric x) (c := c) (V := V) hU hc
    (fun z hz => (fanCoordinates_ode x P hz.2).2.fst) ht hdq.snd hDG
    (metric_symmetric x _) (fun v hv => metric_positive x hm hv) hdt.snd he
  apply hpair.congr_of_eventuallyEq
  have hh : ∀ᶠ r in 𝓝 t, (r,0) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  filter_upwards [hh] with r hr
  exact fanMomentum_coord_on x hS h₀ hP hr.2

 theorem fanMomentum_affine_on {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) (t : ℝ) :
    fanMomentum P t = fanMomentum P 0 + t * (deriv (fun s => ‖(P s).2‖^2) 0 / 2) := by
  let K := deriv (fun s => ‖(P s).2‖^2) 0 / 2
  have hd : ∀ r : ℝ, HasDerivAt (fun r => fanMomentum P r-r*K) 0 r := by
    intro r
    have hh := (fanMomentum_hasDerivAt_on hS h₀ hP r).sub ((hasDerivAt_id r).mul_const K)
    change HasDerivAt (fun r => fanMomentum P r-r*K) (K-1*K) r at hh
    simpa only [one_mul,sub_self] using hh
  have hh := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t 0
  simp only [zero_mul,sub_zero] at hh
  exact sub_eq_iff_eq_add.mp hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartGlobalVariation
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

 omit [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem chartKinetic_smooth (x : M) :
    ContDiffOn ℝ ∞ (chartKinetic (n := n) x) (stateChart (E := Model n) x).target := by
  have hg : ContDiffOn ℝ ∞ (fun q : Model n × Model n => metric x q.1) (stateChart (E := Model n) x).target :=
    (metric_smooth x).comp contDiffOn_fst (fun q hq => (stateChart_target x q).mp hq)
  exact ((hg.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).div_const 2

 theorem fanMomentum_coord_deriv_on (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) {t : ℝ}
    (ht : (t,0) ∈ fanDomain x P) :
    fanMomentum P t = metric x (fanCoordinates x P (t,0)).1
      (fanCoordinates x P (t,0)).2
      (deriv (fun s => (fanCoordinates x P (t,s)).1) 0) := by
  have hm : (t,0) ∈ (Prod.snd ⁻¹' S) ∩ fanDomain x P := ⟨h₀,ht⟩
  have hq := ((fanCoordinates_smooth_on x hP _ hm).contDiffAt
    ((localFanDomain_open x hS hP).mem_nhds hm)).differentiableAt (by simp)
  rw [(FirstVariation.parameter_hasDerivAt hq.fst).deriv]
  exact fanMomentum_coord_on x hS h₀ hP ht

 theorem chart_flow_boundary (x y : M) (t : ℝ) {q : Model n × Model n}
    (hq : q ∈ (stateChart (E := Model n) x).target)
    (hy : geodesicFlow t ((stateChart (E := Model n) x).symm q) ∈ (stateChart (E := Model n) y).source)
    (k : Model n × Model n) :
    metric y (stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm q))).1
      (stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm q))).2
      (fderiv ℝ (fun r => stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm r))) q k).1 =
      metric x q.1 q.2 k.1 + t * fderiv ℝ (chartKinetic x) q k := by
  let a : ℝ → Model n × Model n := fun s => q+s•k
  let S := a ⁻¹' (stateChart (E := Model n) x).target
  let P : ℝ → TangentBundle (model n) M := fun s => (stateChart (E := Model n) x).symm (a s)
  have ha : ContDiff ℝ ∞ a := contDiff_const.add (contDiff_id.smul contDiff_const)
  have ha₀ : a 0 = q := by simp [a]
  have hS : IsOpen S := (stateChart (E := Model n) x).open_target.preimage ha.continuous
  have h₀ : (0 : ℝ) ∈ S := by simpa only [S,mem_preimage,ha₀] using hq
  have hsym : ContMDiffOn 𝓘(ℝ,Model n × Model n) ((model n).prod (model n)) ∞
      (stateChart (E := Model n) x).symm (stateChart (E := Model n) x).target := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffOn_chart_symm (I := (model n).prod (model n))
      (x := (⟨x,0⟩ : TangentBundle (model n) M))
  have hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S :=
    hsym.comp (contMDiff_iff_contDiff.mpr ha).contMDiffOn (fun _ hs => hs)
  have hxP : (0,0) ∈ fanDomain x P := by
    change geodesicFlow 0 ((stateChart (E := Model n) x).symm (a 0)) ∈ (stateChart (E := Model n) x).source
    rw [geodesicFlow_zero,ha₀]
    exact (stateChart (E := Model n) x).map_target hq
  have hyP : (t,0) ∈ fanDomain y P := by
    change geodesicFlow t ((stateChart (E := Model n) x).symm (a 0)) ∈ (stateChart (E := Model n) y).source
    rwa [ha₀]
  have hda : HasDerivAt a k 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add q using 1 <;> (first | rfl | simp)
  have hi : (fun s => fanCoordinates x P (0,s)) =ᶠ[𝓝 (0 : ℝ)] a := by
    filter_upwards [hS.mem_nhds h₀] with s hs
    change stateChart (E := Model n) x (geodesicFlow 0 ((stateChart (E := Model n) x).symm (a s))) = a s
    rw [geodesicFlow_zero,(stateChart (E := Model n) x).right_inv hs]
  have hida : HasDerivAt (fun s => (a s).1) k.1 0 := hda.fst
  have hid : HasDerivAt (fun s => (fanCoordinates x P (0,s)).1) k.1 0 :=
    hida.congr_of_eventuallyEq (hi.mono (fun _ h => congrArg Prod.fst h))
  let Φ : (Model n × Model n) → (Model n × Model n) := fun r => stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm r))
  have hΦ := chart_flow_smooth x y t hq hy
  have hDt : HasFDerivAt Φ (fderiv ℝ Φ q) (a 0) := by simpa only [ha₀] using (hΦ.differentiableAt (by simp)).hasFDerivAt
  have htd : HasDerivAt (fun s => (fanCoordinates y P (t,s)).1) (fderiv ℝ Φ q k).1 0 :=
    (hDt.comp_hasDerivAt 0 hda).fst
  have hki := (chartKinetic_smooth x q hq).contDiffAt ((stateChart (E := Model n) x).open_target.mem_nhds hq)
  have hDk : HasFDerivAt (chartKinetic x) (fderiv ℝ (chartKinetic x) q) (a 0) := by
    simpa only [ha₀] using (hki.differentiableAt (by simp)).hasFDerivAt
  have hene : (fun s => ‖(P s).2‖^2) =ᶠ[𝓝 (0 : ℝ)] (fun s => 2*chartKinetic x (a s)) := by
    filter_upwards [hS.mem_nhds h₀] with s hs
    have hps : P s ∈ (stateChart (E := Model n) x).source := (stateChart (E := Model n) x).map_target hs
    have hh := stateChart_pairing x (P s).1 ((stateChart_source x _).mp hps) (P s).2 (P s).2
    have hcoords : stateChart (E := Model n) x (P s) = a s := (stateChart (E := Model n) x).right_inv hs
    have hh' : metric x (stateChart (E := Model n) x (P s)).1 (stateChart (E := Model n) x (P s)).2 (stateChart (E := Model n) x (P s)).2 = ‖(P s).2‖^2 := by
      convert (show metric x (chartAt (Model n) x (P s).1) (stateChart (E := Model n) x (P s)).2 (stateChart (E := Model n) x (P s)).2 = ‖(P s).2‖^2 from
        by simpa only [real_inner_self_eq_norm_sq] using hh) using 1
      rfl
    rw [hcoords] at hh'
    dsimp only [chartKinetic]
    linarith
  have hed := (((hDk.comp_hasDerivAt 0 hda).const_mul 2).congr_of_eventuallyEq hene).deriv
  have hm := fanMomentum_affine_on hS h₀ hP t
  rw [fanMomentum_coord_deriv_on y hS h₀ hP hyP,
    fanMomentum_coord_deriv_on x hS h₀ hP hxP,hid.deriv,htd.deriv,hed] at hm
  have hi₀ : fanCoordinates x P (0,0) = q := (hi.eq_of_nhds).trans ha₀
  rw [hi₀] at hm
  have ht₀ : fanCoordinates y P (t,0) = Φ q := by change Φ (a 0) = Φ q; rw [ha₀]
  rw [ht₀] at hm
  convert hm using 1
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingAction
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

 theorem crossFlowCoordinates_step (x y : M) {s : ℝ} {q : Model n × Model n}
    (hs : geodesicFlow s ((stateChart x).symm q) ∈ (stateChart y).source) (t : ℝ) :
    flowCoordinates y t (crossFlowCoordinates x y s q) = crossFlowCoordinates x y (t+s) q := by
  dsimp only [flowCoordinates,crossFlowCoordinates]
  rw [(stateChart y).left_inv hs,← geodesicFlow_add]

 theorem generatingAction_smooth (x y : M) {ε : ℝ} {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (hshort : ShortChartAction y ε (crossFlowCoordinates x y (1-ε) q)) :
    ContDiffAt ℝ ∞ (generatingAction x y ε)
      (q,(crossFlowCoordinates x y 1 q).1) := by
  have hstep : flowCoordinates y ε (crossFlowCoordinates x y (1-ε) q) = crossFlowCoordinates x y 1 q := by
     rw [crossFlowCoordinates_step x y hτ ε]
     congr 1
     ring
  have hK := (chartKinetic_smooth x q hq).contDiffAt ((stateChart x).open_target.mem_nhds hq)
  have hΦ := chart_flow_smooth x y (1-ε) hq hτ
  have hC := hshort.2.2.1
  rw [hstep] at hC
  have harg : ContDiffAt ℝ ∞ (fun Q : (Model n × Model n) × Model n =>
      ((crossFlowCoordinates x y (1-ε) Q.1).1,Q.2)) (q,(crossFlowCoordinates x y 1 q).1) :=
    (ContDiffAt.comp (f := Prod.fst) (g := fun r => (crossFlowCoordinates x y (1-ε) r).1)
      _ hΦ.fst contDiffAt_fst).prodMk contDiffAt_snd
  exact (contDiffAt_const.mul (ContDiffAt.comp (f := Prod.fst) (g := chartKinetic x)
    (q,(crossFlowCoordinates x y 1 q).1) hK contDiffAt_fst)).add
    (contDiffAt_const.mul (ContDiffAt.comp (f := fun Q : (Model n × Model n) × Model n =>
      ((crossFlowCoordinates x y (1-ε) Q.1).1,Q.2)) (g := chartCost y)
      (q,(crossFlowCoordinates x y 1 q).1) hC harg))

 theorem generatingAction_gradient (x y : M) {ε : ℝ} (hε : ε ≠ 0)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (hshort : ShortChartAction y ε (crossFlowCoordinates x y (1-ε) q))
    (k : Model n × Model n) (z : Model n) :
    fderiv ℝ (generatingAction x y ε) (q,(crossFlowCoordinates x y 1 q).1) (k,z) =
      metric y (crossFlowCoordinates x y 1 q).1 (crossFlowCoordinates x y 1 q).2 z -
      metric x q.1 q.2 k.1 := by
  let τ := 1-ε
  let Φ := crossFlowCoordinates (n := n) x y τ
  let Ψ := crossFlowCoordinates (n := n) x y 1
  let Q := (q,(Ψ q).1)
  have hstep : flowCoordinates y ε (Φ q) = Ψ q := by
    change flowCoordinates y ε (crossFlowCoordinates x y (1-ε) q) = crossFlowCoordinates x y 1 q
    rw [crossFlowCoordinates_step x y hτ ε]
    congr 1
    ring
  have hK := ((chartKinetic_smooth x q hq).contDiffAt ((stateChart x).open_target.mem_nhds hq)).differentiableAt (by simp)
  have hΦ : DifferentiableAt ℝ Φ q := (chart_flow_smooth x y τ hq hτ).differentiableAt (by simp)
  have hC := hshort.2.2.1.differentiableAt (by simp)
  rw [hstep] at hC
  have h₁ := hK.hasFDerivAt.comp Q (hasFDerivAt_fst (𝕜 := ℝ))
  have h₂ := (hΦ.hasFDerivAt.comp Q (hasFDerivAt_fst (𝕜 := ℝ))).fst.prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := Q))
  have h₃ := hC.hasFDerivAt.comp Q h₂
  have hd := (h₁.const_mul τ).add (h₃.const_mul ε⁻¹)
  have hDf : fderiv ℝ (generatingAction x y ε) Q =
      τ • ((fderiv ℝ (chartKinetic x) q).comp (ContinuousLinearMap.fst ℝ (Model n × Model n) (Model n))) +
      ε⁻¹ • ((fderiv ℝ (chartCost y) ((Φ q).1,(Ψ q).1)).comp
        (((ContinuousLinearMap.fst ℝ (Model n) (Model n)).comp
          ((fderiv ℝ Φ q).comp (ContinuousLinearMap.fst ℝ (Model n × Model n) (Model n)))).prod
          (ContinuousLinearMap.snd ℝ (Model n × Model n) (Model n)))) := hd.fderiv
  rw [hDf]
  change τ * fderiv ℝ (chartKinetic x) q k + ε⁻¹ *
    fderiv ℝ (chartCost y) ((Φ q).1,(Ψ q).1) ((fderiv ℝ Φ q k).1,z) =
    metric y (Ψ q).1 (Ψ q).2 z - metric x q.1 q.2 k.1
  have hshortD := hshort.2.2.2 ((fderiv ℝ Φ q k).1,z)
  rw [hstep] at hshortD
  change fderiv ℝ (chartCost y) ((Φ q).1,(Ψ q).1) ((fderiv ℝ Φ q k).1,z) =
    ε * (metric y (Ψ q).1 (Ψ q).2 z - metric y (Φ q).1 (Φ q).2 (fderiv ℝ Φ q k).1) at hshortD
  rw [hshortD]
  have hb := chart_flow_boundary x y τ hq hτ k
  change metric y (Φ q).1 (Φ q).2 (fderiv ℝ Φ q k).1 = metric x q.1 q.2 k.1 + τ * fderiv ℝ (chartKinetic x) q k at hb
  rw [hb]
  field_simp [hε]
  ring

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

 theorem generating_focal_hessian {F : (E × E) × E → ℝ} {Y : E × E → E}
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {q : E × E} {κ : E}
    (hF : ContDiffAt ℝ 2 F (q,Y q)) (hY : DifferentiableAt ℝ Y q)
    (hker : fderiv ℝ Y q (0,κ) = 0)
    (hgrad : ∀ᶠ r in 𝓝 q, ∀ a b : E,
      fderiv ℝ F (r,Y r) ((a,b),0) = -G r.1 r.2 a) (a b : E) :
    fderiv ℝ (fderiv ℝ F) (q,Y q) ((0,κ),0) ((a,b),0) = -G q.1 κ a := by
  let r : ℝ → E × E := fun t => q+t•(0,κ)
  have hr₀ : r 0 = q := by simp [r]
  have hr : HasDerivAt r (0,κ) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const ((0,κ) : E × E)).const_add q using 1
    first | rfl | simp
  have hy : HasDerivAt (Y ∘ r) 0 0 := by
    have hd : HasFDerivAt Y (fderiv ℝ Y q) (r 0) := by simpa only [hr₀] using hY.hasFDerivAt
    simpa only [hker] using hd.comp_hasDerivAt 0 hr
  have hp : HasDerivAt (fun t => (r t,Y (r t))) ((0,κ),0) 0 := hr.prodMk hy
  have hF' : ContDiffAt ℝ 2 F (r 0,Y (r 0)) := by simpa only [hr₀] using hF
  have hh := derivative_hessian_along_curve hF' hp (((a,b),0) : (E × E) × E)
  have he : (fun t => fderiv ℝ F (r t,Y (r t)) ((a,b),0)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => -G q.1 (q.2+t•κ) a) := by
    have htend : Tendsto r (𝓝 (0 : ℝ)) (𝓝 q) := by simpa only [hr₀] using hr.continuousAt.tendsto
    filter_upwards [htend hgrad] with t ht
    have hfst : (r t).1 = q.1 := by change q.1+t•(0 : E) = q.1; simp
    have hsnd : (r t).2 = q.2+t•κ := rfl
    change ∀ a b : E, fderiv ℝ F (r t,Y (r t)) ((a,b),0) = -G (r t).1 (r t).2 a at ht
    rw [hfst,hsnd] at ht
    exact ht a b
  have hlin : HasDerivAt (fun t : ℝ => -G q.1 (q.2+t•κ) a) (-G q.1 κ a) 0 := by
    have hk := ((hasDerivAt_id (0 : ℝ)).smul_const κ).const_add q.2
    convert! ((G q.1).hasFDerivAt.comp_hasDerivAt 0 hk |>.clm_apply (hasDerivAt_const (0 : ℝ) a)).neg using 1
    simp
  simpa only [hr₀] using hh.unique (hlin.congr_of_eventuallyEq he)

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingNeighborhood
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

 theorem GeneratingChartAction.smooth {x y : M} {ε : ℝ} {q : Model n × Model n}
    (h : GeneratingChartAction x y ε q) :
    ContDiffAt ℝ ∞ (generatingAction x y ε) (q,(crossFlowCoordinates x y 1 q).1) :=
    generatingAction_smooth x y h.1 h.2.1 h.2.2.2

 theorem GeneratingChartAction.flow_smooth {x y : M} {ε : ℝ} {q : Model n × Model n}
    (h : GeneratingChartAction x y ε q) : ContDiffAt ℝ ∞ (crossFlowCoordinates x y 1) q :=
    chart_flow_smooth x y 1 h.1 h.2.2.1

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingHessian
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
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem generatingHessian_focal_oai (x y : M) {ε : ℝ} (hε : ε ≠ 0) {q : Model n × Model n}
    (hq : ∀ᶠ r in 𝓝 q, GeneratingChartAction x y ε r) {κ : Model n}
    (hker : fderiv ℝ (fun r => (crossFlowCoordinates x y 1 r).1) q (0,κ) = 0)
    (a b : Model n) :
    generatingHessian x y ε q ((0,κ),0) ((a,b),0) = -metric x q.1 κ a := by
  have h₀ := mem_of_mem_nhds hq
  have hg : ∀ᶠ r in 𝓝 q, ∀ a b : Model n,
      fderiv ℝ (generatingAction x y ε) (r,(crossFlowCoordinates x y 1 r).1) ((a,b),0) = -metric x r.1 r.2 a := by
    filter_upwards [hq] with r hr a b
    simpa only [map_zero,zero_sub] using generatingAction_gradient x y hε hr.1 hr.2.1 hr.2.2.2 (a,b) 0
  exact generating_focal_hessian
    (h₀.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (h₀.flow_smooth.fst.differentiableAt (by simp)) hker hg a b

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal_oai.{u_1}
