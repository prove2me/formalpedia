-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:07:27.428992+00:00
-- url     : https://prove2.me/submissions/3c2876dc-4ea4-47af-b31c-043b41625a5b

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
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartScaling
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

 theorem stateChart_mulState (x : M) (a : ℝ) (p : TangentBundle 𝓘(ℝ, E) M)
    (hp : p ∈ (stateChart x).source) :
    stateChart x (mulState a p) = ((stateChart x p).1,a • (stateChart x p).2) := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : p.1 ∈ e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet] using (stateChart_source x p).mp hp
  apply Prod.ext
  · rfl
  change (e ⟨p.1,a•p.2⟩).2 = a • (e p).2
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hb,
    ← e.continuousLinearMapAt_apply_of_mem ℝ hb,map_smul]

 theorem stateChart_symm_mul (x : M) (a : ℝ) {q : E × E}
    (hq : q ∈ (stateChart x).target) :
    (stateChart x).symm (q.1,a•q.2) = mulState a ((stateChart x).symm q) := by
  have hq' := (stateChart_target x q).mp hq
  rw [stateChart_symm x (q := (q.1,a•q.2)) hq',stateChart_symm x hq']
  change (⟨(chartAt E x).symm q.1,chartLift x q.1 (a•q.2)⟩ : TangentBundle 𝓘(ℝ, E) M) =
    ⟨(chartAt E x).symm q.1,a•chartLift x q.1 q.2⟩
  rw [map_smul]

end
end RiemannianLocal
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
-- module Solutions.OAIQW_WeakMTW.Geodesics_GeneralFirstVariation
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

theorem geodesic_general_pairing {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hV : ContDiffOn ℝ 1 V U)
    (hmem : ∀ q ∈ U, c q ∈ S)
    (hct : ∀ q ∈ U, HasDerivAt (fun t => c (t, q.2)) (V q) q.1)
    (hVt : ∀ q ∈ U, HasDerivAt (fun t => V (t, q.2))
      (-christoffel G (c q) (V q) (V q)) q.1)
    {T : ℝ} (hT : 0 ≤ T) {P : Set ℝ} (hP : P ∈ 𝓝 (0 : ℝ))
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P, (t, s) ∈ U)
    : ∀ t ∈ Icc (0 : ℝ) T,
      G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) =
        G (c (0, 0)) (V (0, 0)) (fderiv ℝ c (0, 0) (0, 1)) +
        t * (fderiv ℝ G (c (0,0)) (fderiv ℝ c (0,0) (0,1)) (V (0,0)) (V (0,0)) / 2 +
          G (c (0,0)) (V (0,0)) (fderiv ℝ V (0,0) (0,1))) := by
  have hP0 : (0 : ℝ) ∈ P := mem_of_mem_nhds hP
  have h00 : (0, (0 : ℝ)) ∈ U := hseg 0 ⟨le_rfl, hT⟩ 0 hP0
  let J : ℝ → E := fun t => fderiv ℝ c (t, 0) (0, 1)
  let W : ℝ → E := fun t => fderiv ℝ V (t, 0) (0, 1)
  have hq : ∀ t ∈ Icc (0 : ℝ) T, (t, (0 : ℝ)) ∈ U := fun t ht => hseg t ht 0 hP0
  have hCdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ c (t, 0) :=
    fun t ht => ((hc _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hVdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ V (t, 0) :=
    fun t ht => ((hV _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hdJ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt J (W t) t := by
    intro t ht
    exact VariationCalculus.parameter_variation_hasDerivAt hU hc hct (hq t ht) (hVdiff t ht)
  have henergy : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P,
      G (c (t, s)) (V (t, s)) (V (t, s)) = G (c (0,s)) (V (0,s)) (V (0,s)) := by
    intro t ht s hs
    have he := geodesic_energy_constant hS hG hsym hpos
      (fun r hr => hmem _ (hseg r hr s hs))
      (fun r hr => hct _ (hseg r hr s hs)) (fun r hr => hVt _ (hseg r hr s hs)) t ht
    exact he
  have henergyD : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
        2 * G (c (t, 0)) (V (t, 0)) (W t) = fderiv ℝ G (c (0,0)) (J 0) (V (0,0)) (V (0,0)) +
        2 * G (c (0,0)) (V (0,0)) (W 0) := by
    intro t ht
    have hGs := (hG _ (hmem _ (hq t ht))).differentiableAt (hS.mem_nhds (hmem _ (hq t ht)))
    have hdL := hasDerivAt_metric_pairing hGs
      (parameter_hasDerivAt (hCdiff t ht)) (parameter_hasDerivAt (hVdiff t ht))
      (parameter_hasDerivAt (hVdiff t ht))
    have hdR := hasDerivAt_metric_pairing
      ((hG _ (hmem _ h00)).differentiableAt (hS.mem_nhds (hmem _ h00)))
      (parameter_hasDerivAt (hCdiff 0 ⟨le_rfl,hT⟩))
      (parameter_hasDerivAt (hVdiff 0 ⟨le_rfl,hT⟩))
      (parameter_hasDerivAt (hVdiff 0 ⟨le_rfl,hT⟩))
    have heq : (fun s => G (c (t, s)) (V (t, s)) (V (t, s))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => G (c (0,s)) (V (0,s)) (V (0,s))) := by
      filter_upwards [hP] with s hs
      exact henergy t ht s hs
    have he := hdL.unique (hdR.congr_of_eventuallyEq heq)
    rw [hsym _ (hmem _ (hq t ht)) _ (V (t, 0)),
      hsym _ (hmem _ h00) _ (V (0,0))] at he
    dsimp only [J,W] at ⊢
    linarith
  let A : ℝ := fderiv ℝ G (c (0,0)) (J 0) (V (0,0)) (V (0,0)) / 2 +
    G (c (0,0)) (V (0,0)) (W 0)
  have hpair : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun r => G (c (r, 0)) (V (r, 0)) (J r)) A t := by
    intro t ht
    have hm := hmem _ (hq t ht)
    have hd := geodesic_pairing_hasDerivAt (c := fun r => c (r, 0)) (V := fun r => V (r, 0)) (J := J) ((hG _ hm).differentiableAt (hS.mem_nhds hm))
      (hpos _ hm) (hct _ (hq t ht)) (hVt _ (hq t ht)) (hdJ t ht)
    convert! hd using 1
    dsimp [A]
    linarith [henergyD t ht]
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => G (c (t, 0)) (V (t, 0)) (J t) - t * A)
    (fun t ht => ((hpair t ht).sub ((hasDerivAt_id t).mul_const A)).continuousAt.continuousWithinAt)
    (fun t ht => by
      convert! ((hpair t (Ico_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).mul_const A)).hasDerivWithinAt using 1; simp)
  intro t ht
  have he := hconst t ht
  simp only [zero_mul, sub_zero] at he
  change _ = _ + t * A
  linarith

end
end FirstVariation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_FlowFirstVariation
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

 theorem flow_first_variation {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0,q) ∈ U → Φ (0,q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t,q.2)) (geodesicSpray G (Φ q)) q.1)
    {q : E × E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t,q) ∈ U) (w : E × E) :
    G (Φ (T,q)).1 (Φ (T,q)).2 (fderiv ℝ Φ (T,q) (0,w)).1 =
      G q.1 q.2 w.1 + T * (fderiv ℝ G q.1 w.1 q.2 q.2 / 2 + G q.1 q.2 w.2) := by
  let χ : ℝ × ℝ → ℝ × (E × E) := fun z => (z.1,q+z.2 • w)
  have hχ : ContDiff ℝ ∞ χ := contDiff_fst.prodMk
    (contDiff_const.add (contDiff_snd.smul contDiff_const))
  let W := χ ⁻¹' U
  have hW : IsOpen W := hU.preimage hχ.continuous
  let c : ℝ × ℝ → E := fun z => (Φ (χ z)).1
  let V : ℝ × ℝ → E := fun z => (Φ (χ z)).2
  have hcomp : ContDiffOn ℝ ∞ (Φ ∘ χ) W := hΦ.comp hχ.contDiffOn (fun _ hz => hz)
  have hcSmooth : ContDiffOn ℝ ∞ c W := hcomp.fst
  have hc : ContDiffOn ℝ 2 c W := hcSmooth.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hVSmooth : ContDiffOn ℝ ∞ V W := hcomp.snd
  have hV : ContDiffOn ℝ 1 V W := hVSmooth.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T, (t,s) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hm : χ (t,0) ∈ U := by simpa [χ] using hseg t ht
    exact ((hχ.continuous.comp continuous_swap).continuousAt (x := (0,t))).preimage_mem_nhds
      (hU.mem_nhds hm)
  let P : Set ℝ := {s | ∀ t ∈ Icc (0 : ℝ) T, (t,s) ∈ W}
  have hP : P ∈ 𝓝 (0 : ℝ) := hnear
  have hfan := geodesic_general_pairing hS (hG.differentiableOn (by simp)) hsym hpos
    hW hc hV (fun z hz => (hode (χ z) hz).1)
    (fun z hz => (hode (χ z) hz).2.fst)
    (fun z hz => (hode (χ z) hz).2.snd) hT hP (fun t ht s hs => hs t ht)
    T ⟨hT,le_rfl⟩
  have hdχ (t : ℝ) : HasFDerivAt χ
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w))
      (t,0) :=
    (hasFDerivAt_fst (p := (t,(0 : ℝ)))).prodMk
      (((hasFDerivAt_snd (p := (t,(0 : ℝ)))).smul_const w).const_add q)
  have hfd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      fderiv ℝ c (t,0) (0,1) = (fderiv ℝ Φ (t,q) (0,w)).1 ∧
      fderiv ℝ V (t,0) (0,1) = (fderiv ℝ Φ (t,q) (0,w)).2 := by
    have hm := hseg t ht
    have hd := ((hΦ _ hm).contDiffAt (hU.mem_nhds hm)).differentiableAt (by simp)
    have hd' : HasFDerivAt Φ (fderiv ℝ Φ (t,q)) (χ (t,0)) := by
      simpa [χ] using hd.hasFDerivAt
    have hh := hd'.comp (t,(0 : ℝ)) (hdχ t)
    constructor
    · have hh₁ : HasFDerivAt c _ (t,0) := hh.fst
      rw [hh₁.fderiv]; simp
    · have hh₂ : HasFDerivAt V _ (t,0) := hh.snd
      rw [hh₂.fderiv]; simp
  have hinit := hzero q (hseg 0 ⟨le_rfl,hT⟩)
  have hdinit := FlowLinearization.initial_variation hU (hΦ.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)) hzero
    (w := w) (hseg 0 ⟨le_rfl,hT⟩)
  rw [(hfd T ⟨hT,le_rfl⟩).1,(hfd 0 ⟨le_rfl,hT⟩).1,(hfd 0 ⟨le_rfl,hT⟩).2,hdinit] at hfan
  simpa only [c,V,χ,zero_smul,add_zero,hinit] using hfan

end
end FirstVariation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

 omit [FiniteDimensional ℝ E] in
 theorem normal_smooth (N : NormalFlow G S x₀) : ContDiffOn ℝ ∞ N.normal N.normal.source := by
   have hh : ContDiffOn ℝ ∞ (fun q => (q.1, (N.flow (N.time,q)).1)) N.normal.source :=
     contDiffOn_fst.prodMk ((N.flow_smooth.comp
       (contDiff_const.prodMk contDiff_id).contDiffOn
       (fun q hq => N.source_stays q hq _ ⟨N.time_pos.le,le_rfl⟩)).fst)
   exact hh.congr (fun q _ => N.normal_apply q)

 omit [FiniteDimensional ℝ E] in
 theorem action_hasFDerivAt (N : NormalFlow G S x₀) {q : E × E}
    (hq : DifferentiableAt ℝ G q.1) :
    HasFDerivAt N.action
      ((N.time^2/2 : ℝ) •
        (((G q.1 q.2).comp (.snd ℝ E E)) +
          ((G q.1).comp (.snd ℝ E E) + (fderiv ℝ G q.1 ∘L .fst ℝ E E).flip q.2).flip q.2)) q := by
   have hp : HasFDerivAt (Prod.fst : E × E → E) (.fst ℝ E E) q := hasFDerivAt_fst
   have hB := HasFDerivAt.comp (𝕜 := ℝ) (f := Prod.fst) (g := G) q hq.hasFDerivAt hp
   have hν : HasFDerivAt (fun z : E × E => z.2) (.snd ℝ E E) q := hasFDerivAt_snd
   have hh := (hB.clm_apply hν).clm_apply hν
   exact hh.const_mul (N.time^2/2)

 theorem action_derivative (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ y ∈ S, ∀ v w, G y v w = G y w v)
    (hpos : ∀ y ∈ S, ∀ v : E, v ≠ 0 → 0 < G y v v)
    {q : E × E} (hq : q ∈ N.normal.source) (w : E × E) :
    fderiv ℝ N.action q w = N.time *
      (G (N.flow (N.time,q)).1 (N.flow (N.time,q)).2 (fderiv ℝ N.normal q w).2 -
        G q.1 q.2 w.1) := by
   have hqS : q.1 ∈ S := by
     have hh := (N.ode _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)).1
     simpa only [N.initial _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)] using hh
   have hDG := ((hG _ hqS).contDiffAt (hS.mem_nhds hqS)).differentiableAt (by simp)
   have hΦ := ((N.flow_smooth _ (N.source_stays q hq _ ⟨N.time_pos.le,le_rfl⟩)).contDiffAt
     (N.domain_open.mem_nhds (N.source_stays q hq _ ⟨N.time_pos.le,le_rfl⟩))).differentiableAt (by simp)
   have hF := hΦ.hasFDerivAt.comp q ((hasFDerivAt_const N.time q).prodMk (hasFDerivAt_id q))
   have hN : HasFDerivAt N.normal ((ContinuousLinearMap.fst ℝ E E).prod
       ((ContinuousLinearMap.fst ℝ E E).comp (fderiv ℝ N.flow (N.time,q) ∘L
         ((0 : E × E →L[ℝ] ℝ).prod (.id ℝ (E × E)))))) q := by
     have hh := hasFDerivAt_fst.prodMk hF.fst
     exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => N.normal_apply z))
   have hv := FirstVariation.flow_first_variation hS hG hsym hpos N.domain_open
     N.flow_smooth N.initial N.ode N.time_pos.le (N.source_stays q hq) w
   rw [(N.action_hasFDerivAt hDG).fderiv, hN.fderiv]
   simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
     zero_apply,ContinuousLinearMap.id_apply,
     add_apply,ContinuousLinearMap.flip_apply,
     smul_apply,smul_eq_mul]
   change N.time^2/2 * (G q.1 q.2 w.2 + (G q.1 w.2 q.2 + fderiv ℝ G q.1 w.1 q.2 q.2)) =
     N.time * (G (N.flow (N.time,q)).1 (N.flow (N.time,q)).2
       (fderiv ℝ N.flow (N.time,q) (0,w)).1 - G q.1 q.2 w.1)
   rw [hsym q.1 hqS w.2 q.2]
   rw [hv]
   ring

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_EndpointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

omit [FiniteDimensional ℝ E] in
 theorem inverse_fst (N : NormalFlow G S x₀) {q : E × E} (hq : q ∈ N.normal.target) :
    (N.normal.symm q).1 = q.1 := by
   have hh := congrArg Prod.fst (N.normal.right_inv hq)
   simpa only [N.normal_apply] using hh

omit [FiniteDimensional ℝ E] in
 theorem action_smooth (N : NormalFlow G S x₀) (_ : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) : ContDiffOn ℝ ∞ N.action N.normal.source := by
   have hmem : ∀ q ∈ N.normal.source, q.1 ∈ S := by
     intro q hq
     have hh := (N.ode _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)).1
     simpa only [N.initial _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)] using hh
   exact contDiffOn_const.mul (((hG.comp contDiffOn_fst hmem).clm_apply contDiffOn_snd).clm_apply contDiffOn_snd)

omit [FiniteDimensional ℝ E] in
 theorem endpointAction_smooth (N : NormalFlow G S x₀) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) : ContDiffOn ℝ ∞ N.endpointAction N.normal.target :=
   (N.action_smooth hS hG).comp N.inverse_smooth (fun _ h => N.normal.map_target h)

 theorem endpointAction_derivative (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ y ∈ S, ∀ v w, G y v w = G y w v)
    (hpos : ∀ y ∈ S, ∀ v : E, v ≠ 0 → 0 < G y v v)
    {q : E × E} (hq : q ∈ N.normal.target) (w : E × E) :
    fderiv ℝ N.endpointAction q w = N.time *
      (G (N.flow (N.time,N.normal.symm q)).1 (N.flow (N.time,N.normal.symm q)).2 w.2 -
        G q.1 (N.normal.symm q).2 w.1) := by
   let p := N.normal.symm q
   have hp : p ∈ N.normal.source := N.normal.map_target hq
   have hi : DifferentiableAt ℝ N.normal.symm q :=
     ((N.inverse_smooth _ hq).contDiffAt (N.normal.open_target.mem_nhds hq)).differentiableAt (by simp)
   have hn : DifferentiableAt ℝ N.normal p :=
     ((N.normal_smooth _ hp).contDiffAt (N.normal.open_source.mem_nhds hp)).differentiableAt (by simp)
   have ha : DifferentiableAt ℝ N.action p :=
     ((N.action_smooth hS hG _ hp).contDiffAt (N.normal.open_source.mem_nhds hp)).differentiableAt (by simp)
   have hid : (N.normal ∘ N.normal.symm) =ᶠ[𝓝 q] id := by
     filter_upwards [N.normal.open_target.mem_nhds hq] with z hz
     exact N.normal.right_inv hz
   have hcomp : HasFDerivAt (N.normal ∘ N.normal.symm)
       (fderiv ℝ N.normal p ∘L fderiv ℝ N.normal.symm q) q :=
     HasFDerivAt.comp (f := N.normal.symm) (g := N.normal) q hn.hasFDerivAt hi.hasFDerivAt
   have hdi := hcomp.unique ((hasFDerivAt_id q).congr_of_eventuallyEq hid)
   have hw := congrArg (fun L : E × E →L[ℝ] E × E => L w) hdi
   have hfst : (fun z : E × E => (N.normal.symm z).1) =ᶠ[𝓝 q] Prod.fst := by
     filter_upwards [N.normal.open_target.mem_nhds hq] with z hz
     exact N.inverse_fst hz
   have hdf := hfst.fderiv_eq (𝕜 := ℝ)
   rw [hi.hasFDerivAt.fst.fderiv,hasFDerivAt_fst.fderiv] at hdf
   have hwf := congrArg (fun L : E × E →L[ℝ] E => L w) hdf
   have hAction : HasFDerivAt N.endpointAction
       (fderiv ℝ N.action p ∘L fderiv ℝ N.normal.symm q) q :=
     HasFDerivAt.comp (f := N.normal.symm) (g := N.action) q ha.hasFDerivAt hi.hasFDerivAt
   rw [hAction.fderiv,ContinuousLinearMap.comp_apply,N.action_derivative hS hG hsym hpos hp]
   simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hw
   change (fderiv ℝ N.normal.symm q w).1 = w.1 at hwf
   rw [hw,hwf,N.inverse_fst hq]

end
end NormalNeighborhood.NormalFlow
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
-- module Solutions.OAIQW_WeakMTW.Coordinates_LocalCost
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
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem cost_coord_eq_normal (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z)) :
    ∀ᶠ q : Model n × Model n in 𝓝 (chartAt (Model n) x z,chartAt (Model n) x z),
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) x).symm q.2) =
        N.time^2 / 2 * metric x q.1 (N.normal.symm q).2 (N.normal.symm q).2 := by
  let c := chartAt (Model n) x
  let a := c z
  have ha : a ∈ c.target := c.map_source hz
  have hpair : Tendsto (fun q : Model n × Model n => (c.symm q.1,c.symm q.2)) (𝓝 (a,a)) (𝓝 (z,z)) := by
    simpa only [Function.comp_def,a,c.left_inv hz] using
      ((ContinuousAt.comp (x := (a,a)) (f := Prod.fst) (g := c.symm) (c.symm.continuousAt ha) (continuousAt_fst : ContinuousAt (fun q : Model n × Model n => q.1) (a,a))).prodMk
        (ContinuousAt.comp (x := (a,a)) (f := Prod.snd) (g := c.symm) (c.symm.continuousAt ha) (continuousAt_snd : ContinuousAt (fun q : Model n × Model n => q.2) (a,a)))).tendsto
  have heq' : ∀ᶠ q : Model n × Model n in 𝓝 (a,a),
      dist (c.symm q.1) (c.symm q.2) = N.time *
        Real.sqrt (metric x (c (c.symm q.1))
          (N.normal.symm (c (c.symm q.1),c (c.symm q.2))).2
          (N.normal.symm (c (c.symm q.1),c (c.symm q.2))).2) :=
    hpair (eventually_dist_normal_pair x z hz N)
  have hnear : ∀ᶠ q : Model n × Model n in 𝓝 (a,a), q.1 ∈ c.target ∧ q.2 ∈ c.target :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (c.open_target.mem_nhds ha))
      (continuousAt_snd.preimage_mem_nhds (c.open_target.mem_nhds ha))
  filter_upwards [heq',hnear] with q hq hqt
  rw [c.right_inv hqt.1,c.right_inv hqt.2] at hq
  have hnonneg : 0 ≤ metric x q.1 (N.normal.symm q).2 (N.normal.symm q).2 := by
    rw [metric_apply,real_inner_self_eq_norm_sq]
    positivity
  dsimp only [cost]
  rw [hq,mul_pow,Real.sq_sqrt hnonneg]
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CostEndpointAction
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
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem chartCost_eq_endpointAction (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z)) :
    chartCost x =ᶠ[𝓝 (chartAt (Model n) x z,chartAt (Model n) x z)] N.endpointAction := by
  have he := N.normal_zero (chartAt (Model n) x).open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) N.center_mem
  have ht : (chartAt (Model n) x z,chartAt (Model n) x z) ∈ N.normal.target :=
    he ▸ N.normal.map_source N.center_mem
  filter_upwards [cost_coord_eq_normal x z hz N,N.normal.open_target.mem_nhds ht] with q hq hqt
  change _ = N.time^2/2 * metric x (N.normal.symm q).1 (N.normal.symm q).2 (N.normal.symm q).2
  rw [N.inverse_fst hqt]
  exact hq

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalEndpoint
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
 theorem open_interval_around_segment {S : Set ℝ} (hS : IsOpen S) {T : ℝ} (hT : 0 ≤ T)
    (hseg : Icc (0 : ℝ) T ⊆ S) :
    ∃ a b : ℝ, a < 0 ∧ T < b ∧ Ioo a b ⊆ S := by
  obtain ⟨a,c,hac,hacS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds (hseg ⟨le_rfl,hT⟩))
  obtain ⟨d,b,hdb,hdbS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds (hseg ⟨hT,le_rfl⟩))
  refine ⟨a,b,hac.1,hdb.2,?_⟩
  intro t ht
  by_cases h0 : 0 ≤ t
  · by_cases h1 : t ≤ T
    · exact hseg ⟨h0,h1⟩
    · exact hdbS ⟨hdb.1.trans (lt_of_not_ge h1),ht.2⟩
  · exact hacS ⟨ht.1,(lt_of_not_ge h0).trans hac.2⟩
end RiemannianLocal

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalState
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
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesicFlow_eq_coordinate (x : M) {U : Set ℝ} (hU : IsOpen U) (hpre : IsPreconnected U)
    {q : ℝ → Model n × Model n} (hqs : ContDiffOn ℝ ∞ q U)
    (hqe : ∀ t ∈ U, (q t).1 ∈ (chartAt (Model n) x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t) (h0 : (0 : ℝ) ∈ U)
    {t : ℝ} (ht : t ∈ U) :
    geodesicFlow t ((stateChart (E := Model n) x).symm (q 0)) =
      (stateChart x).symm (q t) := by
  have he := geodesic_eq_coordinate x hU hpre hqs hqe h0
  have he' : geodesic ((stateChart (E := Model n) x).symm (q 0)) =ᶠ[𝓝 t]
      (fun r => (chartAt (Model n) x).symm (q r).1) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds ht,he⟩
  rw [← coordinate_curve_state_chart x (hqe t ht).1 (hqe t ht).2]
  exact curveState_congr he'

 theorem geodesicFlow_normal (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {q : Model n × Model n} (hq : q ∈ N.normal.source) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) N.time) :
    geodesicFlow t ((stateChart (E := Model n) x).symm q) =
      (stateChart x).symm (N.flow (t,q)) := by
  let S : Set ℝ := {t | (t,q) ∈ N.domain}
  have hS : IsOpen S := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨a,b,ha,hb,hJ⟩ := open_interval_around_segment hS N.time_pos.le (N.source_stays q hq)
  have h0J : (0 : ℝ) ∈ Ioo a b := ⟨ha,lt_trans N.time_pos hb⟩
  have htJ : t ∈ Ioo a b := ⟨lt_of_lt_of_le ha ht.1,lt_of_le_of_lt ht.2 hb⟩
  have hqs : ContDiffOn ℝ ∞ (fun r => N.flow (r,q)) (Ioo a b) :=
    N.flow_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) hJ
  have hqe := fun r hr => N.ode (r,q) (hJ hr)
  have hh := geodesicFlow_eq_coordinate x isOpen_Ioo (convex_Ioo a b).isPreconnected hqs hqe h0J htJ
  simpa only [N.initial q (hJ h0J)] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GeodesicScaling
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

 theorem geodesic_mulState (p : TangentBundle (model n) M) (a : ℝ) :
    geodesic (mulState a p) = fun t => geodesic p (a*t) :=
  completeGeodesic_unique (geodesic_complete _) (completeGeodesic_comp_mul (geodesic_complete p) a)

 theorem geodesicFlow_mulState (p : TangentBundle (model n) M) (a t : ℝ) :
    geodesicFlow t (mulState a p) = mulState a (geodesicFlow (a*t) p) := by
  change curveState (E := Model n) (geodesic (mulState a p)) t = _
  rw [geodesic_mulState]
  simpa only [add_zero,geodesicFlow] using curveState_comp_affine (E := Model n)
    (γ := geodesic p) (a := a) (b := 0) (t := t)
    ((geodesic_smooth p).mdifferentiable (by simp) _)

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
-- module Solutions.OAIQW_WeakMTW.Geodesics_ShortFlowCoordinates
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
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem normal_flow_rescaled (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target) (a : ℝ)
    (hr : (q.1,a•q.2) ∈ N.normal.source) :
    geodesicFlow (a*N.time) ((stateChart x).symm q) ∈ (stateChart x).source ∧
    N.flow (N.time,(q.1,a•q.2)) =
      ((flowCoordinates x (a*N.time) q).1,a • (flowCoordinates x (a*N.time) q).2) := by
  have hh := geodesicFlow_normal x N hr ⟨N.time_pos.le,le_rfl⟩
  rw [stateChart_symm_mul x a hq,geodesicFlow_mulState] at hh
  have hm : N.flow (N.time,(q.1,a•q.2)) ∈ (stateChart x).target :=
    (stateChart_target x _).mpr (N.ode _ (N.source_stays _ hr _ ⟨N.time_pos.le,le_rfl⟩)).1
  have hF : geodesicFlow (a*N.time) ((stateChart x).symm q) ∈ (stateChart x).source := by
    have hmul := hh.symm ▸ (stateChart x).map_target hm
    exact (stateChart_source x _).mpr ((stateChart_source x _).mp hmul)
  refine ⟨hF,?_⟩
  have he := congrArg (stateChart x) hh
  rw [stateChart_mulState x a _ hF,(stateChart x).right_inv hm] at he
  exact he.symm

 theorem normal_endpoint_rescaled (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target) (a : ℝ)
    (hr : (q.1,a•q.2) ∈ N.normal.source) :
    N.normal (q.1,a•q.2) = (q.1,(flowCoordinates x (a*N.time) q).1) := by
  rw [N.normal_apply,(normal_flow_rescaled x N hq a hr).2]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_ShortChartAction
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
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem chartCost_short_of_normal (x z : M) (_hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z))
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target) (a : ℝ)
    (hr : (q.1,a•q.2) ∈ N.normal.source)
    (he : chartCost x =ᶠ[𝓝 (N.normal (q.1,a•q.2))] N.endpointAction) :
    ShortChartAction x (a*N.time) q := by
  have hm := normal_flow_rescaled x N hq a hr
  have hp : N.normal (q.1,a•q.2) = (q.1,(flowCoordinates x (a*N.time) q).1) :=
    normal_endpoint_rescaled x N hq a hr
  have ht := N.normal.map_source hr
  have hs := ((N.endpointAction_smooth (chartAt (Model n) x).open_target (metric_smooth x) _ ht).contDiffAt
    (N.normal.open_target.mem_nhds ht)).congr_of_eventuallyEq he
  refine ⟨hq,hm.1,hp ▸ hs,?_⟩
  intro w
  rw [← hp,he.fderiv_eq,N.endpointAction_derivative (chartAt (Model n) x).open_target
    (metric_smooth x) (fun y _ => metric_symmetric x y)
    (fun y hy v hv => metric_positive x hy hv) ht w,N.normal.left_inv hr,N.normal_apply,hm.2]
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

 theorem eventually_short_chart_action (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (v : Model n) :
    ∀ᶠ tq : ℝ × (Model n × Model n) in 𝓝 (0,(chartAt (Model n) x z,v)),
      ShortChartAction x tq.1 tq.2 := by
  let c := chartAt (Model n) x
  let q₀ : Model n × Model n := (c z,v)
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) (c.map_source hz)
  let r : ℝ × (Model n × Model n) → Model n × Model n := fun tq => (tq.2.1,(tq.1/N.time)•tq.2.2)
  have hr : Continuous r := continuous_snd.fst.prodMk
    ((continuous_fst.div_const N.time).smul continuous_snd.snd)
  have hr₀ : r (0,q₀) = (c z,0) := by simp [r,q₀]
  have hq₀ : q₀ ∈ (stateChart x).target := (stateChart_target x _).mpr (c.map_source hz)
  have hnr : ContinuousAt (fun tq => N.normal (r tq)) (0,q₀) :=
    (N.normal.continuousAt (hr₀ ▸ N.center_mem)).comp hr.continuousAt
  have hn₀ : N.normal (r (0,q₀)) = (c z,c z) := by
    rw [hr₀]
    exact N.normal_zero c.open_target (metric_smooth x)
      (fun y hy v hv => metric_positive x hy hv) N.center_mem
  have hnear : ∀ᶠ tq in 𝓝 (0,q₀), tq.2 ∈ (stateChart x).target ∧ r tq ∈ N.normal.source :=
    inter_mem (continuousAt_snd.preimage_mem_nhds ((stateChart x).open_target.mem_nhds hq₀))
      (hr.continuousAt.preimage_mem_nhds (hr₀ ▸ N.normal.open_source.mem_nhds N.center_mem))
  have he : ∀ᶠ tq in 𝓝 (0,q₀), chartCost x =ᶠ[𝓝 (N.normal (r tq))] N.endpointAction := by
    have hh := (chartCost_eq_endpointAction x z hz N).eventuallyEq_nhds
    rw [← hn₀] at hh
    exact hnr.tendsto hh
  filter_upwards [hnear,he] with tq htq heq
  have hh := chartCost_short_of_normal x z hz N htq.1 (tq.1/N.time) htq.2 heq
  simpa only [div_mul_cancel₀ _ N.time_pos.ne'] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_ShortStates
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

 theorem short_state_bridge (y : M) (p : TangentBundle (model n) M)
    (hp : geodesicFlow 1 p ∈ (stateChart y).source) {k : ℝ} (hk : 0 < k) :
    ∃ ε : ℝ, 0 < ε ∧ ε < k ∧
      ∀ᶠ p' : TangentBundle (model n) M in 𝓝 p,
        geodesicFlow (1-ε) p' ∈ (stateChart y).source ∧
        geodesicFlow 1 p' ∈ (stateChart y).source ∧
        ShortChartAction y ε (stateChart y (geodesicFlow (1-ε) p')) := by
  let d := stateChart (E := Model n) y
  let q₀ := d (geodesicFlow 1 p)
  have hz : geodesic p 1 ∈ (chartAt (Model n) y).source := (stateChart_source y _).mp hp
  have hs := eventually_short_chart_action y (geodesic p 1) hz q₀.2
  have hs' : ∀ᶠ tq : ℝ × (Model n × Model n) in 𝓝 (0,q₀), ShortChartAction y tq.1 tq.2 := hs
  obtain ⟨U,hU,hUo,hU₀⟩ := mem_nhds_iff.mp hs'
  have hflow : ContinuousAt (fun ε : ℝ => geodesicFlow (1-ε) p) 0 := by
    exact (geodesicFlow_smooth (n := n) (M := M)).continuous.continuousAt.comp
      ((continuousAt_const.sub continuousAt_id).prodMk continuousAt_const)
  have hq : ContinuousAt (fun ε : ℝ => (ε,d (geodesicFlow (1-ε) p))) 0 := by
    refine continuousAt_id.prodMk ?_
    exact (d.continuousAt (by simpa only [sub_zero] using hp)).comp hflow
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      (ε,d (geodesicFlow (1-ε) p)) ∈ U ∧ geodesicFlow (1-ε) p ∈ d.source := by
    refine inter_mem (hq.preimage_mem_nhds ?_) (hflow.preimage_mem_nhds ?_)
    · simpa only [sub_zero] using hUo.mem_nhds hU₀
    · rw [sub_zero]
      exact d.open_source.mem_nhds hp
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨ε,hε,hεk⟩ := exists_between (lt_min hδ hk)
  have hεδ : ε < δ := lt_of_lt_of_le hεk (min_le_left _ _)
  have hεk' : ε < k := lt_of_lt_of_le hεk (min_le_right _ _)
  have hh := hball (show ε ∈ Metric.ball (0 : ℝ) δ by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε] using hεδ)
  have hF : ContinuousAt (geodesicFlow (1-ε) : TangentBundle (model n) M → TangentBundle (model n) M) p :=
    (geodesicFlow_smooth_fixed (1-ε)).continuous.continuousAt
  have hC := (d.continuousAt hh.2).comp hF
  have hU' : ∀ᶠ p' : TangentBundle (model n) M in 𝓝 p,
      (ε,d (geodesicFlow (1-ε) p')) ∈ U :=
    (continuousAt_const.prodMk hC).preimage_mem_nhds (hUo.mem_nhds hh.1)
  have hτ' := hF.preimage_mem_nhds (d.open_source.mem_nhds hh.2)
  have h₁' := (geodesicFlow_smooth_fixed (n := n) (M := M) 1).continuous.continuousAt.preimage_mem_nhds
    (d.open_source.mem_nhds hp)
  refine ⟨ε,hε,hεk',?_⟩
  filter_upwards [hU',hτ',h₁'] with p' hpU hpτ hp₁
  exact ⟨hpτ,hp₁,hU hpU⟩

end
end WeakMTW
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

 theorem exists_generating_neighborhood_oai (x y : M) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hy : geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ r in 𝓝 q, GeneratingChartAction x y ε r := by
  obtain ⟨ε,hε,hε₁,hev⟩ := short_state_bridge y ((stateChart x).symm q) hy (k := 1) zero_lt_one
  have hc : ContinuousAt ((stateChart (E := Model n) x).symm) q := (stateChart x).symm.continuousAt hq
  refine ⟨ε,hε,hε₁,?_⟩
  filter_upwards [(stateChart x).open_target.mem_nhds hq,hc.tendsto hev] with r hr hh
  exact ⟨hr,hh.1,hh.2.1,hh.2.2⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood_oai.{u_1}
