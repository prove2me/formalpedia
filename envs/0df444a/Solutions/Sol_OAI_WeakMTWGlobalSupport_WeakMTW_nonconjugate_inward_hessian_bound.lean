-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_inward_hessian_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:18:23.913967+00:00
-- url     : https://prove2.me/submissions/90506f1f-8b73-4b81-9622-003cd8eaed33

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actionHessian_eq_branch

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

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem stateChart_vertical (b : M) (v : TangentSpace (model n) b) :
    stateChart b (⟨b,v⟩ : TangentBundle (model n) M) =
      (chartAt (Model n) b b,
        (trivializationAt (Model n) (TangentSpace (model n)) b).continuousLinearMapAt ℝ b v) := by
  let e := trivializationAt (Model n) (TangentSpace (model n)) b
  apply Prod.ext
  · rfl
  change (e (⟨b,v⟩ : TangentBundle (model n) M)).2 = e.continuousLinearMapAt ℝ b v
  exact (e.continuousLinearMapAt_apply_of_mem ℝ
    (mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) b) v).symm

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
-- module Solutions.OAIQW_WeakMTW.Geodesics_FibreNonfocal
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

 theorem exp_coordinates_smooth (b x : M) {v : TangentSpace (model n) b}
    (hv : exp b v ∈ (chartAt (Model n) x).source) :
    ContDiffAt ℝ ∞ (fun w => chartAt (Model n) x (exp b w)) v := by
  have hch := (contMDiffOn_extChartAt (I := model n) (n := ∞) (x := x) _ hv).contMDiffAt
    ((chartAt (Model n) x).open_source.mem_nhds hv)
  exact contMDiffAt_iff_contDiffAt.mp (hch.comp v (exp_fibre_smooth b v))

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_PairExpCoordinates
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

 theorem pairExpDomain_open (x y : M) : IsOpen (pairExpDomain (n := n) x y) := by
  exact (stateChart x).continuousOn_symm.isOpen_inter_preimage (stateChart x).open_target
    ((stateChart y).open_source.preimage (geodesicFlow_smooth_fixed (n := n) (M := M) 1).continuous)

 theorem pairExpCoordinates_smooth (x y : M) :
    ContDiffOn ℝ ∞ (pairExpCoordinates (n := n) x y) (pairExpDomain (n := n) x y) := by
  intro q hq
  exact (contDiffAt_fst.prodMk (chart_flow_smooth x y 1 hq.1 hq.2).fst).contDiffWithinAt

 theorem pairExpCoordinates_vertical (x y : M) (v : TangentSpace (model n) x) :
    pairExpCoordinates (n := n) x y (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) =
      (chartAt (Model n) x x,chartAt (Model n) y (exp x v)) := by
  have hx : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  dsimp only [pairExpCoordinates]
  rw [(stateChart x).left_inv hx]
  change (_,chartAt (Model n) y (geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1)) = _
  rw [← exp_eq_geodesic]
  rfl

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BranchAction
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

 theorem branchAction_smooth (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) : ContDiffOn ℝ ∞ (branchAction x e) e.target :=
  (chartKinetic_smooth x).comp hei (fun _ hq => (hes (e.map_target hq)).1)

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
-- module Solutions.OAIQW_WeakMTW.Coordinates_FocalCoordinates
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

 theorem verticalCoordinates_eq (x : M) (v : TangentSpace (model n) x) :
    verticalCoordinates x v = stateChart x (⟨x,v⟩ : TangentBundle (model n) M) := by
  apply Prod.ext
  · rfl
  · exact tangentChartLinear_eq x v

variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]

omit [IsManifold (model n) ∞ M] in
 theorem verticalCoordinates_smooth (x : M) : ContDiff ℝ ∞ (verticalCoordinates (n := n) x) := by
   unfold verticalCoordinates
   exact contDiff_const.prodMk (tangentChartLinear (n := n) x).contDiff

end
end WeakMTW
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

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_NonconjugateBranches
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

 theorem nonfocal_line_zero (x y : M) {v w : TangentSpace (model n) x}
    (hn : Function.Injective (fderiv ℝ (fun u => chartAt (Model n) y (exp x u)) v))
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hc : HasDerivAt (fun s : ℝ => chartAt (Model n) y (exp x (v+s•w))) 0 0) : w = 0 := by
  have hd : HasDerivAt (fun s : ℝ => v+s•w) w 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v using 1
    simp
  have hF := ((exp_coordinates_smooth x y hy).differentiableAt (by simp)).hasFDerivAt
  have hF' : HasFDerivAt (fun u => chartAt (Model n) y (exp x u))
      (fderiv ℝ (fun u => chartAt (Model n) y (exp x u)) v) (v+(0 : ℝ)•w) := by simpa using hF
  have hh := (hF'.comp_hasDerivAt (l := fun u => chartAt (Model n) y (exp x u)) (f := fun s : ℝ => v+s•w) 0 hd).unique hc
  apply hn
  simpa only [map_zero] using hh

 theorem pairExpCoordinates_injective_of_nonfocal (x y : M) {v : TangentSpace (model n) x}
    (hn : Function.Injective (fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v)) (hy : exp x v ∈ (chartAt (Model n) y).source) :
    Function.Injective (fderiv ℝ (pairExpCoordinates (n := n) x y)
      (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))) := by
  let q₀ := stateChart x (⟨x,v⟩ : TangentBundle (model n) M)
  have hsrc : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hdom : q₀ ∈ pairExpDomain (n := n) x y := by
    refine ⟨(stateChart x).map_source hsrc,?_⟩
    dsimp only [q₀]
    rw [(stateChart x).left_inv hsrc]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source
    simpa only [← exp_eq_geodesic] using hy
  have hs := (pairExpCoordinates_smooth x y _ hdom).contDiffAt ((pairExpDomain_open x y).mem_nhds hdom)
  have hD := (hs.differentiableAt (by simp)).hasFDerivAt
  rw [injective_iff_map_eq_zero]
  intro k hk
  change (fderiv ℝ (pairExpCoordinates (n := n) x y) q₀) k = 0 at hk
  have hf := (hasFDerivAt_fst (𝕜 := ℝ) (p := pairExpCoordinates (n := n) x y q₀)).comp q₀ hD
  have hf' : (ContinuousLinearMap.fst ℝ (Model n) (Model n)).comp
      (fderiv ℝ (pairExpCoordinates (n := n) x y) q₀) = ContinuousLinearMap.fst ℝ (Model n) (Model n) :=
    hf.unique (hasFDerivAt_fst (𝕜 := ℝ) (p := q₀))
  have hk₁ : k.1 = 0 := by
    have hh := congrArg (fun A : (Model n × Model n) →L[ℝ] Model n => A k) hf'
    change ((fderiv ℝ (pairExpCoordinates (n := n) x y) q₀) k).1 = k.1 at hh
    rw [hk] at hh
    exact hh.symm
  let e := trivializationAt (Model n) (TangentSpace (model n)) x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) x
  let w : TangentSpace (model n) x := e.symmL ℝ x k.2
  let L := e.continuousLinearMapAt ℝ x
  have hL : L w = k.2 := e.continuousLinearMapAt_symmL he k.2
  have hcurve : HasDerivAt (fun s : ℝ => stateChart x (⟨x,v+s•w⟩ : TangentBundle (model n) M)) k 0 := by
    have hh : HasDerivAt (fun s : ℝ => (chartAt (Model n) x x,L v+s•L w)) (0,L w) 0 := by
      have hl : HasDerivAt (fun s : ℝ => L v+s•L w) (L w) 0 := by
        convert (hasDerivAt_const (0 : ℝ) (L v)).add ((hasDerivAt_id (0 : ℝ)).smul_const (L w)) using 1 <;> (first | rfl | simp)
      exact (hasDerivAt_const (0 : ℝ) (chartAt (Model n) x x)).prodMk hl
    have heq : (fun s : ℝ => stateChart x (⟨x,v+s•w⟩ : TangentBundle (model n) M)) =
        (fun s : ℝ => (chartAt (Model n) x x,L v+s•L w)) := by
      funext s
      rw [stateChart_vertical,map_add,map_smul]
    rw [heq]
    convert hh using 1
    exact Prod.ext hk₁ hL.symm
  have hD' : HasFDerivAt (pairExpCoordinates (n := n) x y) (fderiv ℝ (pairExpCoordinates (n := n) x y) q₀)
      (stateChart x (⟨x,v+(0 : ℝ)•w⟩ : TangentBundle (model n) M)) := by
    simpa only [zero_smul,add_zero] using hD
  have hcomp := hD'.comp_hasDerivAt (l := pairExpCoordinates (n := n) x y)
    (f := fun s : ℝ => stateChart x (⟨x,v+s•w⟩ : TangentBundle (model n) M)) 0 hcurve
  rw [hk] at hcomp
  have hcomp' : HasDerivAt (fun s : ℝ => (chartAt (Model n) x x, chartAt (Model n) y (exp x (v+s•w)))) 0 0 := by
    convert hcomp using 1 <;> first | rfl | (funext s; exact (pairExpCoordinates_vertical x y _).symm)
  have hc₀ := (ContinuousLinearMap.snd ℝ (Model n) (Model n)).hasFDerivAt.comp_hasDerivAt 0 hcomp'
  have hc : HasDerivAt (fun s : ℝ => chartAt (Model n) y (exp x (v+s•w))) 0 0 := by
    exact hc₀
  have hw := nonfocal_line_zero x y hn hy hc
  have hk₂ : k.2 = 0 := by rw [hw,map_zero] at hL; exact hL.symm
  exact Prod.ext hk₁ hk₂

 theorem pairExpCoordinates_inverse_of_nonfocal (x y : M) {v : TangentSpace (model n) x}
    (hn : Function.Injective (fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v)) (hy : exp x v ∈ (chartAt (Model n) y).source) :
    ∃ e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n),
      (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y ∧
      stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source ∧
      e.source ⊆ pairExpDomain (n := n) x y ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let q := stateChart x (⟨x,v⟩ : TangentBundle (model n) M)
  have hsrc : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hdom : q ∈ pairExpDomain (n := n) x y := by
    refine ⟨(stateChart x).map_source hsrc,?_⟩
    dsimp only [q]
    rw [(stateChart x).left_inv hsrc]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source
    simpa only [← exp_eq_geodesic] using hy
  let A := fderiv ℝ (pairExpCoordinates (n := n) x y) q
  let D := (LinearEquiv.ofInjectiveEndo A.toLinearMap (pairExpCoordinates_injective_of_nonfocal x y hn hy)).toContinuousLinearEquiv
  have hD : HasFDerivAt (pairExpCoordinates (n := n) x y) (D : (Model n × Model n) →L[ℝ] (Model n × Model n)) q := by
    exact (((pairExpCoordinates_smooth x y _ hdom).contDiffAt ((pairExpDomain_open x y).mem_nhds hdom)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨e,he,hev,hes,hei,_⟩ := NormalNeighborhood.exists_smooth_local_diffeomorph
    (pairExpDomain_open x y) (pairExpCoordinates_smooth x y) hdom hD
  exact ⟨e,he,hev,hes,hei⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BranchHessian
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
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem branchHessianDiag_continuous (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {v : TangentSpace (model n) x}
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source)
    (ξ : TangentSpace (model n) x) : ContinuousAt (fun w => branchHessianDiag x y e w ξ) v := by
  have heq : e (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) =
      (chartAt (Model n) x x,chartAt (Model n) y (exp x v)) := by rw [he,pairExpCoordinates_vertical]
  have ht := heq ▸ e.map_source hev
  have hA := ((branchAction_smooth x y e hes hei) _ ht).contDiffAt (e.open_target.mem_nhds ht)
  have hH := (hA.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hy : exp x v ∈ (chartAt (Model n) y).source := by
    have hh := (hes hev).2
    have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
      (stateChart_source x _).mpr (mem_chart_source (Model n) x)
    rw [(stateChart x).left_inv hp] at hh
    have hg : geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source :=
      (stateChart_source y _).mp hh
    simpa only [← exp_eq_geodesic] using hg
  have hq : ContDiffAt ℝ ∞ (fun w => (chartAt (Model n) x x,chartAt (Model n) y (exp x w))) v :=
    contDiffAt_const.prodMk (exp_coordinates_smooth x y hy)
  have hfirst : ContinuousAt (fun w => fderiv ℝ (fderiv ℝ (branchAction x e))
      (chartAt (Model n) x x,chartAt (Model n) y (exp x w))
      (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0)) v :=
    (((hH.comp v hq).clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt
  refine hfirst.add ?_
  unfold lowerChristoffel
  fun_prop

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_InwardHessianBound
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

 theorem nonconjugate_hessian_lower_near (x : M) {v : TangentSpace (model n) x}
    (hn : Nonconjugate x v) (ξ : TangentSpace (model n) x) :
    ∃ L : ℝ, ∀ᶠ w in 𝓝 v, w ∈ injectivityDomain x → -L ≤ actionHessian x w ξ ξ := by
  let y := exp x v
  obtain ⟨e,he,hev,hes,hei⟩ := pairExpCoordinates_inverse_of_nonfocal x y hn (mem_chart_source (Model n) y)
  have hB := branchHessianDiag_continuous x y e he hes hei hev ξ
  have hlow : ∀ᶠ w in 𝓝 v, branchHessianDiag x y e v ξ-1 < branchHessianDiag x y e w ξ :=
    continuousAt_const.eventually_lt hB (by linarith)
  have hsrc : ∀ᶠ w in 𝓝 v, verticalCoordinates x w ∈ e.source :=
    (verticalCoordinates_smooth x).continuous.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (by simpa only [verticalCoordinates_eq] using hev))
  refine ⟨1-branchHessianDiag x y e v ξ,?_⟩
  filter_upwards [hlow,hsrc] with w hw hwe hwi
  rw [verticalCoordinates_eq] at hwe
  rw [actionHessian_eq_branch x y e he hes hei hwi hwe ξ]
  linarith

 theorem nonconjugate_inward_hessian_bound_oai (x : M) {v : TangentSpace (model n) x}
    (hm : v ∈ minimizingDomain x) (hn : Nonconjugate x v) (ξ : TangentSpace (model n) x) :
    ∃ L δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      -L ≤ actionHessian x ((1-h)•v) ξ ξ := by
  obtain ⟨L,hL⟩ := nonconjugate_hessian_lower_near x hn ξ
  have hc : ContinuousAt (fun h : ℝ => (1-h)•v) 0 := (continuousAt_const.sub continuousAt_id).smul continuousAt_const
  have hh : ∀ᶠ h in 𝓝 (0 : ℝ), (1-h)•v ∈ injectivityDomain x →
      -L ≤ actionHessian x ((1-h)•v) ξ ξ := by
    have hc' : Tendsto (fun h : ℝ => (1-h)•v) (𝓝 0) (𝓝 v) := by simpa using hc.tendsto
    exact hc' hL
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨L,min δ 1,lt_min hδ zero_lt_one,?_⟩
  intro h hh₀ hhδ
  have hhδ' : h < δ := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hh₁ : h < 1 := lt_of_lt_of_le hhδ (min_le_right _ _)
  exact hball (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hh₀] using hhδ')
    (strict_radial_mem_injectivity hm (by linarith) (by linarith))

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_inward_hessian_bound_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_inward_hessian_bound_oai.{u_1}
