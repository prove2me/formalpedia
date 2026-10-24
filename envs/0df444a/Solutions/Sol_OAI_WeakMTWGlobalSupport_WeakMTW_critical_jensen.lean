-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:07:02.884555+00:00
-- url     : https://prove2.me/submissions/510db339-5f29-4858-97b4-66d2d03c5654

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_hessian_limit
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actionHessianDiag_smooth
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_minimizing_vector
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exp_coordinates_local_inverse
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_initialCost_geometry

section
-- module Solutions.OAIQW_WeakMTW.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
-- module Solutions.OAIQW_WeakMTW.Variations_CovariantActionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter Set
open scoped Topology ContDiff
namespace RadialHessianCalculus
open CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 theorem actionForm_eq (G : E → MetricTensor E) (f : E → ℝ) (a ν v w : E)
    (hpos : ∀ z : E, z ≠ 0 → 0 < G a z z)
    (hsymm : ∀ z z', G a z z' = G a z' z) :
    actionForm G f a ν v w = fderiv ℝ (fderiv ℝ f) a v w +
      G a ν (christoffel G a v w) := by
  change _ + lowerChristoffel (fderiv ℝ G a) v w ν = _
  rw [hsymm ν,metric_christoffel hpos,lowerChristoffel_apply]

end
end RadialHessianCalculus
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_SecondCurveChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter
open scoped Topology ContDiff
namespace SecondCurveChain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem second {f : E → ℝ} {c : ℝ → E} {t : ℝ} {v acc : E}
    (hf : ContDiffAt ℝ 2 f (c t)) (hc : ContDiffAt ℝ 2 c t)
    (hv : HasDerivAt c v t) (ha : HasDerivAt (deriv c) acc t) :
    deriv (deriv (f ∘ c)) t =
      fderiv ℝ (fderiv ℝ f) (c t) v v + fderiv ℝ f (c t) acc := by
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDc := hD.hasFDerivAt.comp_hasDerivAt t hv
  have hprod := hDc.clm_apply ha
  have heq : deriv (f ∘ c) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (c s) (deriv c s)) := by
    have hevent := (hf.eventually (by norm_num)).filter_mono hv.continuousAt.tendsto
    filter_upwards [hevent, hc.eventually (by norm_num)] with s hs hcs
    change ContDiffAt ℝ 2 f (c s) at hs
    exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      (hcs.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [heq.deriv_eq]
  simpa only [Function.comp_def,hv.deriv] using hprod.deriv

end SecondCurveChain
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeodesicSecondCoordinates
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

 theorem chart_geodesic_second (x : M) (ξ : TangentSpace (model n) x)
    (f : Model n → ℝ) (hf : ContDiffAt ℝ 2 f (chartAt (Model n) x x)) :
    deriv (deriv (fun t : ℝ => f (chartAt (Model n) x (exp x (t • ξ))))) 0 =
      fderiv ℝ (fderiv ℝ f) (chartAt (Model n) x x)
        (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2
        (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2 -
      fderiv ℝ f (chartAt (Model n) x x)
        (christoffel (metric x) (chartAt (Model n) x x)
          (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2
          (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2) := by
  let p : TangentBundle (model n) M := ⟨x,ξ⟩
  let C : ℝ → Model n := fun t => chartAt (Model n) x (geodesic p t)
  let V : ℝ → Model n := fun t => (stateChart x (geodesicFlow t p)).2
  let a := chartAt (Model n) x x
  let u := (stateChart x p).2
  have hx : x ∈ (chartAt (Model n) x).source := mem_chart_source (Model n) x
  have hC₀ : C 0 = a := by simp [C,a,p,geodesic_zero]
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, geodesic p t ∈ (chartAt (Model n) x).source := by
    have hp : geodesic p 0 ∈ (chartAt (Model n) x).source := by simpa only [geodesic_zero, p] using hx
    exact (geodesic_smooth p).continuous.continuousAt.preimage_mem_nhds
      ((chartAt (Model n) x).open_source.mem_nhds hp)
  have hcd : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt C (V t) t := by
    filter_upwards [hnear] with t ht
    exact (geodesic_coordinate_equation x p t ht).fst
  have hV₀ : V 0 = u := by simp only [V,u,geodesicFlow_zero]
  have hdc : HasDerivAt C u 0 := hV₀ ▸ hcd.self_of_nhds
  have hstate := geodesic_coordinate_equation_zero x p hx
  have hVd : HasDerivAt V (-christoffel (metric x) a u u) 0 := hstate.snd
  have hdeq : deriv C =ᶠ[𝓝 (0 : ℝ)] V := hcd.mono (fun _ ht => ht.deriv)
  have hdd : HasDerivAt (deriv C) (-christoffel (metric x) a u u) 0 :=
    hVd.congr_of_eventuallyEq hdeq
  have hcS : ContDiffAt ℝ ∞ C 0 := by
    apply contMDiffAt_iff_contDiffAt.mp
    have hh : ContMDiffAt (model n) (model n) ∞ (chartAt (Model n) x) x := contMDiffOn_chart.contMDiffAt
      ((chartAt (Model n) x).open_source.mem_nhds hx)
    have hc := (geodesic_smooth p).contMDiffAt (x := (0 : ℝ))
    have hcx : geodesic p 0 = x := by simp only [geodesic_zero,p]
    have hh' : ContMDiffAt (model n) (model n) ∞ (chartAt (Model n) x) (geodesic p 0) := by
      rw [hcx]
      exact hh
    exact hh'.comp 0 hc
  have hfC : ContDiffAt ℝ 2 f (C 0) := by rw [hC₀]; exact hf
  have hh := SecondCurveChain.second hfC (hcS.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hdc hdd
  simp only [hC₀,map_neg,← sub_eq_add_neg] at hh
  have he : (fun t : ℝ => f (chartAt (Model n) x (exp x (t • ξ)))) = f ∘ C := by
    ext t
    rw [exp_mul_eq_geodesic (p := p)]
    rfl
  rw [he]
  exact hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_MTWConcavity
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

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] [IsManifold (model n) ∞ M] in
 theorem mtw_eq_hessian_diag (x : M) (v ξ η : TangentSpace (model n) x) :
    mtw x v ξ η = -(3/2 : ℝ) *
      deriv (fun s : ℝ => deriv (fun r : ℝ => actionHessianDiag x (v+r•η) ξ) s) 0 := rfl

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] [IsManifold (model n) ∞ M] in
 theorem mtw_on_line_eq (x : M) (v ξ η : TangentSpace (model n) x) (s : ℝ) :
    mtw x (v+s•η) ξ η = -(3/2 : ℝ) *
      deriv (deriv (fun r : ℝ => actionHessianDiag x (v+r•η) ξ)) s := by
  let F : ℝ → ℝ := fun r => actionHessianDiag x (v+r•η) ξ
  have he : (fun r => actionHessianDiag x (v+s•η+r•η) ξ) = fun r => F (r+s) := by
    funext r
    dsimp only [F]
    congr 1
    rw [add_smul]
    abel
  rw [mtw_eq_hessian_diag,he]
  simp only [deriv_comp_add_const,zero_add]
  rfl

 theorem transverse_action_concave (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) (v ξ η : TangentSpace (model n) x) (hξη : inner ℝ ξ η = 0)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hI : ∀ s ∈ D, v+s•η ∈ injectivityDomain x) :
    ConcaveOn ℝ D (fun s => actionHessianDiag x (v+s•η) ξ) := by
  let F : ℝ → ℝ := fun s => actionHessianDiag x (v+s•η) ξ
  have hF (s : ℝ) (hs : s ∈ D) : ContDiffAt ℝ ∞ F s :=
    (actionHessianDiag_smooth x (hI s hs) ξ).comp s (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  refine concaveOn_of_deriv2_nonpos hD (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
    (fun s hs => ((hF s (interior_subset hs)).differentiableAt (by simp)).differentiableWithinAt)
    (fun s hs => ?_) (fun s hs => ?_)
  · have hh : ContDiffAt ℝ ∞ (deriv F) s := by
      have hd := (hF s (interior_subset hs)).fderiv_right (m := ∞) (by simp)
      simpa only [fderiv_apply_one_eq_deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
    exact (hh.differentiableAt (by simp)).differentiableWithinAt
  · have hh := hMTW x (v+s•η) (hI s (interior_subset hs)) ξ η hξη
    rw [mtw_on_line_eq] at hh
    change deriv (deriv F) s ≤ 0
    change 0 ≤ -(3/2 : ℝ) * deriv (deriv F) s at hh
    linarith

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

 theorem actionHessian_diag (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    actionHessian x v ξ ξ = actionHessianDiag x v ξ := by
  let f : Model n → ℝ := initialCost x (exp x v)
  let a := chartAt (Model n) x x
  let u := tangentChartLinear x ξ
  have hgeom := initialCost_geometry x hv
  have hh := chart_geodesic_second x ξ f
    (hgeom.1.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top))
  rw [← tangentChartLinear_eq] at hh
  have he : (fun t : ℝ => f (chartAt (Model n) x (exp x (t • ξ)))) =ᶠ[𝓝 0]
      (fun t : ℝ => cost (exp x (t • ξ)) (exp x v)) := by
    have hcont : ContinuousAt (fun t : ℝ => exp x (t • ξ)) 0 :=
      (exp_fibre_smooth x).continuous.continuousAt.comp (continuousAt_id.smul continuousAt_const)
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, exp x (t•ξ) ∈ (chartAt (Model n) x).source := by
      apply hcont.preimage_mem_nhds
      simpa only [zero_smul,exp_zero] using (chartAt (Model n) x).open_source.mem_nhds (mem_chart_source (Model n) x)
    filter_upwards [hnear] with t ht
    exact congrArg (fun z => cost z (exp x v)) ((chartAt (Model n) x).left_inv ht)
  rw [he.deriv.deriv_eq] at hh
  change actionForm (metric x) f a (tangentChartLinear x v) u u = _
  rw [actionForm_eq (metric x) f a (tangentChartLinear x v) u u
    (fun z hz => metric_positive x ((chartAt (Model n) x).map_source (mem_chart_source (Model n) x)) hz)
    (metric_symmetric x a)]
  rw [hgeom.2.1] at hh
  change actionHessianDiag x v ξ = _ at hh
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_TransverseJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Pointwise
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem transverse_hessian_concave (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) (ξ : TangentSpace (model n) x) {K : Set (TangentSpace (model n) x)}
    (hK : Convex ℝ K) (hI : K ⊆ injectivityDomain x)
    (horth : ∀ u ∈ K, ∀ v ∈ K, inner ℝ ξ (v-u) = 0) :
    ConcaveOn ℝ K (fun v => actionHessian x v ξ ξ) := by
  refine ⟨hK,?_⟩
  intro u hu v hv a b ha hb hab
  have hlineI : ∀ t ∈ Icc (0 : ℝ) 1, u+t•(v-u) ∈ injectivityDomain x := by
    intro t ht
    apply hI
    have hh := hK hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert hh using 1
    module
  have hconc := transverse_action_concave hMTW x u ξ (v-u) (horth u hu v hv) (convex_Icc 0 1) hlineI
  have hh := hconc.2 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) ha hb hab
  have huv : a•u+b•v = u+b•(v-u) := by
    have ha' : a = 1-b := by linarith
    rw [ha']
    module
  have hw := hK hu hv ha hb hab
  rw [huv] at hw ⊢
  simp only [zero_smul,add_zero,one_smul,add_sub_cancel,smul_eq_mul,mul_zero,mul_one,zero_add] at hh
  rw [← actionHessian_diag x (hI hu) ξ,← actionHessian_diag x (hI hv) ξ,
    ← actionHessian_diag x (hI hw) ξ] at hh
  exact hh

 theorem transverse_hessian_jensen (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) (ξ : TangentSpace (model n) x) {K : Set (TangentSpace (model n) x)}
    (hK : Convex ℝ K) (hI : K ⊆ injectivityDomain x)
    (horth : ∀ u ∈ K, ∀ v ∈ K, inner ℝ ξ (v-u) = 0)
    {ι : Type*} (T : Finset ι) (a : ι → TangentSpace (model n) x) (θ : ι → ℝ)
    (hθ : ∀ i ∈ T, 0 ≤ θ i) (hsum : ∑ i ∈ T, θ i = 1)
    (ha : ∀ i ∈ T, a i ∈ K) :
    (∑ i ∈ T, θ i * actionHessian x (a i) ξ ξ) ≤
      actionHessian x (∑ i ∈ T, θ i • a i) ξ ξ := by
  simpa only [smul_eq_mul] using
    (transverse_hessian_concave hMTW x ξ hK hI horth).le_map_sum hθ hsum ha

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CriticalJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Pointwise
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem actionHessian_continuous (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    ContinuousAt (fun w => actionHessian x w ξ ξ) v := by
  apply (actionHessianDiag_smooth x hv ξ).continuousAt.congr_of_eventuallyEq
  filter_upwards [(injectivityDomain_open x).mem_nhds hv] with w hw
  exact actionHessian_diag x hw ξ

 theorem transverse_face_jensen (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    (ξ : TangentSpace (model n) x) {S : Set (TangentSpace (model n) x)}
    (hS : Convex ℝ S) (hI : S ⊆ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0) :
    (∑ i, θ i * actionHessian x (a i) ξ ξ) ≤ actionHessian x b ξ ξ := by
  classical
  let aa : κ → TangentSpace (model n) x := fun i => if θ i = 0 then b else a i
  let T : Set (TangentSpace (model n) x) := S ∩ {v | inner ℝ ξ v = inner ℝ ξ b}
  have hT : Convex ℝ T := by
    intro u hu v hv r t hr ht hrt
    refine ⟨hS hu.1 hv.1 hr ht hrt,?_⟩
    change inner ℝ ξ (r•u+t•v) = inner ℝ ξ b
    have hu' : inner ℝ ξ u = inner ℝ ξ b := hu.2
    have hv' : inner ℝ ξ v = inner ℝ ξ b := hv.2
    simp only [inner_add_right,inner_smul_right,hu',hv']
    rw [← add_mul,hrt,one_mul]
  have haa (i : κ) : aa i ∈ T := by
    by_cases hi : θ i = 0
    · simp only [aa,ite_eq_left hi,T,mem_inter_iff,mem_ofPred_eq,and_true]
      exact hb
    · refine ⟨by simpa only [aa,ite_eq_right hi] using ha i,?_⟩
      have hh := horth i hi
      rw [inner_sub_right] at hh
      simpa only [aa,ite_eq_right hi,Set.mem_ofPred_eq] using sub_eq_zero.mp hh
  have horthT : ∀ u ∈ T, ∀ v ∈ T, inner ℝ ξ (v-u) = 0 := by
    intro u hu v hv
    rw [inner_sub_right,hv.2,hu.2,sub_self]
  have hbar : ∑ i, θ i • aa i = b := by
    rw [← hbary]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : θ i = 0 <;> simp [aa,hi]
  have hj := transverse_hessian_jensen hMTW x ξ hT (fun _ h => hI h.1) horthT
    Finset.univ aa θ (fun i _ => hθ i) (by simpa using hsum) (fun i _ => haa i)
  simp only [hbar] at hj
  convert hj using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : θ i = 0 <;> simp [aa,hi]

 theorem critical_jensen_oai (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    (ξ : TangentSpace (model n) x) {S : Set (TangentSpace (model n) x)}
    (hS : Convex ℝ S) {s : ℝ} (hs : 0 < s)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ S, r•a ∈ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0)
    (haI : ∀ i, s•a i ∈ injectivityDomain x)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (hB : stateChart x (⟨x,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    (∑ i, θ i * actionHessian x (s•a i) ξ ξ) ≤
      branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ := by
  have hr : ∀ᶠ r : ℝ in 𝓝[<] s, 0 ≤ r ∧ r < s := by
    filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hrs
    exact ⟨hr.le,hrs⟩
  have ht (v : TangentSpace (model n) x) : Tendsto (fun r : ℝ => r•v) (𝓝[<] s) (𝓝 (s•v)) :=
    (continuous_id.smul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimB := B.hessian_limit hB ξ (ht b) (hr.mono (fun r hrs => hbelow r hrs.1 hrs.2 b hb))
  have hlimA := tendsto_finsetSum Finset.univ (fun i _ =>
    (((actionHessian_continuous x (haI i) ξ).tendsto.comp (ht (a i))).const_mul (θ i)))
  apply le_of_tendsto_of_tendsto hlimA hlimB
  filter_upwards [hr] with r hr
  have hbar : ∑ i, θ i • (r•a i) = r•b := by
    rw [← hbary,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  apply transverse_face_jensen hMTW x ξ (hS.smul r)
    (fun _ ⟨v,hv,he⟩ => he ▸ hbelow r hr.1 hr.2 v hv)
    (fun i => r•a i) θ ⟨b,hb,rfl⟩ (fun i => ⟨a i,ha i,rfl⟩) hθ hsum hbar
  intro i hi
  rw [← smul_sub,inner_smul_right,horth i hi,mul_zero]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen_oai.{u_1, u_2} := @OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen_oai.{u_1, u_2}
