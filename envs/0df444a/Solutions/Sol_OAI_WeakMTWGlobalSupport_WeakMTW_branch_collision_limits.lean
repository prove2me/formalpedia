-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T12:55:15.014376+00:00
-- url     : https://prove2.me/submissions/cb91a0a3-ebc4-405e-b879-00856aa3bf2e

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_eq_cost_along
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_gradient_weighted

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
-- module Solutions.OAIQW_WeakMTW.Coordinates_InteriorCost
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

 theorem pairExpCoordinates_state (x y : M) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) :
    pairExpCoordinates (n := n) x y (stateChart x p) =
      (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) := by
  dsimp only [pairExpCoordinates]
  rw [(stateChart x).left_inv hp]
  change (_,chartAt (Model n) y (geodesic p 1)) = _
  rw [← exp_eq_geodesic]
  rfl

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_TangentScaling
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

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentScale_continuous :
    Continuous (fun q : ℝ × TangentBundle (model n) M => mulState q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s,p⟩
  let e := trivializationAt (Model n) (TangentSpace (model n)) p.1
  have hpe : p ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) p.1)
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · exact ((contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.comp continuous_snd).continuousAt
  · have hpE : ContinuousAt (fun q : ℝ × TangentBundle (model n) M => (e q.2).2) (s,p) :=
      continuousAt_snd.comp ((e.continuousAt hpe).comp continuousAt_snd)
    have hc := continuousAt_fst.smul hpE
    apply hc.congr_of_eventuallyEq
    have hnear : ∀ᶠ q : ℝ × TangentBundle (model n) M in 𝓝 (s,p), q.2 ∈ e.source :=
      continuousAt_snd.preimage_mem_nhds (e.open_source.mem_nhds hpe)
    filter_upwards [hnear] with q hq
    have hb := e.mem_source.mp hq
    change (e (⟨q.2.1,q.1•q.2.2⟩ : TangentBundle (model n) M)).2 = q.1 • (e q.2).2
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hb,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hb,map_smul]

 theorem scaledExp_continuous :
    Continuous (fun q : ℝ × TangentBundle (model n) M => exp q.2.1 (q.1•q.2.2)) :=
    exp_total_smooth.continuous.comp tangentScale_continuous

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
-- module Solutions.OAIQW_WeakMTW.Support_FiniteActiveGraph
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
  {ι : Type*} [Fintype ι] [Nonempty ι]

omit [CompactSpace M] in
 theorem finitePotential_ge (y : ι → M) (h : ι → ℝ) (x : M) (i : ι) :
    h i-cost x (y i) ≤ finitePotential y h x :=
    Finset.le_sup' (fun j => h j-cost x (y j)) (Finset.mem_univ i)

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
-- module Solutions.OAIQW_WeakMTW.Support_ActiveSupports
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
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem activeSupport_le (y : ι → M) (h : ι → ℝ) (p : M)
    {a : TangentSpace (model n) p} (ha : a ∈ activeVelocities y h p)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (z : M) :
    activeSupport y h p a ℓ z ≤ finitePotential y h z := by
  obtain ⟨ham,i,hai,hia⟩ := ha
  have hsplit := cost_triangle_split z (exp p (ℓ•a)) (y i) hℓ (sub_pos.mpr hℓ₁)
  have hd := minimizing_shortened_dist ham hℓ.le hℓ₁.le (le_refl 1)
  simp only [one_smul,hai] at hd
  have hcost : cost (exp p (ℓ•a)) (y i) = (1-ℓ)^2*‖a‖^2/2 := by
    unfold cost
    rw [hd,mul_pow]
  have hcostp : cost p (y i) = ‖a‖^2/2 := by
    unfold cost
    rw [← hai,show dist p (exp p a) = ‖a‖ from ham]
  have hsplit' : cost z (y i) ≤ cost z (exp p (ℓ•a)) / ℓ + (1-ℓ)*‖a‖^2/2 := by
    rw [add_sub_cancel,div_one,hcost] at hsplit
    convert hsplit using 1
    field_simp [hℓ₁.ne]
  have hge := finitePotential_ge y h z i
  unfold activeSupport
  rw [hia,hcostp,minimizing_shortened_cost ham hℓ.le hℓ₁.le]
  have hid : ‖a‖^2/2-(ℓ^2*‖a‖^2/2)/ℓ = (1-ℓ)*‖a‖^2/2 := by
    field_simp [hℓ.ne']
  rw [sub_div]
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_ActionBranch
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

 namespace ActionBranch
 variable {x y : M}

 theorem smooth_value (B : ActionBranch (n := n) x y) :
    ContDiffOn ℝ ∞ B.value B.coord.target := branchAction_smooth x y B.coord B.domain B.smooth

 theorem inverse_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) :
    B.coord.symm (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) = stateChart x p := by
  rw [← pairExpCoordinates_state x y p hp,← B.map_eq,B.coord.left_inv hpe]

 theorem target_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) :
    (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) ∈ B.coord.target := by
  rw [← pairExpCoordinates_state x y p hp,← B.map_eq]
  exact B.coord.map_source hpe

 theorem value_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) :
    B.value (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) = ‖p.2‖^2/2 := by
  rw [value,branchAction, B.inverse_state p hp hpe]
  unfold chartKinetic
  have hh := stateChart_pairing x p.1 ((stateChart_source x p).mp hp) p.2 p.2
  change metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 / 2 = _
  simpa only [real_inner_self_eq_norm_sq] using congrArg (fun a : ℝ => a/2) hh

 end ActionBranch
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CollisionBranches
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
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem ActionBranch.eventually_source {x z : M} (B : ActionBranch (n := n) x z)
    {L : Filter ℕ} {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p L (𝓝 p₀)) (hpS : p₀ ∈ (stateChart x).source)
    (hpB : stateChart x p₀ ∈ B.coord.source) :
    ∀ᶠ j in L, p j ∈ (stateChart x).source ∧ stateChart x (p j) ∈ B.coord.source := by
  have h₁ : ∀ᶠ j in L, p j ∈ (stateChart x).source := hp ((stateChart x).open_source.mem_nhds hpS)
  have h₂ : ∀ᶠ j in L, stateChart x (p j) ∈ B.coord.source :=
    (((stateChart x).continuousAt hpS).tendsto.comp hp) (B.coord.open_source.mem_nhds hpB)
  exact h₁.and h₂

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem base_chart_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => chartAt (Model n) p₀.1 (p j).1) atTop (𝓝 (chartAt (Model n) p₀.1 p₀.1)) := by
  have hproj : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  exact ((chartAt (Model n) p₀.1).continuousAt (mem_chart_source (Model n) p₀.1)).tendsto.comp
    (hproj.continuousAt.tendsto.comp hp)

 theorem scaled_endpoint_chart_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) {sⱼ : ℕ → ℝ} {s : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s)) :
    Tendsto (fun j => chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp (p j).1 (sⱼ j•(p j).2)))
      atTop (𝓝 (chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2)))) := by
  exact ((chartAt (Model n) (exp p₀.1 (s•p₀.2))).continuousAt (mem_chart_source (Model n) _)).tendsto.comp
    (scaledExp_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hp))

 theorem branch_support_inequality (y : ι → M) (h : ι → ℝ)
    {x z w : M} {p q : TangentBundle (model n) M} {s ℓ : ℝ}
    (hs : 0 ≤ s) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    {a : TangentSpace (model n) p.1} (ha : a ∈ activeVelocities y h p.1)
    (B : ActionBranch (n := n) x z) (C : ActionBranch (n := n) x w)
    (hpS : (mulState s p) ∈ (stateChart x).source)
    (hqS : (mulState s q) ∈ (stateChart x).source)
    (hpB : stateChart x (mulState s p) ∈ B.coord.source)
    (hqB : stateChart x (mulState s q) ∈ B.coord.source)
    (hcollision : exp p.1 (s•p.2) = exp q.1 (s•q.2))
    (hvalue : scaledPoleValue y h s q ≤ scaledPoleValue y h s p)
    (hCp : C.value (chartAt (Model n) x p.1,chartAt (Model n) w (exp p.1 (ℓ•a))) =
      cost p.1 (exp p.1 (ℓ•a)))
    (hCq : C.value (chartAt (Model n) x q.1,chartAt (Model n) w (exp p.1 (ℓ•a))) =
      cost q.1 (exp p.1 (ℓ•a))) :
    B.value (chartAt (Model n) x q.1,chartAt (Model n) z (exp p.1 (s•p.2))) -
      B.value (chartAt (Model n) x p.1,chartAt (Model n) z (exp p.1 (s•p.2))) -
      (s/ℓ)*(C.value (chartAt (Model n) x q.1,chartAt (Model n) w (exp p.1 (ℓ•a))) -
        C.value (chartAt (Model n) x p.1,chartAt (Model n) w (exp p.1 (ℓ•a)))) ≤ 0 := by
  have hpV := B.value_state (mulState s p) hpS hpB
  have hqV := B.value_state (mulState s q) hqS hqB
  change B.value (chartAt (Model n) x p.1,chartAt (Model n) z (exp p.1 (s•p.2))) = ‖s•p.2‖^2/2 at hpV
  change B.value (chartAt (Model n) x q.1,chartAt (Model n) z (exp q.1 (s•q.2))) = ‖s•q.2‖^2/2 at hqV
  rw [← hcollision] at hqV
  rw [hpV,hqV,hCp,hCq]
  have hsup := mul_le_mul_of_nonneg_left (activeSupport_le y h p.1 ha hℓ hℓ₁ q.1) hs
  unfold activeSupport at hsup
  unfold scaledPoleValue at hvalue
  have halg : (s/ℓ)*(cost q.1 (exp p.1 (ℓ•a))-cost p.1 (exp p.1 (ℓ•a))) =
      -(s*((cost p.1 (exp p.1 (ℓ•a))-cost q.1 (exp p.1 (ℓ•a)))/ℓ)) := by ring
  rw [halg]
  nlinarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_LineTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem line_second_at {f : E → ℝ} (x v : E) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (x+t•v)) :
    deriv (deriv (fun r : ℝ => f (x+r•v))) t =
      fderiv ℝ (fderiv ℝ f) (x+t•v) v v := by
  have hv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => x+r•v) v r := fun r => by
    simpa using (hasDerivAt_id r).smul_const v |>.const_add x
  have ha : HasDerivAt (deriv (fun r : ℝ => x+r•v)) 0 t := by
    have he : deriv (fun r : ℝ => x+r•v) = fun _ => v := funext (fun r => (hv r).deriv)
    rw [he]
    exact hasDerivAt_const t v
  simpa only [Function.comp_def,map_zero,add_zero] using
    SecondCurveChain.second hf (by fun_prop) (hv t) ha

 theorem second_segment {f : E → ℝ} (x v : E)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x+t•v)) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      f (x+v)-f x-fderiv ℝ f x v =
        fderiv ℝ (fderiv ℝ f) (x+t•v) v v / 2 := by
  let g : ℝ → ℝ := fun t => f (x+t•v)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 2 g t :=
    (hf t ht).comp t (by fun_prop)
  have hgOn : ContDiffOn ℝ (1+1 : ℕ) g (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun t ht => (hg t ht).contDiffWithinAt
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    (by norm_num : (0 : ℝ) ≠ 1) hgOn
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using ht
  have hD : derivWithin g (uIcc (0 : ℝ) 1) 0 = fderiv ℝ f x v := by
    have hfx : ContDiffAt ℝ 2 f x := by simpa using hf 0 (by simp)
    have hfx' : HasFDerivAt f (fderiv ℝ f x) (x+(0 : ℝ)•v) := by simpa using (hfx.differentiableAt (by norm_num)).hasFDerivAt
    have hd := hfx'.comp_hasDerivAt 0
      (show HasDerivAt (fun r : ℝ => x+r•v) v 0 by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x)
    have hd' : HasDerivAt g (fderiv ℝ f x v) 0 := by simpa only [g,Function.comp_def] using hd
    exact hd'.hasDerivWithinAt.derivWithin (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1) 0 (by simp))
  have h2 : iteratedDeriv 2 g t = fderiv ℝ (fderiv ℝ f) (x+t•v) v v := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def,g] using
      line_second_at x v t (hf t ⟨ht'.1.le,ht'.2.le⟩)
  refine ⟨t,ht',?_⟩
  simp only [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_succ,
    iteratedDerivWithin_zero] at he
  rw [hD] at he
  norm_num only [Nat.factorial_one,Nat.cast_one,inv_one,sub_zero,one_pow,one_mul,
    one_smul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_ofNat] at he
  rw [h2,mul_one] at he
  simpa only [g,one_smul,zero_smul,add_zero,sub_add_eq_sub_sub] using he
end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_MovingTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem tendsto_clm_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {g : α → E}
    {L : E →L[ℝ] F} {v : E} (hf : Tendsto f l (𝓝 L)) (hg : Tendsto g l (𝓝 v)) :
    Tendsto (fun a => f a (g a)) l (𝓝 (L v)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.continuousAt.tendsto.comp (hf.prodMk_nhds hg)

 theorem segment_norm_bound (_ : E) (v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖t•v‖ ≤ ‖v‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

 theorem moving_segment_tendsto {x v : ℕ → E} {a : E}
    (hx : Tendsto x atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 0))
    {t : ℕ → ℝ} (ht : ∀ᶠ j in atTop, t j ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun j => x j+t j•v j) atTop (𝓝 a) := by
  have hzero : Tendsto (fun j => t j•v j) atTop (𝓝 (0 : E)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (ht.mono (fun j hj => segment_norm_bound (x j) (v j) hj))
    simpa using hv.norm
  simpa using hx.add hzero

 theorem moving_segment_smooth {f : E → ℝ} {a : E} (hf : ContDiffAt ℝ ∞ f a)
    {x v : ℕ → E} (hx : Tendsto x atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x j+t•v j) := by
  have hnear : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ 2 f z :=
    (hf.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall : ∀ᶠ j in atTop, ‖x j-a‖+‖v j‖ < ε := by
    apply (tendsto_order.mp ((hx.sub tendsto_const_nhds).norm.add hv.norm)).2 ε
    simpa using hε
  filter_upwards [hsmall] with j hj t ht
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  change ‖x j+t•v j-a‖ < ε
  calc
    _ = ‖(x j-a)+t•v j‖ := by congr 1; abel
    _ ≤ ‖x j-a‖+‖t•v j‖ := norm_add_le _ _
    _ ≤ ‖x j-a‖+‖v j‖ := add_le_add (le_refl _) (segment_norm_bound (x j) (v j) ht)
    _ < ε := hj

 theorem second_limit {f : E → ℝ} {a e : E} (hf : ContDiffAt ℝ ∞ f a)
    {x d : ℕ → E} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j)-f (x j)-fderiv ℝ f (x j) (l j•d j))/(l j)^2)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) a e e / 2)) := by
  classical
  have hv : Tendsto (fun j => l j•d j) atTop (𝓝 (0 : E)) := by simpa using hl.smul hd
  have hsm := moving_segment_smooth hf hx hv
  let P (j : ℕ) (t : ℝ) : Prop := t ∈ Ioo (0 : ℝ) 1 ∧
    f (x j+l j•d j)-f (x j)-fderiv ℝ f (x j) (l j•d j) =
      fderiv ℝ (fderiv ℝ f) (x j+t•(l j•d j)) (l j•d j) (l j•d j) / 2
  have hex : ∀ᶠ j in atTop, ∃ t, P j t := hsm.mono (fun j hj => second_segment (x j) (l j•d j) hj)
  let t (j : ℕ) : ℝ := if H : ∃ t, P j t then Classical.choose H else 0
  have ht : ∀ᶠ j in atTop, P j (t j) := hex.mono (fun j hj => by
    dsimp only [t]
    rw [dite_eq_left hj]
    exact Classical.choose_spec hj)
  have hpoint := moving_segment_tendsto hx hv (ht.mono (fun j hj => ⟨hj.1.1.le,hj.1.2.le⟩))
  have hH : ContinuousAt (fderiv ℝ (fderiv ℝ f)) a :=
    ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuousAt
  have hlim := (tendsto_clm_apply (tendsto_clm_apply (hH.tendsto.comp hpoint) hd) hd).div_const 2
  apply hlim.congr'
  filter_upwards [ht,hlne] with j hj hlj
  rw [hj.2]
  simp only [map_smul,smul_apply,smul_eq_mul,Function.comp_def]
  field_simp [hlj]

 theorem first_limit {f : E → ℝ} {a e : E} (hf : ContDiffAt ℝ ∞ f a)
    {x d : ℕ → E} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j)-f (x j))/l j)
      atTop (𝓝 (fderiv ℝ f a e)) := by
  have h2 := second_limit hf hx hd hl hlne
  have hD := tendsto_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).continuousAt.tendsto.comp hx) hd
  have hh := (h2.mul hl).add hD
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [hlne] with j hj
  simp only [map_smul,smul_eq_mul,Function.comp_def]
  field_simp [hj]
  ring

end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_ParametricTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem param_first_limit {f : E × F → ℝ} {a e : E} {b : F}
    (hf : ContDiffAt ℝ ∞ f (a,b))
    {x d : ℕ → E} {q : ℕ → F} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hq : Tendsto q atTop (𝓝 b))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j,q j)-f (x j,q j))/l j)
      atTop (𝓝 (fderiv ℝ f (a,b) (e,0))) := by
  simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using
    first_limit hf (hx.prodMk_nhds hq) (hd.prodMk_nhds (tendsto_const_nhds (x := (0 : F)))) hl hlne

 theorem param_second_limit {f : E × F → ℝ} {a e : E} {b : F}
    (hf : ContDiffAt ℝ ∞ f (a,b))
    {x d : ℕ → E} {q : ℕ → F} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hq : Tendsto q atTop (𝓝 b))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j,q j)-f (x j,q j)-
        l j*fderiv ℝ f (x j,q j) (d j,0))/(l j)^2)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) (a,b) (e,0) (e,0) / 2)) := by
  have hscale (j : ℕ) : fderiv ℝ f (x j,q j) (l j•d j,0) =
      l j*fderiv ℝ f (x j,q j) (d j,0) := by
    simpa only [Prod.smul_mk,smul_zero,smul_eq_mul] using
      (fderiv ℝ f (x j,q j)).map_smul (l j) (d j,0)
  simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero,hscale] using
    second_limit hf (hx.prodMk_nhds hq) (hd.prodMk_nhds (tendsto_const_nhds (x := (0 : F)))) hl hlne
end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CollisionCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E F P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι]

 theorem collision_limits {B : E × F → ℝ} {C : ι → E × P → ℝ}
    {x₀ e : E} {y₀ : F} {a₀ : ι → P} {β₀ : ℝ} {θ₀ : ι → ℝ}
    (hB : ContDiffAt ℝ ∞ B (x₀,y₀)) (hC : ∀ i, ContDiffAt ℝ ∞ (C i) (x₀,a₀ i))
    {x d : ℕ → E} {y : ℕ → F} {a : ℕ → ι → P} {β l : ℕ → ℝ} {θ : ℕ → ι → ℝ}
    (hx : Tendsto x atTop (𝓝 x₀)) (hd : Tendsto d atTop (𝓝 e))
    (hy : Tendsto y atTop (𝓝 y₀)) (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (a₀ i)))
    (hβ : Tendsto β atTop (𝓝 β₀)) (hθ : ∀ i, Tendsto (fun j => θ j i) atTop (𝓝 (θ₀ i)))
    (hl : Tendsto l atTop (𝓝 0)) (hlpos : ∀ᶠ j in atTop, 0 < l j)
    (hθpos : ∀ᶠ j in atTop, ∀ i, 0 ≤ θ j i)
    (hineq : ∀ᶠ j in atTop, ∀ i,
      B (x j+l j•d j,y j)-B (x j,y j) -
      β j*(C i (x j+l j•d j,a j i)-C i (x j,a j i)) ≤ 0)
    (hcancel : ∀ᶠ j in atTop, ∑ i, θ j i *
      (fderiv ℝ B (x j,y j) (d j,0)-β j*fderiv ℝ (C i) (x j,a j i) (d j,0)) = 0) :
    (∀ i, fderiv ℝ B (x₀,y₀) (e,0)-β₀*fderiv ℝ (C i) (x₀,a₀ i) (e,0) ≤ 0) ∧
    (∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) -
      β₀*fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0)) ≤ 0) := by
  have hlne := hlpos.mono (fun _ hj => hj.ne')
  constructor
  · intro i
    have hlim := (param_first_limit hB hx hd hy hl hlne).sub
      (hβ.mul (param_first_limit (hC i) hx hd (ha i) hl hlne))
    apply le_of_tendsto hlim
    filter_upwards [hlpos,hineq] with j hj hji
    have hh := div_nonpos_of_nonpos_of_nonneg (hji i) hj.le
    convert hh using 1
    ring
  · have hlimB := param_second_limit hB hx hd hy hl hlne
    have hlimC (i : ι) := param_second_limit (hC i) hx hd (ha i) hl hlne
    have hlim := tendsto_finsetSum Finset.univ (fun i _ => (hθ i).mul (hlimB.sub (hβ.mul (hlimC i))))
    have hle : ∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) / 2 -
        β₀*(fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0) / 2)) ≤ 0 := by
      apply le_of_tendsto hlim
      filter_upwards [hlpos,hθpos,hineq,hcancel] with j hj hjθ hji hjc
      let DB := fderiv ℝ B (x j,y j) (d j,0)
      let DC := fun i => fderiv ℝ (C i) (x j,a j i) (d j,0)
      let VB := B (x j+l j•d j,y j)-B (x j,y j)
      let VC := fun i => C i (x j+l j•d j,a j i)-C i (x j,a j i)
      change ∑ i, θ j i*((VB-l j*DB)/(l j)^2-β j*((VC i-l j*DC i)/(l j)^2)) ≤ 0
      have heq : (∑ i, θ j i*((VB-l j*DB)/(l j)^2-β j*((VC i-l j*DC i)/(l j)^2))) =
          ((∑ i, θ j i*(VB-β j*VC i))-l j*(∑ i, θ j i*(DB-β j*DC i)))/(l j)^2 := by
        rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [heq,hjc,mul_zero,sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hjθ i) (hji i))) (sq_nonneg _)
    have heq : (∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) / 2 -
        β₀*(fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0) / 2))) =
        (∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) -
        β₀*fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0))) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq] at hle
    linarith
end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CollisionGeometry
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

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem bundle_base_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) : Tendsto (fun j => (p j).1) atTop (𝓝 p₀.1) :=
  (FiberBundle.continuous_proj (Model n) (TangentSpace (model n))).continuousAt.tendsto.comp hp

 theorem bundle_endpoint_limit {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => exp (p j).1 (p j).2) atTop (𝓝 (exp p₀.1 p₀.2)) :=
  exp_total_smooth.continuous.continuousAt.tendsto.comp hp

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_NormalizedSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology
namespace MovingTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem separation_scale_limit {x q : ℕ → E} {x₀ : E}
    (hx : Tendsto x atTop (𝓝 x₀)) (hq : Tendsto q atTop (𝓝 x₀)) :
    Tendsto (fun j => ‖q j-x j‖) atTop (𝓝 0) := by
  simpa only [sub_self,norm_zero] using (hq.sub hx).norm

omit [FiniteDimensional ℝ E] in
 theorem separation_identity (x q : E) : x+‖q-x‖•NormedSpace.normalize (q-x) = q := by
  rw [NormedSpace.norm_smul_normalize,add_sub_cancel]

end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_BranchCollisionLimits
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
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem branch_collision_limits_oai (y : ι → M) (h : ι → ℝ)
    {p q : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto (fun j => (q j).1) atTop (𝓝 p₀.1))
    {sⱼ : ℕ → ℝ} {s ℓ : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
    (hqp : Tendsto (fun j => mulState (sⱼ j) (q j)) atTop (𝓝 (mulState s p₀)))
    (hpos : ∀ᶠ j in atTop, 0 < sⱼ j) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hcollision : ∀ᶠ j in atTop, exp (p j).1 (sⱼ j•(p j).2) = exp (q j).1 (sⱼ j•(q j).2))
    (hvalue : ∀ᶠ j in atTop, scaledPoleValue y h (sⱼ j) (q j) ≤ scaledPoleValue y h (sⱼ j) (p j))
    (R : ∀ j, ActiveRepresentation y h (p j)) (R₀ : ActiveRepresentation y h p₀)
    (hθ : ∀ i, Tendsto (fun j => (R j).θ i) atTop (𝓝 (R₀.θ i)))
    (ha : ∀ i, Tendsto (fun j => (⟨(p j).1,(R j).a i⟩ : TangentBundle (model n) M))
      atTop (𝓝 ⟨p₀.1,R₀.a i⟩))
    (B : ActionBranch (n := n) p₀.1 (exp p₀.1 (s•p₀.2)))
    (hB : stateChart p₀.1 (mulState s p₀) ∈ B.coord.source)
    (C : ∀ i, ActionBranch (n := n) p₀.1 (exp p₀.1 (ℓ•R₀.a i)))
    (hC : ∀ i, stateChart p₀.1 (⟨p₀.1,ℓ•R₀.a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    {e : Model n}
    (hd : Tendsto (fun j => NormedSpace.normalize
      (chartAt (Model n) p₀.1 (q j).1 - chartAt (Model n) p₀.1 (p j).1)) atTop (𝓝 e))
    (hne : ∀ᶠ j in atTop, chartAt (Model n) p₀.1 (q j).1 ≠ chartAt (Model n) p₀.1 (p j).1) :
    (∀ i, fderiv ℝ B.value (chartAt (Model n) p₀.1 p₀.1,
        chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2))) (e,0) -
      (s/ℓ)*fderiv ℝ (C i).value (chartAt (Model n) p₀.1 p₀.1,
        chartAt (Model n) (exp p₀.1 (ℓ•R₀.a i)) (exp p₀.1 (ℓ•R₀.a i))) (e,0) ≤ 0) ∧
    (∑ i, R₀.θ i*(fderiv ℝ (fderiv ℝ B.value)
      (chartAt (Model n) p₀.1 p₀.1,chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2))) (e,0) (e,0) -
      (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
        (chartAt (Model n) p₀.1 p₀.1,chartAt (Model n) (exp p₀.1 (ℓ•R₀.a i)) (exp p₀.1 (ℓ•R₀.a i))) (e,0) (e,0))) ≤ 0 := by
  let x := p₀.1
  let z := exp p₀.1 (s•p₀.2)
  let w := fun i => exp p₀.1 (ℓ•R₀.a i)
  let xp := fun j => chartAt (Model n) x (p j).1
  let xq := fun j => chartAt (Model n) x (q j).1
  let yp := fun j => chartAt (Model n) z (exp (p j).1 (sⱼ j•(p j).2))
  let ap := fun j i => chartAt (Model n) (w i) (exp (p j).1 (ℓ•(R j).a i))
  have hpS : mulState s p₀ ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hpp := tangentScale_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hp)
  have hBp := B.eventually_source hpp hpS hB
  have hBq := B.eventually_source hqp hpS hB
  have hpa (i : ActiveIndex n) : Tendsto
      (fun j => (⟨(p j).1,ℓ•(R j).a i⟩ : TangentBundle (model n) M)) atTop
      (𝓝 (⟨x,ℓ•R₀.a i⟩ : TangentBundle (model n) M)) :=
    tangentScale_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds (ha i))
  have hCy (i : ActiveIndex n) := bundle_endpoint_limit (hpa i)
  have hCi (i : ActiveIndex n) : ℓ•R₀.a i ∈ injectivityDomain x :=
    strict_radial_mem_injectivity (R₀.active i).1 hℓ.le hℓ₁
  have hCp := eventually_all.mpr (fun i => (C i).eventually_source (hpa i)
    ((stateChart_source x _).mpr (mem_chart_source (Model n) x)) (hC i))
  have hCpV := eventually_all.mpr (fun i => (C i).eq_cost_along (hCi i) (hC i)
    (bundle_base_limit hp) (hCy i) (mem_chart_source (Model n) (w i)))
  have hCqV := eventually_all.mpr (fun i => (C i).eq_cost_along (hCi i) (hC i)
    hq (hCy i) (mem_chart_source (Model n) (w i)))
  have hxp : Tendsto xp atTop (𝓝 (chartAt (Model n) x x)) := base_chart_limit hp
  have hxq : Tendsto xq atTop (𝓝 (chartAt (Model n) x x)) :=
    ((chartAt (Model n) x).continuousAt (mem_chart_source (Model n) x)).tendsto.comp hq
  have hyp : Tendsto yp atTop (𝓝 (chartAt (Model n) z z)) := scaled_endpoint_chart_limit hp hs
  have hap (i : ActiveIndex n) : Tendsto (fun j => ap j i) atTop (𝓝 (chartAt (Model n) (w i) (w i))) :=
    ((chartAt (Model n) (w i)).continuousAt (mem_chart_source (Model n) (w i))).tendsto.comp (hCy i)
  have hBt := B.smooth_value.contDiffAt (B.coord.open_target.mem_nhds (B.target_state _ hpS hB))
  have hCt (i : ActiveIndex n) : ContDiffAt ℝ ∞ (C i).value
      (chartAt (Model n) x x,chartAt (Model n) (w i) (w i)) := by
    have hAiS : (⟨x,ℓ•R₀.a i⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
      (stateChart_source x _).mpr (mem_chart_source (Model n) x)
    exact (C i).smooth_value.contDiffAt ((C i).coord.open_target.mem_nhds
      ((C i).target_state (⟨x,ℓ•R₀.a i⟩ : TangentBundle (model n) M) hAiS (hC i)))
  apply MovingTaylor.collision_limits hBt hCt hxp hd hyp hap (hs.div_const ℓ) hθ
    (MovingTaylor.separation_scale_limit hxp hxq)
  · filter_upwards [hne] with j hj
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hj)
  · exact Filter.Eventually.of_forall (fun j => (R j).nonneg)
  · filter_upwards [hBp,hBq,hpos,hcollision,hvalue,hCpV,hCqV] with j hjp hjq hjs hje hjv hjCp hjCq
    intro i
    rw [MovingTaylor.separation_identity]
    exact branch_support_inequality y h hjs.le hℓ hℓ₁ ((R j).active i) B (C i)
      hjp.1 hjq.1 hjp.2 hjq.2 hje hjv (hjCp i) (hjCq i)
  · filter_upwards [hBp,hCp] with j hjp hjC
    exact branch_gradient_weighted (R j).a (R j).θ (R j).sum_one (R j).bary hℓ.ne'
      ((stateChart_source x _).mp hjp.1) B hjp.2 w C (fun i => (hjC i).2) _

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits_oai.{u_1, u_2} := @OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits_oai.{u_1, u_2}
