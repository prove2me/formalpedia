-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.convexHull_nonconjugate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:02:36.73167+00:00
-- url     : https://prove2.me/submissions/222a300e-a7cf-4f4f-81c8-902a8455e566

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actionHessianDiag_smooth
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actual_focal_trial_pole
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_fibre_kernel_perp_radial
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_initialCost_geometry
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_nonconjugate_inward_hessian_bound

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

 theorem metric_chart_pair (x y : M) (hy : y ∈ (chartAt E x).source)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    metric x (chartAt E x y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y w) = inner ℝ v w := by
  have hv := congrArg (fun p : TangentBundle 𝓘(ℝ, E) E => p.2)
    (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M))
      (q := (⟨y,v⟩ : TangentBundle 𝓘(ℝ, E) M)) hy)
  have hw := congrArg (fun p : TangentBundle 𝓘(ℝ, E) E => p.2)
    (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M))
      (q := (⟨y,w⟩ : TangentBundle 𝓘(ℝ, E) M)) hy)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y v = (stateChart x ⟨y,v⟩).2 at hv
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y w = (stateChart x ⟨y,w⟩).2 at hw
  rw [hv,hw,stateChart_pairing x y hy]

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
-- module Solutions.OAIQW_WeakMTW.Support_FirstCutSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology

namespace FirstCut

theorem incompatible_pole_bounds {a : ℝ → ℝ → ℝ} {B C c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hlo : ∀ s, 0 < s → s < δ → -B * s ≤ s ^ 2 * a s (s ^ 4))
    (hup : ∀ s, 0 < s → s < δ →
      a s (s ^ 4) ≤ C - c / (s ^ 2 + s ^ 4)) : False := by
  let P : ℝ → ℝ := fun s => (C * s ^ 2 + B * s) * (1 + s ^ 2)
  have hlim : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous P := by dsimp [P]; fun_prop
    convert hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [P]
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c ≤ P s := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    have hs0 : 0 < s := hs.1
    have hsq : 0 < s ^ 2 := sq_pos_of_pos hs0
    have hden : 0 < s ^ 2 + s ^ 4 := by positivity
    have hlo' := hlo s hs0 hs.2
    have hup' := (div_le_iff₀ hden).mp (show c / (s ^ 2 + s ^ 4) ≤
        C - a s (s ^ 4) by linarith [hup s hs0 hs.2])
    have hprod := mul_le_mul_of_nonneg_right hlo' (show 0 ≤ 1 + s ^ 2 by positivity)
    dsimp [P]
    nlinarith
  have hc0 : c ≤ 0 := ge_of_tendsto hlim hev
  exact (not_le_of_gt hc) hc0

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_hessian_identity (A : LinearMap.BilinForm ℝ E)
    (hsymm : ∀ v w, A v w = A w v) {p e : E} {s : ℝ}
    (hpe : inner ℝ p e = 0) (hee : inner ℝ e e = 1)
    (hrad : ∀ v, A (p + s • e) v = inner ℝ (p + s • e) v) :
    A p p = inner ℝ p p + s ^ 2 * (A e e - 1) := by
  have h₁ := hrad p
  have h₂ := hrad e
  have hep : inner ℝ e p = 0 := by rw [real_inner_comm, hpe]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    inner_add_left, real_inner_smul_left, hep, hpe, hee, mul_zero, add_zero,
    zero_add, mul_one] at h₁ h₂
  rw [hsymm e p] at h₁
  nlinarith [congrArg (fun t : ℝ => s * t) h₂]

end InnerProduct

theorem concave_linear_lower {f : ℝ → ℝ} {b s K L : ℝ}
    (hb : 0 < b) (hf : ConcaveOn ℝ (Icc 0 b) f)
    (hzero : f 0 = K) (hend : -L ≤ f b) (hs : s ∈ Icc 0 b) :
    K - ((K + L) / b) * s ≤ f s := by
  have hratio : 0 ≤ s / b := div_nonneg hs.1 hb.le
  have hratio1 : s / b ≤ 1 := (div_le_one hb).mpr hs.2
  have hcomb := hf.2 (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.le⟩)
    (show b ∈ Icc 0 b from ⟨hb.le, le_rfl⟩)
    (sub_nonneg.mpr hratio1) hratio (show (1 - s / b) + s / b = 1 by ring)
  have harg : (1 - s / b) • (0 : ℝ) + (s / b) • b = s := by
    simp [smul_eq_mul, ne_of_gt hb]
  rw [harg, hzero] at hcomb
  simp only [smul_eq_mul] at hcomb
  have hmul := mul_le_mul_of_nonneg_left hend hratio
  have hid : K - (K + L) / b * s = (1 - s / b) * K + (s / b) * (-L) := by
    ring
  rw [hid]
  linarith

theorem incompatible_transverse_pole {f : ℝ → ℝ} {L C c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hlo : ∀ h, 0 < h → h < δ → L ≤ f h)
    (hup : ∀ h, 0 < h → h < δ → f h ≤ C - c / h) : False := by
  have hlim : Tendsto (fun h : ℝ => (C - L) * h) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => (C - L) * h) (𝓝[>] 0) (𝓝 ((C - L) * 0)))
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), c ≤ (C - L) * h := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    have h₁ := hlo h hh.1 hh.2
    have h₂ := (div_le_iff₀ hh.1).mp
      (show c / h ≤ C - f h by linarith [hup h hh.1 hh.2])
    have h₃ := mul_le_mul_of_nonneg_right (show C - f h ≤ C - L by linarith) hh.1.le
    exact h₂.trans h₃
  exact (not_le_of_gt hc) (ge_of_tendsto hlim hev)

section Segment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem transverse_pairing_zero
    {A : ℝ → ℝ → LinearMap.BilinForm ℝ E} {a b : ℝ} {e k : E}
    (ha : 0 < a) (hb : 0 < b)
    (hconc : ∀ h, 0 < h → h < 1 → ∀ ξ : E, inner ℝ ξ e = 0 →
      ConcaveOn ℝ (Icc (-a) b) (fun s => A h s ξ ξ))
    (hends : ∀ ξ : E, ∃ L δ : ℝ, 0 < δ ∧
      ∀ h, 0 < h → h < δ → -L ≤ A h (-a) ξ ξ ∧ -L ≤ A h b ξ ξ)
    (htrial : ∀ ξ : E, inner ℝ ξ k ≠ 0 → HasTrialPole A ξ)
    {ξ : E} (hξ : inner ℝ ξ e = 0) : inner ℝ ξ k = 0 := by
  by_contra hne
  obtain ⟨C, c, δ₁, hc, hδ₁, hpole⟩ := htrial ξ hne
  obtain ⟨L, δ₂, hδ₂, hends'⟩ := hends ξ
  let δ := min δ₁ (min δ₂ 1)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ zero_lt_one)
  apply incompatible_transverse_pole hc hδ
    (f := fun h => A h 0 ξ ξ) (L := -L) (C := C)
  · intro h hh hhδ
    have hhδ₂ : h < δ₂ := lt_of_lt_of_le hhδ ((min_le_right _ _).trans (min_le_left _ _))
    have hh1 : h < 1 := lt_of_lt_of_le hhδ ((min_le_right _ _).trans (min_le_right _ _))
    have hab : -a ≤ b := by linarith
    have hc' := (hconc h hh hh1 ξ hξ).ge_on_segment
      (show -a ∈ Icc (-a) b from ⟨le_rfl, hab⟩)
      (show b ∈ Icc (-a) b from ⟨hab, le_rfl⟩)
      (show (0 : ℝ) ∈ segment ℝ (-a) b by
        rw [segment_eq_Icc hab]; exact ⟨by linarith, hb.le⟩)
    have hend' := hends' h hh hhδ₂
    exact (le_min hend'.1 hend'.2).trans hc'
  · intro h hh hhδ
    have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_left _ _)
    simpa using hpole h hh hhδ₁ 0 (by simpa using hδ₁)

theorem parallel_of_transverse_pairing_zero {e k : E}
    (he : inner ℝ e e = 1)
    (h : ∀ ξ : E, inner ℝ ξ e = 0 → inner ℝ ξ k = 0) :
    k = (inner ℝ e k) • e := by
  let q := k - (inner ℝ e k) • e
  have hqe : inner ℝ q e = 0 := by
    dsimp [q]
    rw [inner_sub_left, real_inner_smul_left, he, mul_one, real_inner_comm k e]
    exact sub_self _
  have hqk : inner ℝ q k = 0 := h q hqe
  have hqq : inner ℝ q q = 0 := by
    conv_rhs => rw [← sub_self (0 : ℝ)]
    dsimp [q] at ⊢
    rw [inner_sub_right, inner_smul_right]
    change inner ℝ q k - inner ℝ e k * inner ℝ q e = 0 - 0
    rw [hqk, hqe, mul_zero]
  have hqzero : q = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hqq
  exact sub_eq_zero.mp hqzero

theorem no_first_cut_kernel
    {A : ℝ → ℝ → LinearMap.BilinForm ℝ E} {a b : ℝ} {p e k : E}
    (ha : 0 < a) (hb : 0 < b) (he : inner ℝ e e = 1)
    (hkp : inner ℝ k p = 0)
    (hsymm : ∀ h, 0 < h → h < 1 → ∀ s ∈ Icc (-a) b,
      ∀ v w, A h s v w = A h s w v)
    (hrad : ∀ h, 0 < h → h < 1 → ∀ s ∈ Icc (-a) b,
      ∀ v, A h s (p + s • e) v = inner ℝ (p + s • e) v)
    (hconc : ∀ h, 0 < h → h < 1 → ∀ ξ : E, inner ℝ ξ e = 0 →
      ConcaveOn ℝ (Icc (-a) b) (fun s => A h s ξ ξ))
    (hends : ∀ ξ : E, ∃ L δ : ℝ, 0 < δ ∧
      ∀ h, 0 < h → h < δ → -L ≤ A h (-a) ξ ξ ∧ -L ≤ A h b ξ ξ)
    (htrial : ∀ ξ : E, inner ℝ ξ k ≠ 0 → HasTrialPole A ξ) : k = 0 := by
  by_contra hk
  have hpar : k = (inner ℝ e k) • e :=
    parallel_of_transverse_pairing_zero he
      (fun ξ hξ => transverse_pairing_zero ha hb hconc hends htrial hξ)
  have hα : inner ℝ e k ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hpar
    exact hk hpar
  have hpe : inner ℝ p e = 0 := by
    have hkp' := hkp
    rw [hpar, real_inner_smul_left] at hkp'
    rw [real_inner_comm]
    exact (mul_eq_zero.mp hkp').resolve_left hα
  obtain ⟨C, c, δ₁, hc, hδ₁, hpole⟩ := htrial e hα
  obtain ⟨L, δ₂, hδ₂, hends'⟩ := hends p
  let δ := min δ₁ (min δ₂ (min b 1))
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ (lt_min hb zero_lt_one))
  have hδ₁' : δ ≤ δ₁ := min_le_left _ _
  have hδ₂' : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ b := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hs4 : ∀ s : ℝ, 0 < s → s < δ → 0 < s ^ 4 ∧ s ^ 4 ≤ s := by
    intro s hs hsδ
    refine ⟨pow_pos hs 4, ?_⟩
    have hs1 : s ≤ 1 := (hsδ.trans_le hδ1).le
    have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs.le hs1
    calc
      s ^ 4 = s ^ 3 * s := by ring
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right hs3 hs.le
      _ = s := one_mul s
  apply incompatible_pole_bounds (a := fun s h => A h s e e)
    (B := (inner ℝ p p + L) / b) (C := C) hc hδ
  · intro s hs hsδ
    obtain ⟨hs4pos, hs4le⟩ := hs4 s hs hsδ
    have hs41 : s ^ 4 < 1 := hs4le.trans_lt (hsδ.trans_le hδ1)
    have hs4δ₂ : s ^ 4 < δ₂ := hs4le.trans_lt (hsδ.trans_le hδ₂')
    have hsmem : s ∈ Icc (-a) b := ⟨by linarith, (hsδ.trans_le hδb).le⟩
    have h0mem : (0 : ℝ) ∈ Icc (-a) b := ⟨by linarith, hb.le⟩
    have hf : ConcaveOn ℝ (Icc 0 b) (fun s' => A (s ^ 4) s' p p) :=
      (hconc (s ^ 4) hs4pos hs41 p hpe).subset
        (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩) (convex_Icc 0 b)
    have hzero : A (s ^ 4) 0 p p = inner ℝ p p := by
      simpa using hrad (s ^ 4) hs4pos hs41 0 h0mem p
    have hlinear := concave_linear_lower hb hf hzero
      (hends' (s ^ 4) hs4pos hs4δ₂).2
      (show s ∈ Icc 0 b from ⟨hs.le, hsmem.2⟩)
    have hid := radial_hessian_identity (A (s ^ 4) s)
      (hsymm (s ^ 4) hs4pos hs41 s hsmem) hpe he
      (hrad (s ^ 4) hs4pos hs41 s hsmem)
    rw [hid] at hlinear
    nlinarith [sq_nonneg s]
  · intro s hs hsδ
    obtain ⟨hs4pos, hs4le⟩ := hs4 s hs hsδ
    apply hpole (s ^ 4) hs4pos (hs4le.trans_lt (hsδ.trans_le hδ₁')) s
    rw [abs_of_pos hs]
    exact hsδ.trans_le hδ₁'

end Segment

end FirstCut

open Set Filter
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

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

 omit [FiniteDimensional ℝ E] in
 theorem actionForm_symmetric (G : E → MetricTensor E) (f : E → ℝ)
    {S : Set E} (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ r ∈ S, ∀ v w, G r v w = G r w v)
    {a : E} (ha : a ∈ S) (hf : ContDiffAt ℝ 2 f a) (ν v w : E) :
    actionForm G f a ν v w = actionForm G f a ν w v := by
  change _ + lowerChristoffel (fderiv ℝ G a) v w ν =
    _ + lowerChristoffel (fderiv ℝ G a) w v ν
  rw [(hf.isSymmSndFDerivAt (by norm_num)).eq v w]
  simp only [lowerChristoffel_apply,derivative_metric_symmetric hS hG hsym ha ν v w]
  ring

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

 theorem actionHessian_symmetric (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ η : TangentSpace (model n) x) :
    actionHessian x v ξ η = actionHessian x v η ξ := by
  exact actionForm_symmetric (metric x) (initialCost x (exp x v)) (chartAt (Model n) x).open_target
    ((metric_smooth x).differentiableOn (by simp)) (fun a _ => metric_symmetric x a)
    ((chartAt (Model n) x).map_source (mem_chart_source (Model n) x))
    ((initialCost_geometry x hv).1.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top))
    (tangentChartLinear x v) (tangentChartLinear x ξ) (tangentChartLinear x η)

 theorem actionHessian_radial (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    actionHessian x v ξ v = inner ℝ ξ v := by
  change actionForm _ _ _ _ (tangentChartLinear x ξ) (tangentChartLinear x v) = _
  rw [(initialCost_geometry x hv).2.2]
  exact metric_chart_pair x x (mem_chart_source (Model n) x) ξ v

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
-- module Solutions.OAIQW_WeakMTW.Variations_GeometricFirstCut
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

 theorem nonconjugate_middle_of_unit_segment (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {p e : TangentSpace (model n) x} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : inner ℝ e e = 1)
    (hseg : ∀ s ∈ Icc (-a) b, p+s•e ∈ minimizingDomain x)
    (hleft : Nonconjugate x (p+(-a)•e)) (hright : Nonconjugate x (p+b•e)) :
    Nonconjugate x p := by
  unfold Nonconjugate
  rw [injective_iff_map_eq_zero]
  intro k hk
  let A : ℝ → ℝ → LinearMap.BilinForm ℝ (TangentSpace (model n) x) :=
    fun h s => actionHessian x ((1-h)•(p+s•e))
  have hI (h : ℝ) (hh : 0 < h) (hh₁ : h < 1) (s : ℝ) (hs : s ∈ Icc (-a) b) :
      (1-h)•(p+s•e) ∈ injectivityDomain x :=
    strict_radial_mem_injectivity (hseg s hs) (by linarith) (by linarith)
  apply FirstCut.no_first_cut_kernel (A := A) ha hb he
    (fibre_kernel_perp_radial x (exp x p) (mem_chart_source (Model n) (exp x p)) hk)
  · intro h hh hh₁ s hs v w
    exact actionHessian_symmetric x (hI h hh hh₁ s hs) v w
  · intro h hh hh₁ s hs v
    have hrad := actionHessian_radial x (hI h hh hh₁ s hs) v
    rw [LinearMap.BilinForm.smul_right,inner_smul_right] at hrad
    have hne : (1-h) ≠ 0 := ne_of_gt (by linarith)
    have hr := mul_left_cancel₀ hne hrad
    change actionHessian x ((1-h)•(p+s•e)) (p+s•e) v = _
    rw [actionHessian_symmetric x (hI h hh hh₁ s hs)]
    exact hr.trans (real_inner_comm v (p+s•e)).symm
  · intro h hh hh₁ ξ hξ
    have hξη : inner ℝ ξ ((1-h)•e) = 0 := by rw [inner_smul_right,hξ,mul_zero]
    have hid (s : ℝ) : (1-h)•p+s•((1-h)•e) = (1-h)•(p+s•e) := by
      rw [smul_add,smul_smul,smul_smul,mul_comm s (1-h)]
    have hc := transverse_action_concave hMTW x ((1-h)•p) ξ ((1-h)•e) hξη
      (convex_Icc (-a) b) (fun s hs => (hid s).symm ▸ hI h hh hh₁ s hs)
    apply hc.congr
    intro s hs
    change actionHessianDiag x ((1-h)•p+s•((1-h)•e)) ξ =
      actionHessian x ((1-h)•(p+s•e)) ξ ξ
    rw [hid s,← actionHessian_diag x (hI h hh hh₁ s hs)]
  · intro ξ
    have hab : -a ≤ b := by linarith
    obtain ⟨L₀,δ₀,hδ₀,h₀⟩ := nonconjugate_inward_hessian_bound x (hseg (-a) ⟨le_rfl,hab⟩) hleft ξ
    obtain ⟨L₁,δ₁,hδ₁,h₁⟩ := nonconjugate_inward_hessian_bound x (hseg b ⟨hab,le_rfl⟩) hright ξ
    refine ⟨max L₀ L₁,min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
    intro h hh hhδ
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans (h₀ h hh (lt_of_lt_of_le hhδ (min_le_left _ _)))
    · exact (neg_le_neg (le_max_right _ _)).trans (h₁ h hh (lt_of_lt_of_le hhδ (min_le_right _ _)))
  · intro ξ hξ
    exact actual_focal_trial_pole x ha hb hseg hk ξ hξ

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_SegmentNonconjugacy
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

 theorem segment_nonconjugacy (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {v₀ v₁ : TangentSpace (model n) x}
    (hseg : segment ℝ v₀ v₁ ⊆ minimizingDomain x)
    (h₀ : Nonconjugate x v₀) (h₁ : Nonconjugate x v₁) :
    ∀ w ∈ segment ℝ v₀ v₁, Nonconjugate x w := by
  intro w hw
  by_cases hv : v₀ = v₁
  · subst v₁
    have : w = v₀ := by simpa only [segment_same,mem_singleton_iff] using hw
    exact this ▸ h₀
  rw [segment_eq_image'] at hw
  obtain ⟨t,ht,rfl⟩ := hw
  by_cases ht₀ : t = 0
  · simpa only [ht₀,zero_smul,add_zero] using h₀
  by_cases ht₁ : t = 1
  · simpa only [ht₁,one_smul,add_sub_cancel] using h₁
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht₀)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht₁
  let d := v₁-v₀
  let l := ‖d‖
  let p := v₀+t•d
  let e := l⁻¹•d
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hl : 0 < l := norm_pos_iff.mpr hd
  have he : inner ℝ e e = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hen : ‖e‖ = 1 := by
      rw [show e = l⁻¹•d from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hl)]
      exact inv_mul_cancel₀ hl.ne'
    rw [hen,one_pow]
  have hid (s : ℝ) : p+s•e = v₀+(t+s/l)•d := by
    dsimp only [p,e]
    rw [div_eq_mul_inv,smul_smul,add_smul,add_assoc]
  have hleft : p+(-(t*l))•e = v₀ := by
    rw [hid]
    have hsc : t+(-(t*l))/l = 0 := by field_simp; ring
    rw [hsc,zero_smul,add_zero]
  have hright : p+((1-t)*l)•e = v₁ := by
    rw [hid]
    have hsc : t+((1-t)*l)/l = 1 := by field_simp; ring
    rw [hsc,one_smul]
    exact add_sub_cancel _ _
  apply nonconjugate_middle_of_unit_segment hMTW x (mul_pos htpos hl) (mul_pos (sub_pos.mpr htlt) hl) he
  · intro s hs
    have hu : t+s/l ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have hh : -t ≤ s/l := (le_div_iff₀ hl).mpr (by nlinarith [hs.1])
        linarith
      · have hh : s/l ≤ 1-t := (div_le_iff₀ hl).mpr hs.2
        linarith
    rw [hid]
    apply hseg
    rw [segment_eq_image']
    exact ⟨t+s/l,hu,rfl⟩
  · rw [hleft]; exact h₀
  · rw [hright]; exact h₁

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_HullNonconjugacy
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

 theorem convexHull_nonconjugate_oai (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {A : Set (TangentSpace (model n) x)}
    (hA : ∀ a ∈ A, Nonconjugate x a)
    (hmin : convexHull ℝ A ⊆ minimizingDomain x) :
    ∀ v ∈ convexHull ℝ A, Nonconjugate x v := by
  let K := convexHull ℝ A ∩ {v | Nonconjugate x v}
  have hK : Convex ℝ K := by
    rw [convex_iff_segment_subset]
    intro u hu v hv w hw
    have hseg := (convex_convexHull ℝ A).segment_subset hu.1 hv.1
    exact ⟨hseg hw,segment_nonconjugacy hMTW x (hseg.trans hmin) hu.2 hv.2 w hw⟩
  have hAK : A ⊆ K := fun a ha => ⟨subset_convexHull ℝ A ha,hA a ha⟩
  exact fun v hv => (convexHull_min hAK hK hv).2

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.convexHull_nonconjugate_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.convexHull_nonconjugate_oai.{u_1}
