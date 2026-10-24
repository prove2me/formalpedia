-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.actual_focal_trial_pole
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T12:54:51.678993+00:00
-- url     : https://prove2.me/submissions/ccaf70d4-7beb-4969-bc80-3095ad606582

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_generating_neighborhood
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_generatingHessian_focal
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_generatingHessian_vertical_nonneg
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_generating_scalar_trial

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

variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem crossFlowCoordinates_vertical (x y : M) (v : TangentSpace (model n) x) :
    (crossFlowCoordinates x y 1 (verticalCoordinates x v)).1 = chartAt (Model n) y (exp x v) := by
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  rw [verticalCoordinates_eq]
  dsimp only [crossFlowCoordinates]
  rw [(stateChart x).left_inv hp]
  change chartAt (Model n) y (geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1) = _
  rw [← exp_eq_geodesic]

 theorem fibre_kernel_state_kernel (x y : M) {v k : TangentSpace (model n) x}
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hk : fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v k = 0) :
    fderiv ℝ (fun q => (crossFlowCoordinates x y 1 q).1) (verticalCoordinates x v)
      (0,tangentChartLinear x k) = 0 := by
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hq : verticalCoordinates x v ∈ (stateChart x).target := by
    rw [verticalCoordinates_eq]; exact (stateChart x).map_source hp
  have hys : geodesicFlow 1 ((stateChart x).symm (verticalCoordinates x v)) ∈ (stateChart y).source := by
    rw [verticalCoordinates_eq,(stateChart x).left_inv hp]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ _
    simpa only [← exp_eq_geodesic] using hy
  have hD := ((chart_flow_smooth x y 1 hq hys).fst.differentiableAt (by simp)).hasFDerivAt
  have hV : HasFDerivAt (verticalCoordinates (n := n) x)
      ((0 : TangentSpace (model n) x →L[ℝ] Model n).prod (tangentChartLinear x)) v :=
    (hasFDerivAt_const (chartAt (Model n) x x) v).prodMk (tangentChartLinear x).hasFDerivAt
  have hd := hD.comp v hV
  have hd' : HasFDerivAt (fun w => chartAt (Model n) y (exp x w))
      ((fderiv ℝ (fun q => (crossFlowCoordinates x y 1 q).1) (verticalCoordinates x v)).comp
        ((0 : TangentSpace (model n) x →L[ℝ] Model n).prod (tangentChartLinear x))) v := by
    convert! hd using 1
    funext w
    exact (crossFlowCoordinates_vertical x y w).symm
  have he := congrArg (fun A : TangentSpace (model n) x →L[ℝ] Model n => A k) hd'.fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,hk] using he.symm

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

open Set Filter
open scoped Topology

namespace FirstCut

theorem scalar_trial_bound {H U R P : ℝ} (hP : 0 < P)
    (htest : ∀ a : ℝ, H ≤ U + 2 * a * R + a ^ 2 * P) :
    H ≤ U - R ^ 2 / P := by
  have h := htest (-R / P)
  have hid : U + 2 * (-R / P) * R + (-R / P) ^ 2 * P = U - R ^ 2 / P := by
    field_simp [ne_of_gt hP]
    ring
  simpa only [hid] using h

theorem quadratic_upper_of_local_min {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hmin : IsLocalMin f 0) (hzero : f 0 = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ s, |s| < δ → f s ≤ C * s ^ 2 := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := hfd.exists_lipschitzOnWith
  have hdiff : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono (fun x hx => hx.differentiableAt (by norm_num))
  obtain ⟨δ, hδ, hsubset⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hdiff)
  have h0 : (0 : ℝ) ∈ Metric.ball 0 δ := Metric.mem_ball_self hδ
  have hD0 : fderiv ℝ f 0 = 0 := hmin.fderiv_eq_zero
  refine ⟨(K : ℝ) + 1, δ, by positivity, hδ, ?_⟩
  intro s hs
  have hseg : ∀ u ∈ segment ℝ (0 : ℝ) s, ‖u‖ ≤ ‖s‖ := by
    intro u hu
    simpa using norm_sub_le_of_mem_segment hu
  have hball : ∀ u ∈ segment ℝ (0 : ℝ) s, u ∈ Metric.ball 0 δ := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
      (hseg u hu).trans_lt hs
  have hbound : ∀ u ∈ segment ℝ (0 : ℝ) s, ‖fderiv ℝ f u‖ ≤ (K : ℝ) * ‖s‖ := by
    intro u hu
    have h := hK.norm_sub_le (hsubset (hball u hu)).1 (hsubset h0).1
    rw [hD0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hseg u hu) K.coe_nonneg)
  have hm := (convex_segment (0 : ℝ) s).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hsubset (hball u hu)).2) hbound
    (left_mem_segment ℝ (0 : ℝ) s) (right_mem_segment ℝ (0 : ℝ) s)
  rw [hzero, sub_zero, sub_zero] at hm
  have hsquare : ‖s‖ * ‖s‖ = s ^ 2 := by
    simpa only [Real.norm_eq_abs, pow_two] using (sq_abs s)
  have hfinal : ‖f s‖ ≤ (K : ℝ) * s ^ 2 := by
    calc
      ‖f s‖ ≤ (K : ℝ) * ‖s‖ * ‖s‖ := hm
      _ = (K : ℝ) * s ^ 2 := by rw [mul_assoc, hsquare]
  calc
    f s ≤ ‖f s‖ := le_abs_self _
    _ ≤ (K : ℝ) * s ^ 2 := hfinal
    _ ≤ ((K : ℝ) + 1) * s ^ 2 := by nlinarith [sq_nonneg s]

theorem two_parameter_quadratic_upper {P : ℝ × ℝ → ℝ}
    (hP : ContDiffAt ℝ 2 P (0, 0))
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ P (s, 0)) (hzero : P (0, 0) = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ s h : ℝ,
      |s| < δ → 0 ≤ h → h < δ → P (s, h) ≤ C * (s ^ 2 + h) := by
  have hslice : ContDiffAt ℝ 2 (fun s : ℝ => P (s, 0)) 0 :=
    hP.comp (f := fun s : ℝ => (s, (0 : ℝ))) 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hlocal : IsLocalMin (fun s : ℝ => P (s, 0)) 0 := by
    simpa only [IsLocalMin, IsMinFilter, hzero] using hmin
  obtain ⟨C, δ₁, hC, hδ₁, hquad⟩ := quadratic_upper_of_local_min hslice hlocal hzero
  obtain ⟨K, t, ht, hK⟩ := (hP.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).exists_lipschitzOnWith
  obtain ⟨δ₂, hδ₂, ht₂⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨C + (K : ℝ) + 1, min δ₁ δ₂, by positivity, lt_min hδ₁ hδ₂, ?_⟩
  intro s h hs hh hhδ
  have hs₁ : |s| < δ₁ := hs.trans_le (min_le_left _ _)
  have hs₂ : |s| < δ₂ := hs.trans_le (min_le_right _ _)
  have hh₂ : |h| < δ₂ := by rw [abs_of_nonneg hh]; exact hhδ.trans_le (min_le_right _ _)
  have hmem : (s, h) ∈ t := ht₂ (by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      max_lt_iff] using And.intro hs₂ hh₂)
  have hmem0 : (s, 0) ∈ t := ht₂ (by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      abs_zero, max_lt_iff] using And.intro hs₂ hδ₂)
  have hdiff := hK.norm_sub_le hmem hmem0
  have hnorm : ‖(s, h) - (s, 0)‖ = h := by
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hh, hh]
  rw [hnorm] at hdiff
  have hdiff' : P (s, h) - P (s, 0) ≤ (K : ℝ) * h :=
    (le_abs_self _).trans hdiff
  have hsquare : 0 ≤ s ^ 2 := sq_nonneg _
  have hquad' := hquad s hs₁
  nlinarith [K.coe_nonneg, mul_nonneg K.coe_nonneg hsquare, mul_nonneg hC.le hh]

theorem pole_of_smooth_index_coefficients
    {P U R H : ℝ × ℝ → ℝ}
    (hP : ContDiffAt ℝ 2 P (0, 0))
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ P (s, 0)) (hzero : P (0, 0) = 0)
    (hU : ContinuousAt U (0, 0)) (hR : ContinuousAt R (0, 0))
    (hRzero : R (0, 0) ≠ 0)
    (hpositive : ∀ᶠ q in 𝓝 (0, 0), 0 < q.2 → 0 < P q)
    (htest : ∀ᶠ q in 𝓝 (0, 0), 0 < q.2 →
      ∀ a : ℝ, H q ≤ U q + 2 * a * R q + a ^ 2 * P q) :
    ∃ C c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ h, 0 < h → h < δ → ∀ s, |s| < δ →
      H (s, h) ≤ C - c / (s ^ 2 + h) := by
  obtain ⟨B, δ₁, hB, hδ₁, hbound⟩ := two_parameter_quadratic_upper hP hmin hzero
  have hR2 : 0 < R (0, 0) ^ 2 := sq_pos_of_ne_zero hRzero
  have hUbound : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), U q < U (0, 0) + 1 :=
    hU.eventually_lt continuousAt_const (by linarith)
  have hRbound : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), R (0, 0) ^ 2 / 2 < R q ^ 2 :=
    continuousAt_const.eventually_lt (hR.pow 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hgood⟩ := Metric.mem_nhds_iff.mp
    (hUbound.and (hRbound.and (hpositive.and htest)))
  refine ⟨U (0, 0) + 1, (R (0, 0) ^ 2 / 2) / B, min δ₁ δ₂,
    div_pos (by positivity) hB, lt_min hδ₁ hδ₂, ?_⟩
  intro h hh hhδ s hs
  have hh₁ : h < δ₁ := hhδ.trans_le (min_le_left _ _)
  have hs₁ : |s| < δ₁ := hs.trans_le (min_le_left _ _)
  have hh₂ : |h| < δ₂ := by rw [abs_of_pos hh]; exact hhδ.trans_le (min_le_right _ _)
  have hs₂ : |s| < δ₂ := hs.trans_le (min_le_right _ _)
  obtain ⟨hUb, hRb, hPb, htrial⟩ := hgood (show (s, h) ∈ Metric.ball (0, 0) δ₂ by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      max_lt_iff] using And.intro hs₂ hh₂)
  have hposP := hPb hh
  have hscalar := scalar_trial_bound hposP (htrial hh)
  have hden : 0 < s ^ 2 + h := by positivity
  have hPbound := hbound s h hs₁ hh.le hh₁
  have hquot : (R (0, 0) ^ 2 / 2) / B / (s ^ 2 + h) ≤ R (s, h) ^ 2 / P (s, h) := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hB hden) hposP).mpr
    calc
      (R (0, 0) ^ 2 / 2) * P (s, h) ≤
          (R (0, 0) ^ 2 / 2) * (B * (s ^ 2 + h)) :=
        mul_le_mul_of_nonneg_left hPbound (by positivity)
      _ ≤ R (s, h) ^ 2 * (B * (s ^ 2 + h)) :=
        mul_le_mul_of_nonneg_right hRb.le (by positivity)
  linarith

end FirstCut

open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

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

 theorem generatingHessian_smooth (x y : M) {ε : ℝ} {q : Model n × Model n}
    (hq : GeneratingChartAction x y ε q) : ContDiffAt ℝ ∞ (generatingHessian x y ε) q := by
  have hH := (hq.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact hH.comp q (contDiffAt_id.prodMk hq.flow_smooth.fst)

 theorem generatingHessian_symmetric (x y : M) {ε : ℝ} {q : Model n × Model n}
    (hq : GeneratingChartAction x y ε q)
    (U V : (Model n × Model n) × Model n) :
    generatingHessian x y ε q U V = generatingHessian x y ε q V U :=
    ((hq.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).isSymmSndFDerivAt (by norm_num)).eq U V

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace GeneratingCalculus
 theorem positive_of_trial {H U R P : ℝ} (hP : 0 ≤ P) (hR : R ≠ 0)
    (h : ∀ a : ℝ, H ≤ U + 2*a*R+a^2*P) : 0 < P := by
  by_contra hn
  have hzero : P = 0 := le_antisymm (le_of_not_gt hn) hP
  have hh := h ((H-U-1)/(2*R))
  rw [hzero,mul_zero,add_zero] at hh
  have heq : U+2*((H-U-1)/(2*R))*R = H-1 := by field_simp; ring
  rw [heq] at hh
  linarith

end GeneratingCalculus

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_FocalPole
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

 theorem verticalCoordinates_minimizing (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ minimizingDomain x) :
    dist ((stateChart x).symm (verticalCoordinates x v)).1
      (geodesic ((stateChart x).symm (verticalCoordinates x v)) 1) =
      ‖((stateChart x).symm (verticalCoordinates x v)).2‖ := by
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  rw [verticalCoordinates_eq,(stateChart x).left_inv hp,← exp_eq_geodesic]
  exact hv

 theorem actual_focal_trial_pole_oai (x : M) {p e k : TangentSpace (model n) x} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hseg : ∀ s ∈ Icc (-a) b, p+s•e ∈ minimizingDomain x)
    (hk : fderiv ℝ (fun w => chartAt (Model n) (exp x p) (exp x w)) p k = 0)
    (ξ : TangentSpace (model n) x) (hξ : inner ℝ ξ k ≠ 0) :
    FirstCut.HasTrialPole (fun h s => actionHessian x ((1-h)•(p+s•e))) ξ := by
  let y := exp x p
  let κ := tangentChartLinear x k
  let W : ℝ × ℝ → TangentSpace (model n) x := fun z => (1-z.2)•(p+z.1•e)
  let q : ℝ × ℝ → Model n × Model n := fun z => verticalCoordinates x (W z)
  let A : (Model n × Model n) × Model n := ((tangentChartLinear x ξ,0),0)
  let K : (Model n × Model n) × Model n := ((0,κ),0)
  have hW : ContDiff ℝ ∞ W := (contDiff_const.sub contDiff_snd).smul (contDiff_const.add (contDiff_fst.smul contDiff_const))
  have hq : ContDiff ℝ ∞ q := (verticalCoordinates_smooth x).comp hW
  have hW₀ : W (0,0) = p := by simp [W]
  have hq₀ : q (0,0) = verticalCoordinates x p := by rw [show q (0,0) = verticalCoordinates x (W (0,0)) from rfl,hW₀]
  have hp : (⟨x,p⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hpt : verticalCoordinates x p ∈ (stateChart x).target := by
    rw [verticalCoordinates_eq]; exact (stateChart x).map_source hp
  have hpy : geodesicFlow 1 ((stateChart x).symm (verticalCoordinates x p)) ∈ (stateChart y).source := by
    rw [verticalCoordinates_eq,(stateChart x).left_inv hp]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,p⟩ : TangentBundle (model n) M) 1 ∈ _
    simpa only [← exp_eq_geodesic] using mem_chart_source (Model n) y
  obtain ⟨ε,hε,hε₁,hgen⟩ := exists_generating_neighborhood x y hpt hpy
  have hgen₀ := mem_of_mem_nhds hgen
  have hnear : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), GeneratingChartAction x y ε (q z) := by
    have hc : Tendsto q (𝓝 (0,0)) (𝓝 (verticalCoordinates x p)) := hq₀ ▸ hq.continuous.continuousAt.tendsto
    exact hc hgen
  have hHs : ContDiffAt ℝ ∞ (fun z => generatingHessian x y ε (q z)) (0,0) := by
    apply ContDiffAt.comp (f := q) (g := generatingHessian x y ε) (0,0) _ hq.contDiffAt
    rw [hq₀]
    exact generatingHessian_smooth x y hgen₀
  let P : ℝ × ℝ → ℝ := fun z => generatingHessian x y ε (q z) K K
  let R : ℝ × ℝ → ℝ := fun z => generatingHessian x y ε (q z) A K
  let U : ℝ × ℝ → ℝ := fun z => generatingHessian x y ε (q z) A A +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x (W z))
  have hP : ContDiffAt ℝ 2 P (0,0) :=
    ((hHs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hR : ContinuousAt R (0,0) := ((hHs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt
  have hU : ContinuousAt U (0,0) := by
    refine ((hHs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt.add ?_
    unfold lowerChristoffel
    have hh := (tangentChartLinear x).continuous.comp hW.continuous
    fun_prop
  have hker := fibre_kernel_state_kernel x y (mem_chart_source (Model n) y) hk
  have hPzero : P (0,0) = 0 := by
    dsimp only [P]
    rw [hq₀]
    have hh := generatingHessian_focal x y hε.ne' hgen hker 0 κ
    simpa only [K,map_zero,neg_zero] using hh
  have hRvalue : R (0,0) = -inner ℝ k ξ := by
    dsimp only [R]
    rw [hq₀,generatingHessian_symmetric x y hgen₀ A K]
    have hh := generatingHessian_focal x y hε.ne' hgen hker (tangentChartLinear x ξ) 0
    change generatingHessian x y ε (verticalCoordinates x p) K A = _ at hh
    rw [show (verticalCoordinates x p).1 = chartAt (Model n) x x from rfl] at hh
    have hmet : metric x (chartAt (Model n) x x) (tangentChartLinear x k) (tangentChartLinear x ξ) = inner ℝ k ξ :=
      metric_chart_pair x x (mem_chart_source (Model n) x) k ξ
    rw [hmet] at hh
    exact hh
  have hRzero : R (0,0) ≠ 0 := by rw [hRvalue,neg_ne_zero,real_inner_comm]; exact hξ
  have hsnear : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Icc (-a) b := Icc_mem_nhds (by linarith) hb
  have hPmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ P (s,0) := by
    have hsmooth : ContinuousAt (fun s : ℝ => (s,(0 : ℝ))) 0 := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hsnear,hsmooth.tendsto hnear] with s hs hgs
    have hm := hseg s hs
    have hWz : W (s,0) = p+s•e := by simp [W]
    exact generatingHessian_vertical_nonneg x y hε hε₁ hgs
      (verticalCoordinates_minimizing x (hWz.symm ▸ hm)) κ
  have hI : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), 0 < z.2 → W z ∈ injectivityDomain x := by
    have hs := (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ → ℝ) (0,0)).tendsto hsnear
    have ht : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), z.2 < 1 :=
      continuousAt_snd.eventually_lt continuousAt_const (by norm_num)
    filter_upwards [hs,ht] with z hz ht hz₀
    exact strict_radial_mem_injectivity (hseg z.1 hz) (by linarith) (by linarith)
  have htest : ∀ᶠ z in 𝓝 ((0,0) : ℝ × ℝ), 0 < z.2 → ∀ α : ℝ,
      actionHessian x (W z) ξ ξ ≤ U z + 2*α*R z + α^2*P z := by
    filter_upwards [hnear,hI] with z hgz hIz hz α
    have hgz' : GeneratingChartAction x y ε (stateChart x (⟨x,W z⟩ : TangentBundle (model n) M)) := by
      simpa only [q,verticalCoordinates_eq] using hgz
    simpa only [U,R,P,q,verticalCoordinates_eq,A,K] using
      generating_scalar_trial x y hε hε₁ (hIz hz) hgz' ξ κ α
  have hpositive : ∀ᶠ z in 𝓝 ((0,0) : ℝ × ℝ), 0 < z.2 → 0 < P z := by
    have hRnear := hR.eventually_ne hRzero
    filter_upwards [hnear,hI,htest,hRnear] with z hgz hIz htz hRz hz
    apply GeneratingCalculus.positive_of_trial _ hRz (htz hz)
    exact generatingHessian_vertical_nonneg x y hε hε₁ hgz
      (verticalCoordinates_minimizing x (injectivity_subset_minimizing x (hIz hz))) κ
  exact FirstCut.pole_of_smooth_index_coefficients hP hPmin hPzero hU hR hRzero hpositive htest

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.actual_focal_trial_pole_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.actual_focal_trial_pole_oai.{u_1}
