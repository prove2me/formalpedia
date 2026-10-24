-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:13:42.210824+00:00
-- url     : https://prove2.me/submissions/895cf8d2-eb89-49b5-9d6d-696efcabfe8b

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_initialCost_geometry

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

end DiscreteVariational
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
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingActionBound
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

 omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem chartKinetic_energy (x : M) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target) :
    chartKinetic x q = ‖((stateChart x).symm q).2‖^2/2 := by
  let p := (stateChart (E := Model n) x).symm q
  have hp : p ∈ (stateChart x).source := (stateChart x).map_target hq
  have hh := stateChart_pairing x p.1 ((stateChart_source x p).mp hp) p.2 p.2
  have hcoords : stateChart x p = q := (stateChart x).right_inv hq
  have hh' : metric x (stateChart x p).1 (stateChart x p).2 (stateChart x p).2 = ‖p.2‖^2 := by
    convert (show metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 = ‖p.2‖^2 from
      by simpa only [real_inner_self_eq_norm_sq] using hh) using 1
    rfl
  rw [hcoords] at hh'
  exact congrArg (fun a : ℝ => a/2) hh'

 theorem generatingAction_bound (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (z : Model n) :
    cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm z) ≤
      generatingAction x y ε (q,z) := by
  let p := (stateChart (E := Model n) x).symm q
  let Z := (chartAt (Model n) y).symm z
  let N := ‖p.2‖
  let d := dist (geodesic p (1-ε)) Z
  have hτpos : 0 < 1-ε := sub_pos.mpr hε₁
  have hc : chartCost y ((crossFlowCoordinates x y (1-ε) q).1,z) = cost (geodesic p (1-ε)) Z := by
    change cost ((chartAt (Model n) y).symm ((chartAt (Model n) y) (geodesic p (1-ε)))) Z = _
    have hτS : geodesic p (1-ε) ∈ (chartAt (Model n) y).source := (stateChart_source y _).mp hτ
    rw [(chartAt (Model n) y).left_inv hτS]
  have hd := geodesic_dist_le p 0 (1-ε)
  rw [geodesic_zero,sub_zero,abs_of_pos hτpos] at hd
  have ht : dist p.1 Z ≤ (1-ε)*N + d := by
    exact (dist_triangle p.1 (geodesic p (1-ε)) Z).trans (by dsimp [N,d]; nlinarith)
  have hsq := pow_le_pow_left₀ (dist_nonneg (x := p.1) (y := Z)) ht 2
  have hw := DiscreteVariational.weighted_two_sq ((1-ε)*N) d (1-ε) ε hτpos hε
  have hsum : 1-ε+ε = 1 := by ring
  have hdiv : ((1-ε)*N)^2/(1-ε) = (1-ε)*N^2 := by field_simp
  rw [hsum,div_one,hdiv] at hw
  change dist p.1 Z ^ 2/2 ≤ _
  dsimp only [generatingAction]
  rw [chartKinetic_energy x hq,hc]
  unfold cost
  change dist p.1 Z ^ 2/2 ≤ (1-ε)*(N^2/2)+ε⁻¹*(d^2/2)
  have heq : ε⁻¹*(d^2/2) = (d^2/ε)/2 := by ring
  rw [heq]
  nlinarith

 theorem generatingAction_eq_minimizing (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (h₁ : geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖) :
    generatingAction x y ε (q,(crossFlowCoordinates x y 1 q).1) =
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1) := by
  let p := (stateChart (E := Model n) x).symm q
  have he : (chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1 = geodesic p 1 :=
    (chartAt (Model n) y).left_inv ((stateChart_source y _).mp h₁)
  have hd := minimizing_segment_dist p (L := 1) (a := 1-ε) (b := 1)
    (by simpa only [one_mul] using hm) (sub_nonneg.mpr hε₁.le) (by linarith) le_rfl
  have hc : chartCost y ((crossFlowCoordinates x y (1-ε) q).1,(crossFlowCoordinates x y 1 q).1) =
      cost (geodesic p (1-ε)) (geodesic p 1) := by
    change cost ((chartAt (Model n) y).symm ((chartAt (Model n) y) (geodesic p (1-ε))))
      ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1) = _
    have hτS : geodesic p (1-ε) ∈ (chartAt (Model n) y).source := (stateChart_source y _).mp hτ
    rw [(chartAt (Model n) y).left_inv hτS,he]
  dsimp only [generatingAction]
  rw [chartKinetic_energy x hq,hc,he]
  change (1-ε)*(‖p.2‖^2/2)+ε⁻¹*cost (geodesic p (1-ε)) (geodesic p 1) = cost p.1 (geodesic p 1)
  unfold cost
  rw [hd,hm]
  field_simp
  ring

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

 theorem GeneratingChartAction.smooth {x y : M} {ε : ℝ} {q : Model n × Model n}
    (h : GeneratingChartAction x y ε q) :
    ContDiffAt ℝ ∞ (generatingAction x y ε) (q,(crossFlowCoordinates x y 1 q).1) :=
    generatingAction_smooth x y h.1 h.2.1 h.2.2.2

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

 theorem hessian_majorant {f : E → ℝ} {g : F → ℝ} (L : E →L[ℝ] F) {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (L x))
    (heq : f x = g (L x)) (hle : ∀ᶠ z in 𝓝 x, g (L z) ≤ f z) (v : E) :
    fderiv ℝ (fderiv ℝ g) (L x) (L v) (L v) ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let a : ℝ → ℝ := fun t => f (x+t•v)
  let b : ℝ → ℝ := fun t => g (L x+t•L v)
  have hline : ContDiff ℝ 2 (fun t : ℝ => x+t•v) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline' : ContDiff ℝ 2 (fun t : ℝ => L x+t•L v) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have ha : ContDiffAt ℝ 2 a 0 := by
    have hf' : ContDiffAt ℝ 2 f (x+(0 : ℝ)•v) := by simpa using hf
    exact hf'.comp 0 hline.contDiffAt
  have hb : ContDiffAt ℝ 2 b 0 := by
    have hg' : ContDiffAt ℝ 2 g (L x+(0 : ℝ)•L v) := by simpa using hg
    exact hg'.comp 0 hline'.contDiffAt
  have hm : IsLocalMin (a-b) 0 := by
    have ht : Tendsto (fun t : ℝ => x+t•v) (𝓝 0) (𝓝 x) := by
      simpa using hline.continuous.continuousAt.tendsto (x := (0 : ℝ))
    filter_upwards [ht hle] with t htt
    change f (x+(0 : ℝ)•v)-g (L x+(0 : ℝ)•L v) ≤ f (x+t•v)-g (L x+t•L v)
    simp only [zero_smul,add_zero,heq,sub_self]
    apply sub_nonneg.mpr
    change g (L (x+t•v)) ≤ f (x+t•v) at htt
    simpa only [map_add,map_smul] using htt
  have hh := scalar_second_nonneg hm (ha.sub hb).continuousAt
  have hsub := iteratedDeriv_sub (n := 2) ha hb
  have hs : deriv (deriv (a-b)) 0 = deriv (deriv a) 0-deriv (deriv b) 0 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def] using hsub
  rw [hs] at hh
  have hfa := line_second hf v
  have hgb := line_second hg (L v)
  change deriv (deriv a) 0 = _ at hfa
  change deriv (deriv b) 0 = _ at hgb
  rw [hfa,hgb] at hh
  linarith

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
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingTrial
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

 theorem generatingHessian_cost_trial (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : GeneratingChartAction x y ε q)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖)
    (hg : ContDiffAt ℝ 2 (initialCost x ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1)) q.1)
    (k : Model n × Model n) :
    fderiv ℝ (fderiv ℝ (initialCost x ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1))) q.1 k.1 k.1 ≤
      generatingHessian x y ε q (k,0) (k,0) := by
  let z := (crossFlowCoordinates x y 1 q).1
  let f : Model n × Model n → ℝ := fun r => generatingAction x y ε (r,z)
  let g := initialCost (n := n) x ((chartAt (Model n) y).symm z)
  have hF := hq.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiffAt ℝ 2 f q := hF.comp q (contDiffAt_id.prodMk contDiffAt_const)
  have hqnear : ∀ᶠ r in 𝓝 q, r ∈ (stateChart x).target ∧
      geodesicFlow (1-ε) ((stateChart x).symm r) ∈ (stateChart y).source := by
    refine inter_mem ((stateChart x).open_target.mem_nhds hq.1) ?_
    exact ((geodesicFlow_smooth_fixed (1-ε)).continuous.continuousAt.comp
      ((stateChart x).symm.continuousAt hq.1)).preimage_mem_nhds
        ((stateChart y).open_source.mem_nhds hq.2.1)
  have heq : f q = g q.1 := generatingAction_eq_minimizing x y hε hε₁ hq.1 hq.2.1 hq.2.2.1 hm
  have hle : ∀ᶠ r in 𝓝 q, g r.1 ≤ f r := by
    filter_upwards [hqnear] with r hr
    exact generatingAction_bound x y hε hε₁ hr.1 hr.2 z
  have hb := hessian_majorant (ContinuousLinearMap.fst ℝ (Model n) (Model n)) hf hg heq hle k
  let L : (Model n × Model n) →L[ℝ] ((Model n × Model n) × Model n) :=
    (ContinuousLinearMap.id ℝ (Model n × Model n)).prod 0
  let c : (Model n × Model n) × Model n := (0,z)
  have he : c+L q = (q,z) := by simp [c,L]
  have hF' : ContDiffAt ℝ 2 (generatingAction x y ε) (c+L q) := he.symm ▸ hF
  have hchain := hessian_affine_pullback L c hF' k
  have hchain' : fderiv ℝ (fderiv ℝ f) q k k = generatingHessian x y ε q (k,0) (k,0) := by
    simpa [f,z,generatingHessian,L,c] using hchain
  exact hchain' ▸ hb

 theorem generating_action_trial (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hq : GeneratingChartAction x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)))
    (ξ : TangentSpace (model n) x) (κ : Model n) (α : ℝ) :
    actionHessian x v ξ ξ ≤
      generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,α•κ),0) ((tangentChartLinear x ξ,α•κ),0) +
      lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
        (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v) := by
  let p : TangentBundle (model n) M := ⟨x,v⟩
  let q := stateChart (E := Model n) x p
  have hp : p ∈ (stateChart x).source := (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hi : (stateChart x).symm q = p := (stateChart x).left_inv hp
  have hY : (chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1 = exp x v := by
    dsimp only [crossFlowCoordinates]
    rw [hi]
    have hys : geodesic p 1 ∈ (chartAt (Model n) y).source := by
      have hh : geodesic ((stateChart x).symm q) 1 ∈ (chartAt (Model n) y).source :=
        (stateChart_source y _).mp hq.2.2.1
      rw [hi] at hh
      exact hh
    change (chartAt (Model n) y).symm ((chartAt (Model n) y) (geodesic p 1)) = _
    rw [(chartAt (Model n) y).left_inv hys,← exp_eq_geodesic]
  have hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖ := by
    rw [hi,← exp_eq_geodesic]
    exact injectivity_subset_minimizing x hv
  have hgeom := (initialCost_geometry x hv).1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiffAt ℝ 2 (initialCost x ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1)) q.1 := by
    rw [hY]
    exact hgeom
  have ht := generatingHessian_cost_trial x y hε hε₁ hq hm hg (tangentChartLinear x ξ,α•κ)
  rw [hY] at ht
  change _ + lowerChristoffel _ _ _ _ ≤ _
  exact add_le_add ht le_rfl

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

 theorem bilinear_quadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (A K : E) (α : ℝ)
    (h : Q K A = Q A K) :
    Q (A+α•K) (A+α•K) = Q A A+2*α*Q A K+α^2*Q K K := by
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [h]
  ring
end GeneratingCalculus

namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem generating_scalar_trial_oai (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hq : GeneratingChartAction x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)))
    (ξ : TangentSpace (model n) x) (κ : Model n) (α : ℝ) :
    actionHessian x v ξ ξ ≤
      (generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,0),0) ((tangentChartLinear x ξ,0),0) +
      lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
        (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v)) +
      2*α*generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,0),0) ((0,κ),0) +
      α^2*generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((0,κ),0) ((0,κ),0) := by
  have ht := generating_action_trial x y hε hε₁ hv hq ξ κ α
  let A : (Model n × Model n) × Model n := ((tangentChartLinear x ξ,0),0)
  let K : (Model n × Model n) × Model n := ((0,κ),0)
  have he : ((tangentChartLinear x ξ,α•κ),0) = A+α•K := by simp [A,K]
  rw [he] at ht
  rw [GeneratingCalculus.bilinear_quadratic _ A K α (generatingHessian_symmetric x y hq K A)] at ht
  dsimp only [A,K] at ht
  linarith only [ht]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial_oai.{u_1}
