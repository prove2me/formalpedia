-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.activeHull_exp_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T03:09:31.190165+00:00
-- url     : https://prove2.me/submissions/5753d818-403b-4d94-8d3a-e7af9f35caaa

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_cost_first_limit
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_minimizing_vector

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
-- module Solutions.OAIQW_WeakMTW.Geodesics_BundleMinimizerCompactness
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
 theorem tangent_norm_continuous : Continuous (fun p : TangentBundle (model n) M => ‖p.2‖) := by
  have hh : ContMDiff ((model n).prod 𝓘(ℝ, Model n)) 𝓘(ℝ,ℝ) ∞
      (fun p : TangentBundle (model n) M => inner ℝ p.2 p.2) :=
    (show ContMDiff ((model n).prod 𝓘(ℝ, Model n)) ((model n).prod 𝓘(ℝ, Model n)) ∞
      (fun p : TangentBundle (model n) M => (⟨p.1,p.2⟩ : TangentBundle (model n) M)) from contMDiff_id).inner_bundle contMDiff_id
  simpa only [real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)] using hh.continuous.sqrt

omit [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem locally_compact_tangent_bound (x : M) (R : ℝ) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ K : Set (TangentBundle (model n) M),
      IsCompact K ∧ ∀ p : TangentBundle (model n) M, p.1 ∈ V → ‖p.2‖ ≤ R → p ∈ K := by
  let C := chartAt (Model n) x
  have hx : C x ∈ C.target := C.map_source (mem_chart_source (Model n) x)
  obtain ⟨κ,hκ,W,hW,hWx,hWT,hcoer⟩ := uniform_metric_coercive C.open_target
    (metric_smooth x).continuousOn hx (fun v hv => metric_positive x hx hv)
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hWx)
  let B := Metric.closedBall (C x) (r/2)
  have hBW : B ⊆ W := fun z hz => hrW (lt_of_le_of_lt hz (half_lt_self hr))
  let A : ℝ := 1+R^2/κ
  let Q := B ×ˢ Metric.closedBall (0 : Model n) A
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hQT : Q ⊆ (stateChart x).target := fun q hq => (stateChart_target x q).mpr (hWT (hBW hq.1))
  let K := (stateChart x).symm '' Q
  have hK : IsCompact K := hQ.image_of_continuousOn ((stateChart x).continuousOn_symm.mono hQT)
  let V := C.source ∩ C ⁻¹' Metric.ball (C x) (r/2)
  have hV : IsOpen V := C.continuousOn.isOpen_inter_preimage C.open_source Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_chart_source (Model n) x,Metric.mem_ball_self (half_pos hr)⟩
  refine ⟨V,hV,hxV,K,hK,?_⟩
  intro p hp hpR
  have hpS : p ∈ (stateChart x).source := (stateChart_source x _).mpr hp.1
  let q := stateChart x p
  have hqB : q.1 ∈ B := (show dist (C p.1) (C x) < r/2 from hp.2).le
  have hpair := stateChart_pairing x p.1 hp.1 p.2 p.2
  have hco := hcoer q.1 (hBW hqB) q.2
  have henergy : metric x q.1 q.2 q.2 = ‖p.2‖^2 := by
    change metric x q.1 q.2 q.2 = inner ℝ p.2 p.2 at hpair
    simpa only [real_inner_self_eq_norm_sq] using hpair
  rw [henergy] at hco
  have hnorm : ‖q.2‖^2 ≤ R^2/κ := (le_div_iff₀ hκ).mpr (by
    have hpR' : ‖p.2‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hpR 2
    nlinarith)
  have hbound : ‖q.2‖ ≤ A := by dsimp only [A]; nlinarith [sq_nonneg (‖q.2‖-1)]
  refine ⟨q,⟨hqB,?_⟩,(stateChart x).left_inv hpS⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using hbound

 theorem totalMinimizingSet_closed : IsClosed (totalMinimizingSet (n := n) (M := M)) :=
  isClosed_eq ((contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.dist exp_total_smooth.continuous)
    tangent_norm_continuous

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_TangentDiskCompact
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

omit [IsRiemannianManifold (model n) M] in
 theorem tangent_disk_compact (R : ℝ) :
    IsCompact {p : TangentBundle (model n) M | ‖p.2‖ ≤ R} := by
  classical
  choose V hV hxV K hK hbound using (fun x : M => locally_compact_tangent_bound (n := n) x R)
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover V hV (fun x _ => mem_iUnion.mpr ⟨x,hxV x⟩)
  have hbig : IsCompact (⋃ x ∈ F, K x) := F.finite_toSet.isCompact_biUnion (fun x _ => hK x)
  apply hbig.of_isClosed_subset (isClosed_le tangent_norm_continuous continuous_const)
  intro p hp
  obtain ⟨x,hx,hpx⟩ := mem_iUnion₂.mp (hF (mem_univ p.1))
  exact mem_iUnion₂.mpr ⟨x,hx,hbound x p hpx hp⟩

 theorem totalMinimizingSet_compact : IsCompact (totalMinimizingSet (n := n) (M := M)) := by
  apply (tangent_disk_compact (n := n) (M := M) (Metric.diam (univ : Set M))).of_isClosed_subset totalMinimizingSet_closed
  intro p hp
  change ‖p.2‖ ≤ Metric.diam (univ : Set M)
  rw [← show dist p.1 (exp p.1 p.2) = ‖p.2‖ from hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

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
 theorem cost_continuous : Continuous (fun p : M × M => cost p.1 p.2) :=
    (continuous_fst.dist continuous_snd |>.pow 2).div_const 2

omit [CompactSpace M] in
 theorem finitePotential_continuous (y : ι → M) (h : ι → ℝ) : Continuous (finitePotential y h) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  exact continuous_const.sub ((continuous_id.dist continuous_const).pow 2 |>.div_const 2)

omit [CompactSpace M] in
 theorem finitePotential_ge (y : ι → M) (h : ι → ℝ) (x : M) (i : ι) :
    h i-cost x (y i) ≤ finitePotential y h x :=
    Finset.le_sup' (fun j => h j-cost x (y j)) (Finset.mem_univ i)

omit [CompactSpace M] in
 theorem finitePotential_attained (y : ι → M) (h : ι → ℝ) (x : M) :
    ∃ i, finitePotential y h x = h i-cost x (y i) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => h i-cost x (y i))
  exact ⟨i,hi⟩

 theorem activeVelocities_nonempty (y : ι → M) (h : ι → ℝ) (x : M) :
    (activeVelocities (n := n) y h x).Nonempty := by
  obtain ⟨i,hi⟩ := finitePotential_attained y h x
  obtain ⟨a,ha,han⟩ := exists_minimizing_vector (n := n) x (y i)
  refine ⟨a,?_,i,ha,hi⟩
  change dist x (exp x a) = ‖a‖
  rw [ha,han]

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem activeGraph_eq (y : ι → M) (h : ι → ℝ) :
    activeGraph y h = ⋃ i : ι, totalMinimizingSet (n := n) (M := M) ∩
      {p : TangentBundle (model n) M | exp p.1 p.2 = y i ∧ finitePotential y h p.1 = h i-cost p.1 (y i)} := by
  ext p
  simp only [activeGraph,activeVelocities,mem_ofPred_eq,mem_iUnion,mem_inter_iff]
  exact ⟨fun ⟨hp,i,hi⟩ => ⟨i,hp,hi⟩,fun ⟨i,hp,hi⟩ => ⟨hp,i,hi⟩⟩

 theorem activeGraph_compact (y : ι → M) (h : ι → ℝ) : IsCompact (activeGraph (n := n) y h) := by
  rw [activeGraph_eq]
  apply isCompact_iUnion
  intro i
  apply totalMinimizingSet_compact.inter_right
  apply IsClosed.inter
  · exact isClosed_eq exp_total_smooth.continuous continuous_const
  · have hb : Continuous (fun p : TangentBundle (model n) M => p.1) :=
      (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
    exact isClosed_eq ((finitePotential_continuous y h).comp hb)
      (continuous_const.sub ((hb.dist continuous_const).pow 2 |>.div_const 2))

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
-- module Solutions.OAIQW_WeakMTW.Support_ActiveGraphLimits
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

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentBundle_firstCountable : FirstCountableTopology (TangentBundle (model n) M) := by
  constructor
  intro p
  have hp : p ∈ (RiemannianLocal.stateChart p.1).source :=
    (RiemannianLocal.stateChart_source p.1 p).mpr (mem_chart_source (Model n) p.1)
  rw [(RiemannianLocal.stateChart p.1).nhds_eq_comap_inf_principal hp]
  infer_instance

 theorem active_velocity_subseq (y : ι → M) (h : ι → ℝ)
    {p : ℕ → M} {x : M} (hp : Tendsto p atTop (𝓝 x))
    (a : ∀ j, TangentSpace (model n) (p j))
    (ha : ∀ j, a j ∈ activeVelocities y h (p j)) :
    ∃ a₀ ∈ activeVelocities y h x, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (⟨p (ρ j),a (ρ j)⟩ : TangentBundle (model n) M)) atTop (𝓝 ⟨x,a₀⟩) := by
  let := tangentBundle_firstCountable (n := n) (M := M)
  obtain ⟨⟨z,a₀⟩,ha₀,ρ,hρ,hlim⟩ := (activeGraph_compact y h).tendsto_subseq
    (fun j => show (⟨p j,a j⟩ : TangentBundle (model n) M) ∈ activeGraph y h from ha j)
  have hb : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  have hz : z = x := tendsto_nhds_unique (hb.continuousAt.tendsto.comp hlim) (hp.comp hρ.tendsto_atTop)
  subst z
  exact ⟨a₀,ha₀,ρ,hρ,hlim⟩

 theorem shortened_upper_difference {x : M} {w : TangentSpace (model n) x}
    (hw : w ∈ minimizingDomain x) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (z : M) :
    cost z (exp x w)-cost x (exp x w) ≤
      (cost z (exp x (ℓ•w))-cost x (exp x (ℓ•w)))/ℓ := by
  have hsplit := cost_triangle_split z (exp x (ℓ•w)) (exp x w) hℓ (sub_pos.mpr hℓ₁)
  have hdist := minimizing_shortened_dist hw hℓ.le hℓ₁.le (le_refl 1)
  simp only [one_smul] at hdist
  have htail : cost (exp x (ℓ•w)) (exp x w) = (1-ℓ)^2*‖w‖^2/2 := by
    unfold cost
    rw [hdist,mul_pow]
  have hbase : cost x (exp x w) = ‖w‖^2/2 := by
    unfold cost
    rw [show dist x (exp x w) = ‖w‖ from hw]
  rw [add_sub_cancel,div_one,htail] at hsplit
  rw [hbase,minimizing_shortened_cost hw hℓ.le hℓ₁.le]
  have hid : (1-ℓ)^2*‖w‖^2/2/(1-ℓ)-‖w‖^2/2 = -(ℓ^2*‖w‖^2/2)/ℓ := by
    field_simp [hℓ.ne',(sub_pos.mpr hℓ₁).ne']
    ring
  rw [neg_div] at hid
  rw [sub_div]
  linarith

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
-- module Solutions.OAIQW_WeakMTW.Support_ConvexRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set
open scoped BigOperators
namespace ConvexRepresentation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem fixed_size {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) {N : ℕ}
    (hN : Module.finrank ℝ E + 1 ≤ N) :
    ∃ (z : Fin N → E) (w : Fin N → ℝ), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  classical
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  have hTS : (T : Set E) ⊆ S := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hTx : x ∈ convexHull ℝ (T : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have hTI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hTN : Fintype.card T ≤ N := hTI.card_le_finrank_succ.trans
    ((Nat.add_le_add_right (Submodule.finrank_le _) 1).trans hN)
  obtain ⟨a₀,ha₀⟩ := Caratheodory.minCardFinsetOfMemConvexHull_nonempty hx
  have htcombo := hTx
  rw [Finset.convexHull_eq] at htcombo
  obtain ⟨v,hv,hvsum,hvx⟩ := htcombo
  have hvsum' : ∑ i : T, v i = 1 := by simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hvsum
  have hvx' : ∑ i : T, v i • (i : E) = x := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hvsum] at hvx
    change (∑ i ∈ T.attach, (fun j : E => v j • j) (i : E)) = x
    rw [Finset.sum_attach (f := fun j : E => v j • j)]
    exact hvx
  obtain ⟨e⟩ : Nonempty (T ↪ Fin N) := Function.Embedding.nonempty_of_card_le (by simpa using hTN)
  let z : Fin N → E := Function.extend e (fun i : T => (i : E)) (fun _ => a₀)
  let w : Fin N → ℝ := Function.extend e (fun i : T => v i) (fun _ => 0)
  have hz (i : T) : z (e i) = (i : E) := e.injective.extend_apply _ _ i
  have hw (i : T) : w (e i) = v i := e.injective.extend_apply _ _ i
  have hwzero (i : Fin N) (hi : i ∉ range e) : w i = 0 := Function.extend_apply' _ _ _ hi
  refine ⟨z,w,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ range e
    · obtain ⟨j,rfl⟩ := hi
      rw [hz]
      exact hTS j.2
    · have hi' : z i = a₀ := Function.extend_apply' _ _ _ hi
      rw [hi']
      exact hTS ha₀
  · intro i
    by_cases hi : i ∈ range e
    · obtain ⟨j,rfl⟩ := hi
      rw [hw]
      exact hv j j.2
    · rw [hwzero i hi]
  · rw [← hvsum']
    symm
    exact Fintype.sum_of_injective e e.injective _ w (fun i hi => hwzero i hi) (fun i => (hw i).symm)
  · rw [← hvx']
    symm
    apply Fintype.sum_of_injective e e.injective
    · intro i hi
      rw [hwzero i hi,zero_smul]
    · intro i
      rw [hw,hz]

end
end ConvexRepresentation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_FiberHullCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set
open scoped BigOperators
namespace ConvexRepresentation
noncomputable section
variable {B E : Type*} [TopologicalSpace B] [T2Space B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem fiberHull_compact {K : Set (B × E)} (hK : IsCompact K) :
    IsCompact (fiberHull K) := by
  classical
  let N := Module.finrank ℝ E + 1
  let i₀ : Fin N := ⟨0,Nat.zero_lt_succ _⟩
  let simplex : Set (Fin N → ℝ) :=
    {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}
  have simplex_compact : IsCompact simplex := by
    exact isCompact_stdSimplex ℝ (Fin N)
  let D : Set ((Fin N → ℝ) × (Fin N → B × E)) :=
    (simplex ×ˢ {z | ∀ i, z i ∈ K}) ∩ {q | ∀ i, (q.2 i).1 = (q.2 i₀).1}
  let F : ((Fin N → ℝ) × (Fin N → B × E)) → B × E :=
    fun q => ((q.2 i₀).1,∑ i, q.1 i • (q.2 i).2)
  have hD : IsCompact D := by
    apply (simplex_compact.prod (isCompact_pi_infinite (fun _ : Fin N => hK))).inter_right
    have hc (i : Fin N) : Continuous (fun q : (Fin N → ℝ) × (Fin N → B × E) => (q.2 i).1) :=
      ((continuous_apply i).comp continuous_snd).fst
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun i => isClosed_eq (hc i) (hc i₀))
  have hF : Continuous F := by
    apply Continuous.prodMk
    · exact ((continuous_apply i₀).comp continuous_snd).fst
    · exact continuous_finsetSum Finset.univ (fun i _ =>
        ((continuous_apply i).comp continuous_fst).smul
          (((continuous_apply i).comp continuous_snd).snd))
  have heq : F '' D = fiberHull K := by
    ext q
    constructor
    · rintro ⟨⟨w,z⟩,⟨⟨hw,hz⟩,hbase⟩,rfl⟩
      change (∑ i, w i • (z i).2) ∈ convexHull ℝ {v | ((z i₀).1,v) ∈ K}
      apply (convex_convexHull ℝ _).sum_mem
      · intro i _
        exact hw.1 i
      · exact hw.2
      · intro i _
        apply subset_convexHull
        have hi : z i ∈ K := hz i
        change ((z i₀).1,(z i).2) ∈ K
        rw [← hbase i]
        exact hi
    · intro hq
      obtain ⟨z,w,hz,hw,hws,hwz⟩ := fixed_size hq (le_refl (Module.finrank ℝ E+1))
      refine ⟨(w,fun i => (q.1,z i)),⟨⟨⟨hw,hws⟩,?_⟩,?_⟩,?_⟩
      · intro i
        exact hz i
      · intro i
        rfl
      · exact Prod.ext rfl hwz
  rw [← heq]
  exact hD.image hF

end
end ConvexRepresentation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_TangentHullCompact
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
open RiemannianLocal ConvexRepresentation
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentHull_chart (x : M) (K : Set (TangentBundle (model n) M))
    {X : Set M} (hX : X ⊆ (chartAt (Model n) x).source)
    {p : TangentBundle (model n) M} (hp : p.1 ∈ X) :
    stateChart x p ∈ fiberHull (stateChart x '' (K ∩ {q | q.1 ∈ X})) ↔ p ∈ tangentHull K := by
  cases p with | mk b v =>
    let c := chartAt (Model n) x
    let e := trivializationAt (Model n) (TangentSpace (model n)) x
    have hb : b ∈ e.baseSet := by
      simpa only [e,TangentBundle.trivializationAt_baseSet] using hX hp
    let L := e.continuousLinearEquivAt ℝ b hb
    let A : Set (TangentSpace (model n) b) := {a | (⟨b,a⟩ : TangentBundle (model n) M) ∈ K}
    have heq : {w : Model n | (c b,w) ∈ stateChart x '' (K ∩ {q | q.1 ∈ X})} = L '' A := by
      ext w
      constructor
      · rintro ⟨⟨d,u⟩,⟨huK,huX⟩,hcoord⟩
        have hdb : d = b := c.injOn (hX huX) (hX hp) (congrArg Prod.fst hcoord)
        subst d
        exact ⟨u,huK,congrArg Prod.snd hcoord⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨⟨b,u⟩,⟨hu,hp⟩,rfl⟩
    change L v ∈ convexHull ℝ {w | (c b,w) ∈ stateChart x '' (K ∩ {q | q.1 ∈ X})} ↔ v ∈ convexHull ℝ A
    have hL : L '' convexHull ℝ A = convexHull ℝ (L '' A) := L.toLinearMap.image_convexHull A
    rw [heq,← hL]
    exact L.injective.mem_set_image

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentHull_closed {K : Set (TangentBundle (model n) M)} (hK : IsCompact K) :
    IsClosed (tangentHull K) := by
  apply isClosed_iff_nhds.mpr
  intro p hp
  let c := chartAt (Model n) p.1
  obtain ⟨X,hXn,hXcl,hXc⟩ := exists_mem_nhds_isClosed_subset (c.open_source.mem_nhds (mem_chart_source (Model n) p.1))
  have hb : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  let K' := K ∩ {q : TangentBundle (model n) M | q.1 ∈ X}
  have hK' : IsCompact K' := hK.inter_right (hXcl.preimage hb)
  have hKS : K' ⊆ (stateChart p.1).source := fun q hq => (stateChart_source p.1 q).mpr (hXc hq.2)
  let C := stateChart p.1 '' K'
  have hC : IsCompact C := hK'.image_of_continuousOn ((stateChart p.1).continuousOn.mono hKS)
  have hH := fiberHull_compact hC
  have hpS : p ∈ (stateChart p.1).source := (stateChart_source p.1 p).mpr (mem_chart_source (Model n) p.1)
  have hcp : ContinuousAt (stateChart p.1) p := (stateChart p.1).continuousAt hpS
  have hpX : p.1 ∈ X := mem_of_mem_nhds hXn
  apply (tangentHull_chart p.1 K hXc hpX).mp
  by_contra hn
  have hpre : stateChart p.1 ⁻¹' (fiberHull C)ᶜ ∈ 𝓝 p :=
    hcp.preimage_mem_nhds (hH.isClosed.isOpen_compl.mem_nhds hn)
  have hbase : {q : TangentBundle (model n) M | q.1 ∈ X} ∈ 𝓝 p := hb.continuousAt.preimage_mem_nhds hXn
  obtain ⟨q,⟨hqX,hqC⟩,hqH⟩ := hp _ (inter_mem hbase hpre)
  exact hqC ((tangentHull_chart p.1 K hXc hqX).mpr hqH)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_MinimizerCapture
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

 theorem minimizing_pole_direction (y : ι → M) (h : ι → ℝ)
    {x : M} {w : TangentSpace (model n) x} (hw : w ∈ minimizingDomain x)
    {s : ℝ} (hs : 0 < s)
    (hmin : ∀ z, cost x (exp x w) + s*finitePotential y h x ≤
      cost z (exp x w) + s*finitePotential y h z)
    (ξ : TangentSpace (model n) x) :
    ∃ a ∈ activeVelocities y h x, inner ℝ w ξ ≤ s*inner ℝ a ξ := by
  let c := chartAt (Model n) x
  let l : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hl : Tendsto l atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlpos (j : ℕ) : 0 < l j := one_div_pos.mpr (by positivity)
  let p : ℕ → M := fun j => c.symm (c x+l j•tangentChartLinear x ξ)
  have hp : Tendsto p atTop (𝓝 x) := by
    have hc := (c.symm.continuousAt (c.map_source (mem_chart_source (Model n) x))).tendsto
    have hh := (tendsto_const_nhds (x := c x)).add (hl.smul_const (tangentChartLinear x ξ))
    simp only [zero_smul,add_zero] at hh
    simpa only [p,Function.comp_def,c.left_inv (mem_chart_source (Model n) x)] using hc.comp hh
  choose a ha using fun j => activeVelocities_nonempty (n := n) y h (p j)
  obtain ⟨a₀,ha₀,ρ,hρ,hlim⟩ := active_velocity_subseq y h hp a ha
  have hz : Tendsto (fun j => exp (p (ρ j)) ((1/2:ℝ)•a (ρ j))) atTop (𝓝 (exp x ((1/2:ℝ)•a₀))) :=
    scaledExp_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hlim)
  have hne : ∀ᶠ j in atTop, l (ρ j) ≠ 0 := Eventually.of_forall (fun j => (hlpos (ρ j)).ne')
  have htW := cost_first_limit x (strict_radial_mem_injectivity hw (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)) ξ (tendsto_const_nhds (x := exp x ((1/2:ℝ)•w)))
      (hl.comp hρ.tendsto_atTop) hne
  have htA := cost_first_limit x (strict_radial_mem_injectivity ha₀.1 (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)) ξ hz (hl.comp hρ.tendsto_atTop) hne
  have hineq (j : ℕ) : 0 ≤
      (cost (p (ρ j)) (exp x ((1/2:ℝ)•w))-cost x (exp x ((1/2:ℝ)•w)))/l (ρ j) -
      s*((cost (p (ρ j)) (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))-
        cost x (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j))))/l (ρ j)) := by
    have h0 := hmin (p (ρ j))
    have h1 := shortened_upper_difference hw (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1) (p (ρ j))
    have h2 := activeSupport_le y h (p (ρ j)) (ha (ρ j)) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1) x
    simp only [activeSupport] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hs.le
    have hpos : 0 ≤ (cost (p (ρ j)) (exp x ((1/2:ℝ)•w))-cost x (exp x ((1/2:ℝ)•w)))-
        s*(cost (p (ρ j)) (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))-cost x (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))) := by
      norm_num at h1 h3
      nlinarith
    simpa only [sub_div,mul_div_assoc] using div_nonneg hpos (hlpos (ρ j)).le
  have hlim' := htW.sub (htA.const_mul s)
  have hle := ge_of_tendsto hlim' (Eventually.of_forall hineq)
  simp only [inner_smul_left,conj_trivial] at hle
  refine ⟨a₀,ha₀,?_⟩
  linarith

 theorem closed_convex_mem_of_directions {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E}
    (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty) {u : E}
    (hu : ∀ ξ : E, ∃ a ∈ K, inner ℝ u ξ ≤ inner ℝ a ξ) : u ∈ K := by
  obtain ⟨v,hv,hm⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hc u
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hc hv).mp hm
  obtain ⟨a,ha,h⟩ := hu (u-v)
  have hp := hproj a ha
  rw [inner_sub_right,real_inner_comm a (u-v),real_inner_comm v (u-v)] at hp
  have hnorm : ‖u-v‖^2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq,inner_sub_left]
    linarith
  have heq : u = v := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u-v)]))
  exact heq ▸ hv

 theorem minimizing_pole_capture (y : ι → M) (h : ι → ℝ)
    {x : M} {w : TangentSpace (model n) x} (hw : w ∈ minimizingDomain x)
    {s : ℝ} (hs : 0 < s)
    (hmin : ∀ z, cost x (exp x w) + s*finitePotential y h x ≤
      cost z (exp x w) + s*finitePotential y h z) :
    s⁻¹ • w ∈ activeHull y h x := by
  let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
    VectorBundle.finiteDimensional ℝ (Model n) _ x
  let : CompleteSpace (TangentSpace (model n) x) := FiniteDimensional.complete ℝ _
  have hcl : IsClosed (activeHull (n := n) y h x) :=
    (tangentHull_closed (activeGraph_compact (n := n) y h)).preimage
      (FiberBundle.continuous_totalSpaceMk (Model n) (TangentSpace (model n)) x)
  apply closed_convex_mem_of_directions hcl (convex_convexHull ℝ _)
    ((activeVelocities_nonempty (n := n) y h x).mono (subset_convexHull ℝ _))
  intro ξ
  obtain ⟨a,ha,h⟩ := minimizing_pole_direction y h hw hs hmin ξ
  refine ⟨a,subset_convexHull ℝ _ ha,?_⟩
  simp only [inner_smul_left,conj_trivial]
  have hh := mul_le_mul_of_nonneg_left h (inv_pos.mpr hs).le
  simpa only [← mul_assoc,inv_mul_cancel₀ hs.ne',one_mul] using hh

 theorem activeHull_exp_surjective_oai (y : ι → M) (h : ι → ℝ)
    {s : ℝ} (hs : 0 < s) (z : M) :
    ∃ x : M, ∃ b ∈ activeHull (n := n) y h x, exp x (s•b) = z := by
  let : Nonempty M := ⟨z⟩
  have hc : Continuous (fun x : M => cost x z+s*finitePotential y h x) :=
    ((cost_continuous (M := M)).comp (continuous_id.prodMk continuous_const)).add
      ((finitePotential_continuous y h).const_mul s)
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hc.continuousOn
  obtain ⟨w,hw,hn⟩ := exists_minimizing_vector (n := n) x z
  have hwm : w ∈ minimizingDomain x := by
    change dist x (exp x w) = ‖w‖
    rw [hw,hn]
  have hmin : ∀ x', cost x (exp x w)+s*finitePotential y h x ≤
      cost x' (exp x w)+s*finitePotential y h x' := by
    intro x'
    rw [hw]
    exact hx (mem_univ x')
  refine ⟨x,s⁻¹•w,minimizing_pole_capture y h hwm hs hmin,?_⟩
  simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hw

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.activeHull_exp_surjective_oai.{u_1, u_2} := @OAI.WeakMTWGlobalSupport.WeakMTW.activeHull_exp_surjective_oai.{u_1, u_2}
