-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.critical_collision_sequence_false
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:04:39.482761+00:00
-- url     : https://prove2.me/submissions/8ae0838d-2843-4f19-82a3-6aff7c134668

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_exists_of_nonconjugate
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_collision_limits
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_collision_strict_gap
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_nonconjugate_of_mem_injectivity

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
 theorem finitePotential_continuous (y : ι → M) (h : ι → ℝ) : Continuous (finitePotential y h) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  exact continuous_const.sub ((continuous_id.dist continuous_const).pow 2 |>.div_const 2)

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
-- module Solutions.OAIQW_WeakMTW.Support_CollisionTangentCoordinates
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
  [IsRiemannianManifold (model n) M]

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem tangentCoordinateEquiv_apply (x p : M) (hp : p ∈ (chartAt (Model n) x).source)
    (v : TangentSpace (model n) p) :
    tangentCoordinateEquiv x p hp v = (stateChart x (⟨p,v⟩ : TangentBundle (model n) M)).2 := rfl

 theorem tangentCoordinateEquiv_center (x : M) (v : TangentSpace (model n) x) :
    tangentCoordinateEquiv x x (mem_chart_source (Model n) x) v = tangentChartLinear x v :=
  (tangentChartLinear_eq x v).symm

 theorem stateChart_bary (x p : M) (hp : p ∈ (chartAt (Model n) x).source)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) p) (θ : κ → ℝ) :
    (stateChart x (⟨p,∑ i, θ i • a i⟩ : TangentBundle (model n) M)).2 =
      ∑ i, θ i • (stateChart x (⟨p,a i⟩ : TangentBundle (model n) M)).2 := by
  change tangentCoordinateEquiv x p hp (∑ i,θ i•a i) = ∑ i,θ i•tangentCoordinateEquiv x p hp (a i)
  simp only [map_sum,map_smul]

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
-- module Solutions.OAIQW_WeakMTW.Support_ActiveRepresentation
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
  {ι : Type*} [Fintype ι] [Nonempty ι]

 omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
   (fun x : M => TangentSpace (model n) x)] [IsRiemannianManifold (model n) M]
   [CompactSpace M] in
 theorem activeRepresentation_exists (y : ι → M) (h : ι → ℝ)
    {p : TangentBundle (model n) M} (hp : p ∈ activeHullGraph y h) :
    Nonempty (ActiveRepresentation y h p) := by
  let : FiniteDimensional ℝ (TangentSpace (model n) p.1) :=
    VectorBundle.finiteDimensional ℝ (Model n) _ p.1
  obtain ⟨a,θ,ha,hθ,hs,hb⟩ := ConvexRepresentation.fixed_size hp
    (show Module.finrank ℝ (TangentSpace (model n) p.1)+1 ≤ Module.finrank ℝ (Model n)+1 by
      rw [VectorBundle.finrank_eq ℝ (Model n) (TangentSpace (model n)) p.1])
  exact ⟨⟨a,θ,ha,hθ,hs,hb⟩⟩

 theorem activeRepresentation_subseq (y : ι → M) (h : ι → ℝ)
    {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (R : ∀ j, ActiveRepresentation y h (p j)) :
    ∃ R₀ : ActiveRepresentation y h p₀, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      (∀ i, Tendsto (fun j => (R (ρ j)).θ i) atTop (𝓝 (R₀.θ i))) ∧
      (∀ i, Tendsto (fun j => (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M))
        atTop (𝓝 ⟨p₀.1,R₀.a i⟩)) := by
  let := tangentBundle_firstCountable (n := n) (M := M)
  let D : Set ((ActiveIndex n → ℝ) × (ActiveIndex n → TangentBundle (model n) M)) :=
    {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1} ×ˢ {A | ∀ i, A i ∈ activeGraph y h}
  have hsimplex : IsCompact {θ : ActiveIndex n → ℝ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1} := by
    exact isCompact_stdSimplex ℝ (ActiveIndex n)
  have hD : IsCompact D := hsimplex.prod
    (isCompact_pi_infinite (fun _ : ActiveIndex n => activeGraph_compact y h))
  obtain ⟨⟨θ,A⟩,hmem,ρ,hρ,hlim⟩ := hD.tendsto_subseq (fun j =>
    show ((R j).θ,fun i => (⟨(p j).1,(R j).a i⟩ : TangentBundle (model n) M)) ∈ D from
      ⟨⟨(R j).nonneg,(R j).sum_one⟩,(R j).active⟩)
  have hθ (i : ActiveIndex n) : Tendsto (fun j => (R (ρ j)).θ i) atTop (𝓝 (θ i)) :=
    ((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hlim
  have hA (i : ActiveIndex n) : Tendsto
      (fun j => (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M)) atTop (𝓝 (A i)) :=
    ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp hlim
  have hbcont : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  have hpbase : Tendsto (fun j => (p (ρ j)).1) atTop (𝓝 p₀.1) :=
    hbcont.continuousAt.tendsto.comp (hp.comp hρ.tendsto_atTop)
  have hbase (i : ActiveIndex n) : (A i).1 = p₀.1 := by
    have hlimbase := (hbcont.tendsto (A i)).comp (hA i)
    change Tendsto (fun j => (p (ρ j)).1) atTop (𝓝 (A i).1) at hlimbase
    exact tendsto_nhds_unique hlimbase hpbase
  have hap (i : ActiveIndex n) : ∃ v : TangentSpace (model n) p₀.1,
      A i = (⟨p₀.1,v⟩ : TangentBundle (model n) M) := by
    rcases he : A i with ⟨x,v⟩
    have hx : x = p₀.1 := by simpa only [he] using hbase i
    subst x
    exact ⟨v,rfl⟩
  choose a haeq using hap
  have ha (i : ActiveIndex n) : a i ∈ activeVelocities y h p₀.1 := by
    have hh : A i ∈ activeGraph y h := hmem.2 i
    rw [haeq i] at hh
    exact hh
  have hA' (i : ActiveIndex n) : Tendsto
      (fun j => (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M))
      atTop (𝓝 ⟨p₀.1,a i⟩) := by rw [← haeq i]; exact hA i
  have hbary : ∑ i, θ i • a i = p₀.2 := by
    let c := stateChart (E := Model n) p₀.1
    have hpS : p₀ ∈ c.source := (stateChart_source p₀.1 p₀).mpr (mem_chart_source (Model n) p₀.1)
    have hcP := (c.continuousAt hpS).tendsto.comp (hp.comp hρ.tendsto_atTop)
    have hcA (i : ActiveIndex n) : Tendsto
        (fun j => (c (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M)).2)
        atTop (𝓝 ((c (⟨p₀.1,a i⟩ : TangentBundle (model n) M)).2)) := by
      have hAiS : (⟨p₀.1,a i⟩ : TangentBundle (model n) M) ∈ c.source :=
        (stateChart_source p₀.1 _).mpr (mem_chart_source (Model n) p₀.1)
      have htmp := (c.continuousAt hAiS).tendsto.comp (hA' i)
      exact continuous_snd.continuousAt.tendsto.comp htmp
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => (hθ i).smul (hcA i))
    have hpSrc : ∀ᶠ j in atTop, p (ρ j) ∈ c.source :=
      (hp.comp hρ.tendsto_atTop) (c.open_source.mem_nhds hpS)
    have hsum' : Tendsto (fun j => ∑ i, (R (ρ j)).θ i •
        (c (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M)).2)
        atTop (𝓝 ((c p₀).2)) := by
      apply (continuous_snd.continuousAt.tendsto.comp hcP).congr'
      filter_upwards [hpSrc] with j hj
      rw [← stateChart_bary p₀.1 (p (ρ j)).1 ((stateChart_source p₀.1 _).mp hj), (R (ρ j)).bary]
      rfl
    have heq := tendsto_nhds_unique hsum hsum'
    apply (tangentCoordinateEquiv p₀.1 p₀.1 (mem_chart_source (Model n) p₀.1)).injective
    simpa only [map_sum,map_smul,tangentCoordinateEquiv_apply] using heq
  exact ⟨⟨a,θ,ha,hmem.1.1,hmem.1.2,hbary⟩,ρ,hρ,hθ,hA'⟩

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

end
end WeakMTW
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

omit [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem mulState_injective {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (mulState (E := Model n) (M := M) s) := by
  intro p q he
  have hi := congrArg (mulState s⁻¹) he
  change (⟨p.1, s⁻¹ • (s • p.2)⟩ : TangentBundle (model n) M) =
    (⟨q.1, s⁻¹ • (s • q.2)⟩ : TangentBundle (model n) M) at hi
  simpa only [inv_smul_smul₀ hs] using hi

 theorem branch_collision_base_ne {x z : M} (B : ActionBranch (n := n) x z)
    {p q : TangentBundle (model n) M} {s : ℝ} (hs : s ≠ 0)
    (hp : mulState s p ∈ (stateChart x).source)
    (hq : mulState s q ∈ (stateChart x).source)
    (hpB : stateChart x (mulState s p) ∈ B.coord.source)
    (hqB : stateChart x (mulState s q) ∈ B.coord.source)
    (he : exp p.1 (s•p.2) = exp q.1 (s•q.2)) (hne : p ≠ q) : p.1 ≠ q.1 := by
  intro hb
  apply hne
  apply mulState_injective hs
  apply (stateChart x).injOn hp hq
  apply B.coord.injOn hpB hqB
  rw [B.map_eq, pairExpCoordinates_state x z _ hp, pairExpCoordinates_state x z _ hq]
  simp only [mulState]
  exact Prod.ext (congrArg (chartAt (Model n) x) hb) (congrArg (chartAt (Model n) z) he)

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

 theorem normalized_separation_subseq {x q : ℕ → E} {x₀ : E}
    (_hx : Tendsto x atTop (𝓝 x₀)) (_hq : Tendsto q atTop (𝓝 x₀))
    (hne : ∀ᶠ j in atTop, q j ≠ x j) :
    ∃ e : E, ‖e‖ = 1 ∧ ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => NormedSpace.normalize (q (ρ j)-x (ρ j))) atTop (𝓝 e) := by
  have hb (j : ℕ) : NormedSpace.normalize (q j-x j) ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    by_cases h : q j-x j = 0
    · simp [h]
    · rw [NormedSpace.norm_normalize h]
  obtain ⟨e,he,ρ,hρ,hlim⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hb
  refine ⟨e,?_,ρ,hρ,hlim⟩
  apply tendsto_nhds_unique hlim.norm
  apply tendsto_const_nhds.congr'
  filter_upwards [hρ.tendsto_atTop hne] with j hj
  exact (NormedSpace.norm_normalize (sub_ne_zero.mpr hj)).symm

end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CriticalCollision
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

 theorem critical_collision_sequence_false_oai (y : ι → M) (h : ι → ℝ)
    (hMTW : HasWeakMTW (n := n) (M := M))
    {p q : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto (fun j => (q j).1) atTop (𝓝 p₀.1))
    {sⱼ : ℕ → ℝ} {s : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
    (hqp : Tendsto (fun j => mulState (sⱼ j) (q j)) atTop (𝓝 (mulState s p₀)))
    (hpos : ∀ᶠ j in atTop, 0 < sⱼ j) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hg : ∀ j, p j ∈ activeHullGraph y h)
    (hne : ∀ᶠ j in atTop, p j ≠ q j)
    (hcollision : ∀ᶠ j in atTop, exp (p j).1 (sⱼ j•(p j).2) = exp (q j).1 (sⱼ j•(q j).2))
    (hvalue : ∀ᶠ j in atTop, scaledPoleValue y h (sⱼ j) (q j) ≤ scaledPoleValue y h (sⱼ j) (p j))
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ activeHull (n := n) y h p₀.1, r•a ∈ injectivityDomain p₀.1)
    (hn : Nonconjugate p₀.1 (s•p₀.2)) : False := by
  classical
  let ℓ := (s+1)/2
  have hsℓ : s < ℓ := by dsimp [ℓ]; linarith
  have hℓ : 0 < ℓ := lt_of_le_of_lt hs0 hsℓ
  have hℓ₁ : ℓ < 1 := by dsimp [ℓ]; linarith
  obtain ⟨B,hB⟩ := ActionBranch.exists_of_nonconjugate hn
  have hpS : mulState s p₀ ∈ (stateChart p₀.1).source :=
    (stateChart_source p₀.1 _).mpr (mem_chart_source (Model n) p₀.1)
  have hpp := tangentScale_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hp)
  have hBp := B.eventually_source hpp hpS hB
  have hBq := B.eventually_source hqp hpS hB
  have hbasene : ∀ᶠ j in atTop,
      chartAt (Model n) p₀.1 (q j).1 ≠ chartAt (Model n) p₀.1 (p j).1 := by
    filter_upwards [hBp,hBq,hpos,hcollision,hne] with j hjp hjq hjs hjc hjn
    have hnb := branch_collision_base_ne B hjs.ne' hjp.1 hjq.1 hjp.2 hjq.2 hjc hjn
    intro he
    exact hnb ((chartAt (Model n) p₀.1).injOn
      ((stateChart_source p₀.1 _).mp hjp.1) ((stateChart_source p₀.1 _).mp hjq.1) he.symm)
  have hxq : Tendsto (fun j => chartAt (Model n) p₀.1 (q j).1) atTop (𝓝 (chartAt (Model n) p₀.1 p₀.1)) :=
    ((chartAt (Model n) p₀.1).continuousAt (mem_chart_source (Model n) p₀.1)).tendsto.comp hq
  obtain ⟨e,he,σ,hσ,hd⟩ := MovingTaylor.normalized_separation_subseq (base_chart_limit hp) hxq hbasene
  let R : ∀ j, ActiveRepresentation y h (p j) := fun j => Classical.choice (activeRepresentation_exists y h (hg j))
  obtain ⟨R₀,ρ,hρ,hθ,ha⟩ := activeRepresentation_subseq y h (hp.comp hσ.tendsto_atTop) (fun j => R (σ j))
  let τ := σ ∘ ρ
  have hτ : StrictMono τ := hσ.comp hρ
  have hCi (i : ActiveIndex n) : ℓ•R₀.a i ∈ injectivityDomain p₀.1 :=
    strict_radial_mem_injectivity (R₀.active i).1 hℓ.le hℓ₁
  choose C hC using fun i => ActionBranch.exists_of_nonconjugate (nonconjugate_of_mem_injectivity p₀.1 (hCi i))
  have hlim := branch_collision_limits y h (hp.comp hτ.tendsto_atTop) (hq.comp hτ.tendsto_atTop)
    (hs.comp hτ.tendsto_atTop) (hqp.comp hτ.tendsto_atTop)
    (hτ.tendsto_atTop hpos) hℓ hℓ₁ (hτ.tendsto_atTop hcollision) (hτ.tendsto_atTop hvalue)
    (fun j => R (τ j)) R₀ hθ ha B hB C hC (hd.comp hρ.tendsto_atTop) (hτ.tendsto_atTop hbasene)
  let T := tangentCoordinateEquiv p₀.1 p₀.1 (mem_chart_source (Model n) p₀.1)
  let ξ := T.symm e
  have heq : tangentChartLinear p₀.1 ξ = e := by
    rw [← tangentCoordinateEquiv_center]
    exact T.apply_symm_apply e
  have hξ : ξ ≠ 0 := by
    intro hz
    have he0 : e = 0 := by rw [← heq,hz,map_zero]
    rw [he0,norm_zero] at he
    norm_num at he
  rw [← heq] at hlim
  have hgap := collision_strict_gap y h hMTW R₀ hξ hs0 hsℓ hℓ₁ hbelow B hB C hC hlim.1
  exact (not_lt_of_ge hlim.2) hgap

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.critical_collision_sequence_false_oai.{u_1, u_2} := @OAI.WeakMTWGlobalSupport.WeakMTW.critical_collision_sequence_false_oai.{u_1, u_2}
