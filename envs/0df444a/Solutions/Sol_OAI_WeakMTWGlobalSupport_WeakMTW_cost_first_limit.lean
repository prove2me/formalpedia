-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.cost_first_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:03:03.349388+00:00
-- url     : https://prove2.me/submissions/44f3e9d5-34c7-4bd6-b9d7-b9a194c115eb

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_minimizing_vector
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_initialCost_geometry
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_pairExpCoordinates_local_inverse

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

 theorem baseExp_continuous : Continuous (baseExp (n := n) (M := M)) :=
  (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.prodMk exp_total_smooth.continuous

 theorem totalMinimizingSet_closed : IsClosed (totalMinimizingSet (n := n) (M := M)) :=
  isClosed_eq ((contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.dist exp_total_smooth.continuous)
    tangent_norm_continuous

 theorem minimizing_states_near_unique (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) {U : Set (TangentBundle (model n) M)}
    (hU : IsOpen U) (hvU : (⟨x,v⟩ : TangentBundle (model n) M) ∈ U) :
    ∀ᶠ xy : M × M in 𝓝 (x,exp x v), ∀ p ∈ totalMinimizingSet,
      baseExp p = xy → p ∈ U := by
  obtain ⟨V,hV,hxV,K,hK,hbound⟩ := locally_compact_tangent_bound (n := n) x (Metric.diam (univ : Set M))
  let L := (K ∩ totalMinimizingSet (n := n) (M := M)) \ U
  have hL : IsCompact L := (hK.inter_right totalMinimizingSet_closed).diff hU
  have hC := (hL.image baseExp_continuous).isClosed
  have hnot : (x,exp x v) ∉ baseExp '' L := by
    rintro ⟨⟨b,w⟩,hw,he⟩
    have hb : b = x := congrArg Prod.fst he
    subst b
    have hex : exp x w = exp x v := congrArg Prod.snd he
    have hm : w ∈ minimizingDomain x := hw.1.2
    have hh := minimizing_vector_unique_of_injectivity hv hm hex.symm
    exact hw.2 (by simpa only [← hh] using hvU)
  have hVp : ∀ᶠ xy : M × M in 𝓝 (x,exp x v), xy.1 ∈ V :=
    continuousAt_fst.preimage_mem_nhds (hV.mem_nhds hxV)
  filter_upwards [hC.isOpen_compl.mem_nhds hnot,hVp] with xy hxy hVxy
  intro p hp he
  have hpn : ‖p.2‖ ≤ Metric.diam (univ : Set M) := by
    rw [← show dist p.1 (exp p.1 p.2) = ‖p.2‖ from hp]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have hpV : p.1 ∈ V := by simpa only [← he,baseExp] using hVxy
  have hpK := hbound p hpV hpn
  by_contra hn
  exact hxy ⟨p,⟨⟨hpK,hp⟩,hn⟩,he⟩

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

 theorem cost_coord_eq_interior_inverse (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) =
      pairExpCoordinates (n := n) x (exp x v))
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source) :
    ∀ᶠ q : Model n × Model n in
      𝓝 (chartAt (Model n) x x,chartAt (Model n) (exp x v) (exp x v)),
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) (exp x v)).symm q.2) =
        metric x (e.symm q).1 (e.symm q).2 (e.symm q).2 / 2 := by
  let c := chartAt (Model n) x
  let d := chartAt (Model n) (exp x v)
  let a := c x
  let b := d (exp x v)
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hy : exp x v ∈ d.source := mem_chart_source (Model n) (exp x v)
  have ha : a ∈ c.target := c.map_source hx
  have hb : b ∈ d.target := d.map_source hy
  have hvS : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr hx
  let U := (stateChart x).source ∩ stateChart x ⁻¹' e.source
  have hU : IsOpen U :=
    (stateChart x).continuousOn.isOpen_inter_preimage (stateChart x).open_source e.open_source
  have hvU : (⟨x,v⟩ : TangentBundle (model n) M) ∈ U := ⟨hvS,hev⟩
  have hnear := minimizing_states_near_unique x hv hU hvU
  have hpair : Tendsto (fun q : Model n × Model n => (c.symm q.1,d.symm q.2))
      (𝓝 (a,b)) (𝓝 (x,exp x v)) := by
    have hc := ContinuousAt.comp (x := (a,b)) (f := Prod.fst) (g := c.symm)
      (c.symm.continuousAt ha) (continuousAt_fst : ContinuousAt (fun q : Model n × Model n => q.1) (a,b))
    have hd := ContinuousAt.comp (x := (a,b)) (f := Prod.snd) (g := d.symm)
      (d.symm.continuousAt hb) (continuousAt_snd : ContinuousAt (fun q : Model n × Model n => q.2) (a,b))
    simpa only [Function.comp_def,Prod.fst,Prod.snd,a,b,c.left_inv hx,d.left_inv hy] using (hc.prodMk hd).tendsto
  have hqt : ∀ᶠ q : Model n × Model n in 𝓝 (a,b), q.1 ∈ c.target ∧ q.2 ∈ d.target :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (c.open_target.mem_nhds ha))
      (continuousAt_snd.preimage_mem_nhds (d.open_target.mem_nhds hb))
  filter_upwards [hpair hnear,hqt] with q hq hqt
  obtain ⟨w,hew,hnw⟩ := exists_minimizing_vector (n := n) (c.symm q.1) (d.symm q.2)
  let p : TangentBundle (model n) M := ⟨c.symm q.1,w⟩
  have hpM : p ∈ totalMinimizingSet := by
    change dist (c.symm q.1) (exp (c.symm q.1) w) = ‖w‖
    rw [hew,hnw]
  have hpE : baseExp p = (c.symm q.1,d.symm q.2) := Prod.ext rfl hew
  have hpU : p ∈ U := hq p hpM hpE
  have heq : e (stateChart x p) = q := by
    rw [he,pairExpCoordinates_state x (exp x v) p hpU.1]
    change (c (c.symm q.1),d (exp (c.symm q.1) w)) = q
    rw [hew,c.right_inv hqt.1,d.right_inv hqt.2]
  have hlog : e.symm q = stateChart x p := by
    rw [← heq,e.left_inv hpU.2]
  rw [hlog]
  have hpS : p.1 ∈ c.source := (stateChart_source x _).mp hpU.1
  have hm := stateChart_pairing x p.1 hpS p.2 p.2
  dsimp only [cost]
  rw [← hnw]
  congr 1
  exact (show ‖p.2‖^2 = metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 from
    by simpa only [real_inner_self_eq_norm_sq] using hm.symm)

 theorem cost_coord_smooth_interior (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (fun q : Model n × Model n =>
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) (exp x v)).symm q.2))
      (chartAt (Model n) x x,chartAt (Model n) (exp x v) (exp x v)) := by
  let y := exp x v
  let q := (chartAt (Model n) x x,chartAt (Model n) y y)
  obtain ⟨e,he,hev,hes,hei⟩ := pairExpCoordinates_local_inverse x y hv (mem_chart_source (Model n) y)
  have heq : e (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) = q := by
    rw [he,pairExpCoordinates_vertical]
  have hq : q ∈ e.target := heq ▸ e.map_source hev
  have hν : ContDiffAt ℝ ∞ e.symm q := (hei q hq).contDiffAt (e.open_target.mem_nhds hq)
  have hνT : (e.symm q).1 ∈ (chartAt (Model n) x).target :=
    (stateChart_target x _).mp (hes (e.map_target hq)).1
  have hG : ContDiffAt ℝ ∞ (fun p : Model n × Model n => metric x (e.symm p).1) q :=
    ContDiffAt.comp (f := fun p => (e.symm p).1) (g := metric x) q
      ((metric_smooth x _ hνT).contDiffAt ((chartAt (Model n) x).open_target.mem_nhds hνT)) hν.fst
  have hs : ContDiffAt ℝ ∞ (fun p : Model n × Model n =>
      metric x (e.symm p).1 (e.symm p).2 (e.symm p).2 / 2) q :=
    ((hG.clm_apply hν.snd).clm_apply hν.snd).div_const 2
  exact hs.congr_of_eventuallyEq (cost_coord_eq_interior_inverse x hv e he hev)

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

end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CostFirstTaylor
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

 theorem cost_first_limit_oai (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x)
    {z : ℕ → M} (hz : Tendsto z atTop (𝓝 (exp x v)))
    {l : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0)) (hne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (cost ((chartAt (Model n) x).symm
      (chartAt (Model n) x x + l j • tangentChartLinear x ξ)) (z j) - cost x (z j)) / l j)
      atTop (𝓝 (-inner ℝ v ξ)) := by
  let c := chartAt (Model n) x
  let d := chartAt (Model n) (exp x v)
  let f : Model n × Model n → ℝ := fun q => cost (c.symm q.1) (d.symm q.2)
  let a := c x
  let b := d (exp x v)
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hy : exp x v ∈ d.source := mem_chart_source (Model n) (exp x v)
  have hf : ContDiffAt ℝ ∞ f (a,b) := cost_coord_smooth_interior x hv
  have hd := (d.continuousAt hy).tendsto.comp hz
  have hlim := MovingTaylor.param_first_limit hf (tendsto_const_nhds (x := a))
    (tendsto_const_nhds (x := tangentChartLinear x ξ)) hd hl hne
  have hs : (fun q : Model n => f (q,b)) = initialCost x (exp x v) := by
    funext q
    simp only [f,b,d.left_inv hy,initialCost,c]
  have hg : HasFDerivAt f (fderiv ℝ f (a,b)) (a,b) :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  have hpair : HasFDerivAt (fun q : Model n => (q,b))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const b a)
  have hg' := hg.comp a hpair
  have hgd := hg'.fderiv
  rw [show (f ∘ fun q => (q,b)) = initialCost x (exp x v) from hs] at hgd
  have hder : fderiv ℝ f (a,b) (tangentChartLinear x ξ,0) = -inner ℝ v ξ := by
    have h := congrArg (fun L : Model n →L[ℝ] ℝ => L (tangentChartLinear x ξ)) hgd
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply,zero_apply] at h
    rw [(initialCost_geometry x hv).2.1] at h
    have hm : metric x (chartAt (Model n) x x) (tangentChartLinear x v) (tangentChartLinear x ξ) = inner ℝ v ξ :=
      metric_chart_pair x x (mem_chart_source (Model n) x) v ξ
    rw [hm] at h
    exact h.symm
  rw [hder] at hlim
  apply hlim.congr'
  have hnear := hz (d.open_source.mem_nhds hy)
  filter_upwards [hnear] with j hj
  simp only [f,a,Function.comp_def,c.left_inv hx,d.left_inv hj]
  rfl

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.cost_first_limit_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.cost_first_limit_oai.{u_1}
