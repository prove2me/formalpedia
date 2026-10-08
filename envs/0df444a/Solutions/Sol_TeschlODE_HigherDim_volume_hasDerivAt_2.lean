-- Prove2me | solution 2 for TeschlODE.HigherDim.volume_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-07T12:01:11.464908+00:00
-- url     : https://prove2.me/submissions/9341339b-6e97-438e-a4d8-1772a3fdc31f

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Theorems.Thm_AnosovPlugs_exists_flow_contDiffOn_of_lipschitz
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_divergence


open Set

namespace LVF
open TeschlODE.HigherDim

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem flow_mem {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω) {t : ℝ} (ht : t ∈ I x) : Φ t x ∈ Ω :=
  (hΦ x hx).1.2.2.1 t ht

theorem zero_mem {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω) : (0 : ℝ) ∈ I x :=
  (hΦ x hx).2.1

theorem flow_zero {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω) : Φ 0 x = x :=
  (hΦ x hx).2.2.1

theorem mem_of_uIcc {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω) {t s : ℝ} (ht : t ∈ I x)
    (hs : s ∈ uIcc 0 t) : s ∈ I x :=
  (hΦ x hx).1.2.1.uIcc_subset (zero_mem hΦ hx) ht hs

/-- Group law: `Φ b (Φ a x) = Φ (a + b) x`. -/
theorem flow_add {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω) {a b : ℝ} (ha : a ∈ I x)
    (hab : a + b ∈ I x) : b ∈ I (Φ a x) ∧ Φ b (Φ a x) = Φ (a + b) x := by
  obtain ⟨⟨hJo, hJc, hJm, hJd⟩, -, -, -⟩ := hΦ x hx
  have hy : Φ a x ∈ Ω := hJm a ha
  have hcur : IsIntegralCurve f Ω ((fun s => s + a) ⁻¹' I x) (fun s => Φ (s + a) x) := by
    refine ⟨hJo.preimage (continuous_add_const a), ?_, fun s hs => hJm _ hs, fun s hs => ?_⟩
    · exact hJc.preimage_mono (fun u v huv => by linarith)
    · exact (hJd (s + a) hs).comp_add_const s a
  have h0 : (0 : ℝ) ∈ (fun s => s + a) ⁻¹' I x := by simpa using ha
  obtain ⟨hsub, heq⟩ := (hΦ (Φ a x) hy).2.2.2 _ _ hcur h0 (by simp)
  have hb : b ∈ (fun s => s + a) ⁻¹' I x := by simpa [add_comm] using hab
  refine ⟨hsub hb, ?_⟩
  rw [← heq b hb, add_comm]

/-- `Φ t` is injective on the set of points alive at time `t`. -/
theorem flow_injOn {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) (t : ℝ) : InjOn (Φ t) {x | x ∈ Ω ∧ t ∈ I x} := by
  rintro x ⟨hx, htx⟩ y ⟨hy, hty⟩ hxy
  have h1 := (flow_add hΦ hx htx (b := -t) (by simpa using zero_mem hΦ hx)).2
  have h2 := (flow_add hΦ hy hty (b := -t) (by simpa using zero_mem hΦ hy)).2
  simp only [add_neg_cancel] at h1 h2
  rw [flow_zero hΦ hx] at h1
  rw [flow_zero hΦ hy] at h2
  rw [← h1, ← h2, hxy]

theorem continuousOn_traj {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω) : ContinuousOn (fun s => Φ s x) (I x) :=
  fun s hs => ((hΦ x hx).1.2.2.2 s hs).continuousAt.continuousWithinAt

end LVF


open Set

namespace LVF

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The determinant on `E →L[ℝ] E` as a polynomial in the matrix entries. -/
theorem det_eq_sum (T : E →L[ℝ] E) :
    T.det = ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)), (Equiv.Perm.sign σ : ℝ) *
      ∏ i, (Module.finBasis ℝ E).equivFunL (T ((Module.finBasis ℝ E) i)) (σ i) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.finBasis ℝ E), Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [LinearMap.toMatrix_apply]

theorem differentiable_det : Differentiable ℝ (fun T : E →L[ℝ] E => T.det) := by
  have : (fun T : E →L[ℝ] E => T.det) = fun T => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      (Equiv.Perm.sign σ : ℝ) *
        ∏ i, (Module.finBasis ℝ E).equivFunL (T ((Module.finBasis ℝ E) i)) (σ i) := by
    funext T; exact det_eq_sum T
  rw [this]
  have hl : ∀ i j, Differentiable ℝ
      (fun T : E →L[ℝ] E => (Module.finBasis ℝ E).equivFunL (T ((Module.finBasis ℝ E) i)) j) := by
    intro i j
    have h1 : Differentiable ℝ (fun T : E →L[ℝ] E => T ((Module.finBasis ℝ E) i)) :=
      (ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).differentiable
    have h2 := ((Module.finBasis ℝ E).equivFunL.differentiable.comp h1)
    exact (differentiable_apply j).comp h2
  refine Differentiable.fun_sum fun σ _ => ?_
  refine (differentiable_const _).mul ?_
  intro T
  classical
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun i (T : E →L[ℝ] E) => (Module.finBasis ℝ E).equivFunL (T ((Module.finBasis ℝ E) i)) (σ i))
    fun i _ => (hl i (σ i) T).hasFDerivAt).differentiableAt

theorem det_one_add_smul_clm (P : E →L[ℝ] E) : ∃ Q : Polynomial ℝ, ∀ r : ℝ,
    (1 + r • P).det = 1 + LinearMap.trace ℝ E P * r + Q.eval r * r ^ 2 := by
  set b := Module.finBasis ℝ E
  refine ⟨(Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
    (LinearMap.toMatrix b b (P : E →ₗ[ℝ] E)).map Polynomial.C)).divX.divX, fun r => ?_⟩
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b,
    LinearMap.trace_eq_matrix_trace ℝ b, ← Matrix.det_one_add_smul]
  congr 1
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul,
    ContinuousLinearMap.toLinearMap_one, LinearMap.toMatrix_one]

/-- Jacobi's formula along a curve solving `M' = P ∘ M`. -/
theorem hasDerivAt_det {M : ℝ → E →L[ℝ] E} {P : E →L[ℝ] E} {s : ℝ}
    (h : HasDerivAt M (P.comp (M s)) s) :
    HasDerivAt (fun r => (M r).det) (LinearMap.trace ℝ E P * (M s).det) s := by
  have hd := (differentiable_det (E := E) (M s)).hasFDerivAt
  have h1 := hd.comp_hasDerivAt s h
  have hc : HasDerivAt (fun r : ℝ => (1 + r • P).comp (M s)) (P.comp (M s)) 0 := by
    have : (fun r : ℝ => (1 + r • P).comp (M s)) = fun r => M s + r • P.comp (M s) := by
      funext r; ext v; simp
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (P.comp (M s))).const_add (M s)
  have e0 : (1 + (0 : ℝ) • P).comp (M s) = M s := by ext v; simp
  have hd' : HasFDerivAt (fun T : E →L[ℝ] E => T.det) (fderiv ℝ (fun T : E →L[ℝ] E => T.det) (M s))
      ((1 + (0 : ℝ) • P).comp (M s)) := by rw [e0]; exact hd
  have h2 := hd'.comp_hasDerivAt (x := (0 : ℝ)) (f := fun r : ℝ => (1 + r • P).comp (M s))
    (by simpa using hc)
  obtain ⟨Q, hQ⟩ := det_one_add_smul_clm P
  have h3 : HasDerivAt (fun r : ℝ => ((1 + r • P).comp (M s)).det)
      (LinearMap.trace ℝ E P * (M s).det) 0 := by
    have : (fun r : ℝ => ((1 + r • P).comp (M s)).det) =
        fun r => (1 + LinearMap.trace ℝ E P * r + Q.eval r * r ^ 2) * (M s).det := by
      funext r
      rw [← hQ r, ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.det,
        ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    rw [this]
    have hp : HasDerivAt (fun r : ℝ => 1 + LinearMap.trace ℝ E P * r + Q.eval r * r ^ 2)
        (LinearMap.trace ℝ E P) 0 := by
      have e1 := ((hasDerivAt_id' (0 : ℝ)).const_mul (LinearMap.trace ℝ E P)).const_add 1
      have e2 := (Q.hasDerivAt 0).mul (hasDerivAt_pow 2 (0 : ℝ))
      refine (e1.add e2).congr_deriv ?_
      simp
    simpa using hp.mul_const ((M s).det)
  have := h2.unique h3
  simp only [Function.comp_def] at h1 this
  rw [this] at h1
  exact h1

end LVF


open Set Filter Topology

namespace LVF

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section Var

variable {v : E → E} {ε : ℝ} {α : E → ℝ → E}

/-- The spatial derivative of a jointly `C¹` map, expressed through the joint derivative. -/
noncomputable def Dfun (α : E → ℝ → E) (τ : ℝ) (y : E) : E →L[ℝ] E :=
  (fderiv ℝ (fun p : E × ℝ => α p.1 p.2) (y, τ)).comp ((ContinuousLinearMap.id ℝ E).prod 0)

theorem uIcc_sub {s : ℝ} (hs : s ∈ Ioo (-ε) ε) : uIcc 0 s ⊆ Ioo (-ε) ε := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩
  exact (ordConnected_Ioo).uIcc_subset h0 hs

variable (hv : ContDiff ℝ 1 v) (hα0 : ∀ x, α x 0 = x)
  (hαd : ∀ x, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (v (α x t)) t)
  (hαc : ContDiffOn ℝ 1 (fun p : E × ℝ => α p.1 p.2) (univ ×ˢ Ioo (-ε) ε))
include hαc

theorem hasFDerivAt_slice {τ : ℝ} (hτ : τ ∈ Ioo (-ε) ε) (y : E) :
    HasFDerivAt (fun y => α y τ) (Dfun α τ y) y := by
  have hO : IsOpen (univ ×ˢ Ioo (-ε) ε : Set (E × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hd : DifferentiableAt ℝ (fun p : E × ℝ => α p.1 p.2) (y, τ) :=
    (hαc.differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds ⟨mem_univ _, hτ⟩)
  have hl : HasFDerivAt (fun y : E => (y, τ)) ((ContinuousLinearMap.id ℝ E).prod 0) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const τ y)
  exact hd.hasFDerivAt.comp y hl

theorem continuousOn_Dfun :
    ContinuousOn (fun p : E × ℝ => Dfun α p.2 p.1) (univ ×ˢ Ioo (-ε) ε) := by
  have hO : IsOpen (univ ×ˢ Ioo (-ε) ε : Set (E × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hc := hαc.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have : (fun p : E × ℝ => Dfun α p.2 p.1) =
      fun p => (fderiv ℝ (fun p : E × ℝ => α p.1 p.2) p).comp
        ((ContinuousLinearMap.id ℝ E).prod 0) := by
    funext p; rfl
  rw [this]
  exact hc.clm_comp continuousOn_const

omit hαc in
include hαd in
theorem traj_cont (x : E) : ContinuousOn (α x) (Ioo (-ε) ε) :=
  fun t ht => (hαd x t ht).continuousAt.continuousWithinAt

include hαd hv in
theorem integral_eq (y : E) {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
    α y s = α y 0 + ∫ u in (0 : ℝ)..s, v (α y u) := by
  have hsub := uIcc_sub hs
  have hcont : ContinuousOn (fun u => v (α y u)) (uIcc 0 s) :=
    hv.continuous.comp_continuousOn ((traj_cont hαd y).mono hsub)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hαd y u (hsub hu))
    (hcont.intervalIntegrable)]
  abel

include hαd hv hα0 in
theorem hasDerivAt_Dfun (y₀ : E) {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
    HasDerivAt (fun s => Dfun α s y₀) ((fderiv ℝ v (α y₀ s)).comp (Dfun α s y₀)) s := by
  have hO : IsOpen (univ ×ˢ Ioo (-ε) ε : Set (E × ℝ)) := isOpen_univ.prod isOpen_Ioo
  -- the integrand and its spatial derivative
  set A : E → ℝ → E →L[ℝ] E := fun y u => (fderiv ℝ v (α y u)).comp (Dfun α u y) with hA
  have hαcont : ContinuousOn (fun p : E × ℝ => α p.1 p.2) (univ ×ˢ Ioo (-ε) ε) :=
    hαc.continuousOn
  have hAc : ContinuousOn (fun p : E × ℝ => A p.1 p.2) (univ ×ˢ Ioo (-ε) ε) := by
    have h1 : ContinuousOn (fun p : E × ℝ => fderiv ℝ v (α p.1 p.2)) (univ ×ˢ Ioo (-ε) ε) :=
      (hv.continuous_fderiv (by norm_num)).comp_continuousOn hαcont
    exact h1.clm_comp (continuousOn_Dfun hαc)
  have hAt : ∀ y, ContinuousOn (A y) (Ioo (-ε) ε) := by
    intro y
    refine hAc.comp (continuousOn_const.prodMk continuousOn_id) ?_
    intro u hu; exact ⟨mem_univ _, hu⟩
  have key : ∀ τ ∈ Ioo (-ε) ε,
      Dfun α τ y₀ = ContinuousLinearMap.id ℝ E + ∫ u in (0 : ℝ)..τ, A y₀ u := by
    intro τ hτ
    have hsub := uIcc_sub hτ
    have hK : IsCompact (Metric.closedBall y₀ 1 ×ˢ uIcc 0 τ) :=
      (isCompact_closedBall y₀ 1).prod isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (hAc.mono (fun p hp => ⟨mem_univ _, hsub hp.2⟩))
    have hG : HasFDerivAt (fun y => ∫ u in (0 : ℝ)..τ, v (α y u))
        (∫ u in (0 : ℝ)..τ, A y₀ u) y₀ := by
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (bound := fun _ => C) (F' := A) (Metric.ball_mem_nhds y₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · refine Eventually.of_forall fun y => ?_
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
        exact (hv.continuous.comp_continuousOn ((traj_cont hαd y).mono hsub)).mono
          uIoc_subset_uIcc
      · exact (hv.continuous.comp_continuousOn
          ((traj_cont hαd y₀).mono hsub)).intervalIntegrable
      · exact ((hAt y₀).mono (uIoc_subset_uIcc.trans hsub)).aestronglyMeasurable
          measurableSet_uIoc
      · refine Eventually.of_forall fun u hu y hy => hC (y, u) ⟨?_, uIoc_subset_uIcc hu⟩
        exact Metric.ball_subset_closedBall hy
      · exact intervalIntegrable_const
      · refine Eventually.of_forall fun u hu y _ => ?_
        have hu' := hsub (uIoc_subset_uIcc hu)
        exact ((hv.differentiable (by norm_num) (α y u)).hasFDerivAt).comp y
          (hasFDerivAt_slice hαc hu' y)
    have hfun : (fun y => α y τ) = fun y => y + ∫ u in (0 : ℝ)..τ, v (α y u) := by
      funext y
      rw [integral_eq hv hαd hαc y hτ, hα0]
    have h1 : HasFDerivAt (fun y => α y τ)
        (ContinuousLinearMap.id ℝ E + ∫ u in (0 : ℝ)..τ, A y₀ u) y₀ := by
      rw [hfun]; exact (hasFDerivAt_id y₀).add hG
    exact (hasFDerivAt_slice hαc hτ y₀).unique h1
  have hev : (fun s => Dfun α s y₀) =ᶠ[𝓝 s]
      fun s => ContinuousLinearMap.id ℝ E + ∫ u in (0 : ℝ)..s, A y₀ u :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) key
  have hint : IntervalIntegrable (A y₀) MeasureTheory.volume 0 s :=
    ((hAt y₀).mono (uIcc_sub hs)).intervalIntegrable
  have hI := (intervalIntegral.integral_hasDerivAt_right hint
    ((hAt y₀).stronglyMeasurableAtFilter isOpen_Ioo s hs)
    ((hAt y₀).continuousAt (Ioo_mem_nhds hs.1 hs.2))).const_add (ContinuousLinearMap.id ℝ E)
  exact hI.congr_of_eventuallyEq hev

end Var

end LVF


open Set Filter Topology

namespace LVF
open TeschlODE.HigherDim

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Cut-off of a `C¹` field near a point: a global `C¹`, Lipschitz, bounded field agreeing
with `f` on a ball. -/
theorem cutoff {f : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) {z : E}
    (hz : z ∈ Ω) : ∃ ρ > 0, Metric.ball z ρ ⊆ Ω ∧ ∃ v : E → E, ContDiff ℝ 1 v ∧
      (∃ K, LipschitzWith K v) ∧ (∃ B > 0, ∀ w, ‖v w‖ ≤ B) ∧
      ∀ w ∈ Metric.ball z ρ, v w = f w := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩ z hz
  set ρ := R / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  let χ : ContDiffBump z := ⟨ρ, 2 * ρ, hρ0, by linarith⟩
  set v : E → E := fun w => χ w • f w with hv
  have hzero : ∀ w, 2 * ρ ≤ dist w z → v w = 0 := by
    intro w hw
    have : χ w = 0 := χ.zero_of_le_dist hw
    simp [hv, this]
  have hvC : ContDiff ℝ 1 v := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : dist w z < 3 * ρ
    · have hwΩ : w ∈ Ω := hRΩ (by rw [Metric.mem_ball]; linarith)
      exact χ.contDiff.contDiffAt.smul (hf.contDiffAt (hΩ.mem_nhds hwΩ))
    · push_neg at hw
      have hev : (fun _ => (0 : E)) =ᶠ[𝓝 w] v := by
        have ho : IsOpen {u : E | 2 * ρ < dist u z} := isOpen_lt continuous_const
          (continuous_id.dist continuous_const)
        filter_upwards [ho.mem_nhds (show 2 * ρ < dist w z by linarith)] with u hu
        exact (hzero u hu.le).symm
      exact contDiffAt_const.congr_of_eventuallyEq hev.symm
  have hcs : HasCompactSupport v := by
    refine HasCompactSupport.intro (isCompact_closedBall z (2 * ρ)) fun w hw => ?_
    rw [Metric.mem_closedBall, not_le] at hw
    exact hzero w hw.le
  obtain ⟨K, hK⟩ := hvC.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hcs (by norm_num)
  obtain ⟨B, hB⟩ := hvC.continuous.bounded_above_of_compact_support hcs
  refine ⟨ρ, hρ0, fun w hw => hRΩ (Metric.ball_subset_ball (by linarith) hw), v, hvC, ⟨K, hK⟩,
    ⟨max B 0 + 1, by positivity, fun w => (hB w).trans (by linarith [le_max_left B 0])⟩, ?_⟩
  intro w hw
  have : χ w = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
  simp [hv, this]

/-- Local structure of the flow near a point of `Ω`. -/
theorem local_flow {f : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    {I : E → Set ℝ} {Φ : ℝ → E → E} (hΦ : IsMaximalFlow f Ω I Φ) {z : E} (hz : z ∈ Ω) :
    ∃ r > 0, ∃ ε > 0, ∃ D : ℝ → E → E →L[ℝ] E,
      ContinuousOn (fun p : E × ℝ => D p.2 p.1) (Metric.ball z r ×ˢ Ioo (-ε) ε) ∧
      ContinuousOn (fun p : E × ℝ => Φ p.2 p.1) (Metric.ball z r ×ˢ Ioo (-ε) ε) ∧
      ∀ y ∈ Metric.ball z r, D 0 y = ContinuousLinearMap.id ℝ E ∧
        ∀ s ∈ Ioo (-ε) ε, s ∈ I y ∧ Φ s y ∈ Ω ∧ HasFDerivAt (Φ s) (D s y) y ∧
          HasDerivAt (fun s => D s y) ((fderiv ℝ f (Φ s y)).comp (D s y)) s := by
  obtain ⟨ρ, hρ, hρΩ, v, hvC, ⟨K, hK⟩, ⟨B, hB0, hB⟩, hvf⟩ := cutoff hΩ hf hz
  obtain ⟨ε, hε, α, hα0, hαd, hαc⟩ :=
    AnosovPlugs.exists_flow_contDiffOn_of_lipschitz v hvC K hK
  set ε₁ := min ε (ρ / (2 * B)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε (by positivity)
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hJ : ∀ s ∈ Ioo (-ε₁) ε₁, s ∈ Ioo (-ε) ε := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- trajectories from the half ball stay in the ball where `v = f`
  have hstay : ∀ y ∈ Metric.ball z (ρ / 2), ∀ s ∈ Ioo (-ε₁) ε₁, α y s ∈ Metric.ball z ρ := by
    intro y hy s hs
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := α y)
      (f' := fun t => v (α y t)) (C := B) (s := Ioo (-ε) ε)
      (fun t ht => (hαd y t ht).hasDerivWithinAt) (fun t _ => hB _) (convex_Ioo _ _) h0 (hJ s hs)
    rw [hα0, sub_zero, Real.norm_eq_abs] at hmv
    have hsb : |s| < ρ / (2 * B) := by
      rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, min_le_right ε (ρ / (2 * B))]
    have h2 : B * |s| < ρ / 2 := by
      calc B * |s| < B * (ρ / (2 * B)) := by gcongr
        _ = ρ / 2 := by field_simp
    rw [Metric.mem_ball] at hy ⊢
    calc dist (α y s) z ≤ dist (α y s) y + dist y z := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := by rw [dist_eq_norm]; linarith
      _ = ρ := by ring
  -- the cut-off flow is the true flow
  have hagree : ∀ y ∈ Metric.ball z (ρ / 2), ∀ s ∈ Ioo (-ε₁) ε₁, s ∈ I y ∧ Φ s y = α y s := by
    intro y hy s hs
    have hyΩ : y ∈ Ω := hρΩ (Metric.ball_subset_ball (by linarith) hy)
    have hcur : IsIntegralCurve f Ω (Ioo (-ε₁) ε₁) (α y) := by
      refine ⟨isOpen_Ioo, ordConnected_Ioo, fun t ht => hρΩ (hstay y hy t ht), fun t ht => ?_⟩
      rw [← hvf _ (hstay y hy t ht)]
      exact hαd y t (hJ t ht)
    obtain ⟨hsub, heq⟩ := (hΦ y hyΩ).2.2.2 _ _ hcur ⟨by linarith, hε₁0⟩ (hα0 y)
    exact ⟨hsub hs, (heq s hs).symm⟩
  refine ⟨ρ / 2, by positivity, ε₁, hε₁0, Dfun α, ?_, ?_, ?_⟩
  · exact (continuousOn_Dfun hαc).mono fun p hp => ⟨mem_univ _, hJ _ hp.2⟩
  · refine (hαc.continuousOn.mono fun p hp => ⟨mem_univ _, hJ _ hp.2⟩).congr ?_
    intro p hp
    exact (hagree p.1 hp.1 p.2 hp.2).2
  intro y hy
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  refine ⟨?_, fun s hs => ?_⟩
  · have h1 := hasFDerivAt_slice hαc h0 y
    have h2 : (fun y => α y 0) = id := funext hα0
    rw [h2] at h1
    exact h1.unique (hasFDerivAt_id y)
  obtain ⟨hsI, hΦs⟩ := hagree y hy s hs
  have hyΩ : y ∈ Ω := hρΩ (Metric.ball_subset_ball (by linarith) hy)
  refine ⟨hsI, flow_mem hΦ hyΩ hsI, ?_, ?_⟩
  · have hev : (fun y => α y s) =ᶠ[𝓝 y] Φ s := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with y' hy'
      exact (hagree y' hy' s hs).2.symm
    exact (hasFDerivAt_slice hαc (hJ s hs) y).congr_of_eventuallyEq hev.symm
  · have hd := hasDerivAt_Dfun hvC hα0 hαd hαc y (hJ s hs)
    have hfe : fderiv ℝ v (α y s) = fderiv ℝ f (Φ s y) := by
      rw [hΦs]
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [Metric.isOpen_ball.mem_nhds (hstay y hy s hs)] with w hw
      exact hvf w hw
    rw [hfe] at hd
    exact hd

end LVF


open Set Filter Topology

namespace LVF
open TeschlODE.HigherDim

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem det_comp' (A B : E →L[ℝ] E) : (A.comp B).det = A.det * B.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

theorem det_id' : (ContinuousLinearMap.id ℝ E).det = 1 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]

section DivFree

variable {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}

/-- Locally, a divergence-free flow has Jacobian determinant one. -/
theorem local_det (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hΦ : IsMaximalFlow f Ω I Φ)
    (htr : ∀ w ∈ Ω, LinearMap.trace ℝ E (fderiv ℝ f w) = 0) {z : E} (hz : z ∈ Ω) :
    ∃ r > 0, ∃ ε > 0, ∀ y ∈ Metric.ball z r, ∀ s ∈ Ioo (-ε) ε,
      s ∈ I y ∧ ∃ D : E →L[ℝ] E, HasFDerivAt (Φ s) D y ∧ D.det = 1 := by
  obtain ⟨r, hr, ε, hε, D, -, -, hD⟩ := local_flow hΩ hf hΦ hz
  refine ⟨r, hr, ε, hε, fun y hy s hs => ⟨(hD y hy).2 s hs |>.1, D s y,
    ((hD y hy).2 s hs).2.2.1, ?_⟩⟩
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hder : ∀ u ∈ Ioo (-ε) ε, HasDerivAt (fun u => (D u y).det) 0 u := by
    intro u hu
    obtain ⟨-, huΩ, -, hvar⟩ := (hD y hy).2 u hu
    have := hasDerivAt_det hvar
    rwa [htr _ huΩ, zero_mul] at this
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun u => (D u y).det)
    (f' := fun _ => (0 : ℝ)) (C := 0) (s := Ioo (-ε) ε)
    (fun u hu => (hder u hu).hasDerivWithinAt) (fun _ _ => by simp) (convex_Ioo _ _) h0 hs
  rw [zero_mul, (hD y hy).1, det_id'] at hmv
  have := norm_le_zero_iff.1 hmv
  linarith [sub_eq_zero.1 this]

/-- Uniform version on a compact subset of `Ω`. -/
theorem uniform_det (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hΦ : IsMaximalFlow f Ω I Φ)
    (htr : ∀ w ∈ Ω, LinearMap.trace ℝ E (fderiv ℝ f w) = 0) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ ε > 0, ∀ w ∈ K, ∀ s, |s| < ε →
      s ∈ I w ∧ ∃ D : E →L[ℝ] E, HasFDerivAt (Φ s) D w ∧ D.det = 1 := by
  have hloc : ∀ z ∈ K, ∃ r > 0, ∃ ε > 0, ∀ y ∈ Metric.ball z r, ∀ s ∈ Ioo (-ε) ε,
      s ∈ I y ∧ ∃ D : E →L[ℝ] E, HasFDerivAt (Φ s) D y ∧ D.det = 1 :=
    fun z hz => local_det hΩ hf hΦ htr (hKΩ hz)
  choose! rf hrf εf hεf hP using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun z => Metric.ball z (rf z))
    (fun z hz => Metric.ball_mem_nhds z (hrf z hz))
  classical
  set S : Finset ℝ := insert 1 (t.image εf) with hS
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hSpos : 0 < S.min' hSne := by
    rw [Finset.lt_min'_iff]
    intro a ha
    rw [hS, Finset.mem_insert, Finset.mem_image] at ha
    rcases ha with rfl | ⟨z, hz, rfl⟩
    · norm_num
    · exact hεf z (htK z hz)
  refine ⟨S.min' hSne, hSpos, fun w hw s hs => ?_⟩
  have hw' := hcov hw
  rw [mem_iUnion₂] at hw'
  obtain ⟨z, hz, hwz⟩ := hw'
  have hle : S.min' hSne ≤ εf z :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz))
  rw [abs_lt] at hs
  exact hP z (htK z hz) w hwz s ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem mul_mem_uIcc {c t : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : c * t ∈ uIcc 0 t := by
  rw [mem_uIcc]
  rcases le_total 0 t with ht | ht
  · left; constructor <;> nlinarith
  · right; constructor <;> nlinarith

/-- Global version: the time-`t` map has Jacobian determinant one (within the set of points
alive at time `t`). -/
theorem global_det (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hΦ : IsMaximalFlow f Ω I Φ)
    (htr : ∀ w ∈ Ω, LinearMap.trace ℝ E (fderiv ℝ f w) = 0) {x : E} (hx : x ∈ Ω) {t : ℝ}
    (ht : t ∈ I x) : ∃ D : E →L[ℝ] E,
      HasFDerivWithinAt (Φ t) D {y | y ∈ Ω ∧ t ∈ I y} x ∧ D.det = 1 := by
  set W := {y | y ∈ Ω ∧ t ∈ I y} with hW
  have hxW : x ∈ W := ⟨hx, ht⟩
  have hsub : uIcc 0 t ⊆ I x := fun s hs => mem_of_uIcc hΦ hx ht hs
  set K := (fun s => Φ s x) '' uIcc 0 t with hKdef
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn
    ((continuousOn_traj hΦ hx).mono hsub)
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨s, hs, rfl⟩; exact flow_mem hΦ hx (hsub hs)
  obtain ⟨ε, hε, hP⟩ := uniform_det hΩ hf hΦ htr hK hKΩ
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / ε)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  set δ := t / N with hδ
  have hδε : |δ| < ε := by
    rw [hδ, abs_div, Nat.abs_cast, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hN; linarith
  have hmem : ∀ k : ℕ, k ≤ N → (k : ℝ) * δ ∈ uIcc 0 t := by
    intro k hk
    have : (k : ℝ) * δ = ((k : ℝ) / N) * t := by rw [hδ]; field_simp
    rw [this]
    exact mul_mem_uIcc (by positivity) (by rw [div_le_one hNpos]; exact_mod_cast hk)
  have hclaim : ∀ k : ℕ, k ≤ N → ∃ D : E →L[ℝ] E,
      HasFDerivWithinAt (Φ ((k : ℝ) * δ)) D W x ∧ D.det = 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨ContinuousLinearMap.id ℝ E, ?_, det_id'⟩
      simp only [Nat.cast_zero, zero_mul]
      refine (hasFDerivWithinAt_id x W).congr (fun y hy => flow_zero hΦ hy.1) (flow_zero hΦ hx)
    | succ k ih =>
      intro hk
      obtain ⟨D, hD, hdet⟩ := ih (by omega)
      have hk1 := hmem k (by omega)
      have hk2 := hmem (k + 1) hk
      have hzK : Φ ((k : ℝ) * δ) x ∈ K := ⟨_, hk1, rfl⟩
      obtain ⟨-, D', hD', hdet'⟩ := hP _ hzK δ hδε
      refine ⟨D'.comp D, ?_, by rw [det_comp', hdet, hdet', mul_one]⟩
      have hcomp := hD'.comp_hasFDerivWithinAt x hD
      have heq : ∀ y ∈ W, Φ (((k + 1 : ℕ) : ℝ) * δ) y = Φ δ (Φ ((k : ℝ) * δ) y) := by
        intro y hy
        have h1 := mem_of_uIcc hΦ hy.1 hy.2 hk1
        have h2 := mem_of_uIcc hΦ hy.1 hy.2 hk2
        have e : (k : ℝ) * δ + δ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring
        rw [← e] at h2 ⊢
        exact ((flow_add hΦ hy.1 h1 h2).2).symm
      exact hcomp.congr (fun y hy => heq y hy) (heq x hxW)
  obtain ⟨D, hD, hdet⟩ := hclaim N le_rfl
  have hNt : (N : ℝ) * δ = t := by rw [hδ]; field_simp
  rw [hNt] at hD
  exact ⟨D, hD, hdet⟩

end DivFree

end LVF


open Set Filter Topology

namespace LVF
open TeschlODE.HigherDim

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section Patch

variable {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}

/-- Local flow data on a neighbourhood of every point of a compact set, with a uniform time. -/
theorem patch (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hΦ : IsMaximalFlow f Ω I Φ)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ ε > 0, ∀ w ∈ K, ∃ r > 0,
      ∃ D : ℝ → E → E →L[ℝ] E,
      ContinuousOn (fun p : E × ℝ => D p.2 p.1) (Metric.ball w r ×ˢ Ioo (-ε) ε) ∧
      ContinuousOn (fun p : E × ℝ => Φ p.2 p.1) (Metric.ball w r ×ˢ Ioo (-ε) ε) ∧
      ∀ y ∈ Metric.ball w r, D 0 y = ContinuousLinearMap.id ℝ E ∧
        ∀ s ∈ Ioo (-ε) ε, s ∈ I y ∧ Φ s y ∈ Ω ∧ HasFDerivAt (Φ s) (D s y) y ∧
          HasDerivAt (fun s => D s y) ((fderiv ℝ f (Φ s y)).comp (D s y)) s := by
  have hloc := fun z (hz : z ∈ K) => local_flow hΩ hf hΦ (hKΩ hz)
  choose! rf hrf εf hεf Df hDc hΦc hP using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun z => Metric.ball z (rf z))
    (fun z hz => Metric.ball_mem_nhds z (hrf z hz))
  classical
  set S : Finset ℝ := insert 1 (t.image εf) with hS
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hSpos : 0 < S.min' hSne := by
    rw [Finset.lt_min'_iff]
    intro a ha
    rw [hS, Finset.mem_insert, Finset.mem_image] at ha
    rcases ha with rfl | ⟨z, hz, rfl⟩
    · norm_num
    · exact hεf z (htK z hz)
  refine ⟨S.min' hSne, hSpos, fun w hw => ?_⟩
  have hw' := hcov hw
  rw [mem_iUnion₂] at hw'
  obtain ⟨z, hz, hwz⟩ := hw'
  have hzK := htK z hz
  have hle : S.min' hSne ≤ εf z :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz))
  have hwz' : dist w z < rf z := hwz
  have hball : Metric.ball w (rf z - dist w z) ⊆ Metric.ball z (rf z) := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    linarith [dist_triangle y w z]
  have hIoo : Ioo (-S.min' hSne) (S.min' hSne) ⊆ Ioo (-εf z) (εf z) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hprod : Metric.ball w (rf z - dist w z) ×ˢ Ioo (-S.min' hSne) (S.min' hSne) ⊆
      Metric.ball z (rf z) ×ˢ Ioo (-εf z) (εf z) := prod_mono hball hIoo
  refine ⟨rf z - dist w z, by linarith, Df z, (hDc z hzK).mono hprod, (hΦc z hzK).mono hprod,
    fun y hy => ⟨(hP z hzK y (hball hy)).1, fun s hs => (hP z hzK y (hball hy)).2 s (hIoo hs)⟩⟩

/-- The Jacobian determinant of the time-`h` map. -/
noncomputable def Jac (Φ : ℝ → E → E) (y : E) (h : ℝ) : ℝ := (fderiv ℝ (Φ h) y).det

theorem continuous_trace : Continuous (fun A : E →L[ℝ] E => LinearMap.trace ℝ E A) :=
  ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional

/-- Consequences of the patch data at a point of the compact set. -/
theorem jac_facts (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hΦ : IsMaximalFlow f Ω I Φ)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ ε > 0, ∀ y ∈ K, ∀ h ∈ Ioo (-ε) ε,
      h ∈ I y ∧ Φ h y ∈ Ω ∧ HasFDerivAt (Φ h) (fderiv ℝ (Φ h) y) y ∧
      ContinuousAt (fun p : E × ℝ => Jac Φ p.1 p.2) (y, h) ∧
      ContinuousAt (fun p : E × ℝ => Φ p.2 p.1) (y, h) ∧
      HasDerivAt (fun h => Jac Φ y h)
        (LinearMap.trace ℝ E (fderiv ℝ f (Φ h y)) * Jac Φ y h) h ∧
      0 < Jac Φ y h := by
  obtain ⟨ε, hε, hP⟩ := patch hΩ hf hΦ hK hKΩ
  refine ⟨ε, hε, fun y hy h hh => ?_⟩
  obtain ⟨r, hr, D, hDc, hΦc, hD⟩ := hP y hy
  have hyb : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hN : Metric.ball y r ×ˢ Ioo (-ε) ε ∈ 𝓝 (y, h) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hyb, hh⟩
  have hfd : ∀ y' ∈ Metric.ball y r, ∀ s ∈ Ioo (-ε) ε, fderiv ℝ (Φ s) y' = D s y' :=
    fun y' hy' s hs => ((hD y' hy').2 s hs).2.2.1.fderiv
  obtain ⟨hI, hΩm, hFd, hvar⟩ := (hD y hyb).2 h hh
  have hJeq : ∀ s ∈ Ioo (-ε) ε, Jac Φ y s = (D s y).det := fun s hs => by
    rw [Jac, hfd y hyb s hs]
  refine ⟨hI, hΩm, hfd y hyb h hh ▸ hFd, ?_, hΦc.continuousAt hN, ?_, ?_⟩
  · have hc : ContinuousAt (fun p : E × ℝ => (D p.2 p.1).det) (y, h) :=
      (differentiable_det (E := E)).continuous.continuousAt.comp (hDc.continuousAt hN)
    refine hc.congr ?_
    filter_upwards [hN] with p hp
    rw [Jac, hfd p.1 hp.1 p.2 hp.2]
  · have hd := hasDerivAt_det hvar
    rw [← hJeq h hh] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hh] with s hs
    exact hJeq s hs
  · -- positivity: `Jac = exp (∫ trace)`
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    set a : ℝ → ℝ := fun u => LinearMap.trace ℝ E (fderiv ℝ f (Φ u y)) with ha
    have hac : ContinuousOn a (Ioo (-ε) ε) := by
      have h1 : ContinuousOn (fun u => Φ u y) (Ioo (-ε) ε) := by
        refine hΦc.comp (continuousOn_const.prodMk continuousOn_id) ?_
        intro u hu; exact ⟨hyb, hu⟩
      have h2 : ContinuousOn (fderiv ℝ f) Ω := hf.continuousOn_fderiv_of_isOpen hΩ le_rfl
      exact continuous_trace.comp_continuousOn
        (h2.comp h1 fun u hu => ((hD y hyb).2 u hu).2.1)
    have hJd : ∀ s ∈ Ioo (-ε) ε, HasDerivAt (fun s => Jac Φ y s) (a s * Jac Φ y s) s := by
      intro s hs
      have hd := hasDerivAt_det ((hD y hyb).2 s hs).2.2.2
      rw [← hJeq s hs] at hd
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      exact hJeq u hu
    set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, a u with hF
    have hFd : ∀ s ∈ Ioo (-ε) ε, HasDerivAt F (a s) s := by
      intro s hs
      have hsub := uIcc_sub hs
      exact intervalIntegral.integral_hasDerivAt_right ((hac.mono hsub).intervalIntegrable)
        (hac.stronglyMeasurableAtFilter isOpen_Ioo s hs)
        (hac.continuousAt (isOpen_Ioo.mem_nhds hs))
    have hq : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => Jac Φ y s * Real.exp (-F s)) 0 s := by
      intro s hs
      have := (hJd s hs).mul ((hFd s hs).neg.exp)
      refine this.congr_deriv ?_
      ring
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => Jac Φ y s * Real.exp (-F s)) (f' := fun _ => (0 : ℝ)) (C := 0)
      (s := Ioo (-ε) ε) (fun u hu => (hq u hu).hasDerivWithinAt) (fun _ _ => by simp)
      (convex_Ioo _ _) h0 hh
    have hJ0 : Jac Φ y 0 = 1 := by rw [hJeq 0 h0, (hD y hyb).1, det_id']
    simp only [hJ0, hF, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one,
      zero_mul, norm_le_zero_iff, sub_eq_zero] at hmv
    have hpos : 0 < Jac Φ y h * Real.exp (-F h) := by rw [hmv]; norm_num
    exact pos_of_mul_pos_left hpos (Real.exp_pos _).le

end Patch

end LVF


open Set Filter Topology MeasureTheory

namespace LVF
open TeschlODE.HigherDim

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Differentiability of the time-`t` map within the set of points alive at time `t`. -/
theorem global_diff {f : E → E} {Ω : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hΦ : IsMaximalFlow f Ω I Φ) {x : E} (hx : x ∈ Ω)
    {t : ℝ} (ht : t ∈ I x) : ∃ D : E →L[ℝ] E,
      HasFDerivWithinAt (Φ t) D {y | y ∈ Ω ∧ t ∈ I y} x := by
  set W := {y | y ∈ Ω ∧ t ∈ I y} with hW
  have hxW : x ∈ W := ⟨hx, ht⟩
  have hsub : uIcc 0 t ⊆ I x := fun s hs => mem_of_uIcc hΦ hx ht hs
  set K := (fun s => Φ s x) '' uIcc 0 t with hKdef
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn
    ((continuousOn_traj hΦ hx).mono hsub)
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨s, hs, rfl⟩; exact flow_mem hΦ hx (hsub hs)
  obtain ⟨ε, hε, hP⟩ := jac_facts hΩ hf hΦ hK hKΩ
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / ε)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  set δ := t / N with hδ
  have hδε : δ ∈ Ioo (-ε) ε := by
    have : |δ| < ε := by
      rw [hδ, abs_div, Nat.abs_cast, div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hε] at hN; linarith
    rw [abs_lt] at this; exact this
  have hmem : ∀ k : ℕ, k ≤ N → (k : ℝ) * δ ∈ uIcc 0 t := by
    intro k hk
    have : (k : ℝ) * δ = ((k : ℝ) / N) * t := by rw [hδ]; field_simp
    rw [this]
    exact mul_mem_uIcc (by positivity) (by rw [div_le_one hNpos]; exact_mod_cast hk)
  have hclaim : ∀ k : ℕ, k ≤ N → ∃ D : E →L[ℝ] E,
      HasFDerivWithinAt (Φ ((k : ℝ) * δ)) D W x := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨ContinuousLinearMap.id ℝ E, ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      exact (hasFDerivWithinAt_id x W).congr (fun y hy => flow_zero hΦ hy.1) (flow_zero hΦ hx)
    | succ k ih =>
      intro hk
      obtain ⟨D, hD⟩ := ih (by omega)
      have hk1 := hmem k (by omega)
      have hk2 := hmem (k + 1) hk
      have hzK : Φ ((k : ℝ) * δ) x ∈ K := ⟨_, hk1, rfl⟩
      have hD' := (hP _ hzK δ hδε).2.2.1
      have hcomp := hD'.comp_hasFDerivWithinAt x hD
      have heq : ∀ y ∈ W, Φ (((k + 1 : ℕ) : ℝ) * δ) y = Φ δ (Φ ((k : ℝ) * δ) y) := by
        intro y hy
        have h1 := mem_of_uIcc hΦ hy.1 hy.2 hk1
        have h2 := mem_of_uIcc hΦ hy.1 hy.2 hk2
        have e : (k : ℝ) * δ + δ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring
        rw [← e] at h2 ⊢
        exact ((flow_add hΦ hy.1 h1 h2).2).symm
      exact ⟨_, hcomp.congr (fun y hy => heq y hy) (heq x hxW)⟩
  obtain ⟨D, hD⟩ := hclaim N le_rfl
  have hNt : (N : ℝ) * δ = t := by rw [hδ]; field_simp
  rw [hNt] at hD
  exact ⟨D, hD⟩

end LVF

namespace TeschlODE.HigherDim

theorem divergence_eq_trace {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    divergence f x = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (fderiv ℝ f x : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    Matrix.trace, divergence]
  simp [LinearMap.toMatrix_apply]

end TeschlODE.HigherDim


open Set Filter Topology MeasureTheory

namespace TeschlODE.HigherDim

theorem volume_hasDerivAt' {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f Set.univ I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (t₀ : ℝ) (ht₀ : ∀ x ∈ closure U, t₀ ∈ I x) :
    volume (Φ t₀ '' U) < ⊤ ∧ IntegrableOn (divergence f) (Φ t₀ '' U) ∧
      HasDerivAt (fun t : ℝ => (volume (Φ t '' U)).toReal)
        (∫ x in Φ t₀ '' U, divergence f x) t₀ := by
  have hf' : ContDiffOn ℝ 1 f univ := hf.contDiffOn
  have hcU : IsCompact (closure U) := hUb.isCompact_closure
  have hcont : ContinuousOn (Φ t₀) (closure U) := by
    intro x hx
    obtain ⟨D, hD⟩ := LVF.global_diff isOpen_univ hf' hΦ (mem_univ x) (ht₀ x hx)
    exact hD.continuousWithinAt.mono fun y hy => ⟨mem_univ y, ht₀ y hy⟩
  set K := Φ t₀ '' closure U with hKdef
  have hK : IsCompact K := hcU.image_of_continuousOn hcont
  set V := Φ t₀ '' U with hVdef
  have hVK : V ⊆ K := image_mono subset_closure
  have hinj : InjOn (Φ t₀) U := (LVF.flow_injOn hΦ t₀).mono
    fun y hy => (show y ∈ univ ∧ t₀ ∈ I y from ⟨mem_univ y, ht₀ y (subset_closure hy)⟩)
  have hVm : MeasurableSet V :=
    hU.measurableSet.image_of_continuousOn_injOn (hcont.mono subset_closure) hinj
  have hVfin : volume V < ⊤ := (measure_mono hVK).trans_lt hK.measure_lt_top
  have hdivc : Continuous (divergence f) := by
    have : divergence f = fun x => LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        (fderiv ℝ f x : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
      funext (divergence_eq_trace f)
    rw [this]
    exact LVF.continuous_trace.comp (hf.continuous_fderiv (by norm_num))
  refine ⟨hVfin, (hdivc.continuousOn.integrableOn_compact hK).mono_set hVK, ?_⟩
  obtain ⟨ε, hε, hJ⟩ := LVF.jac_facts isOpen_univ hf' hΦ hK (subset_univ K)
  -- shifting time by `h`
  have hshift : ∀ h ∈ Ioo (-ε) ε, Φ (t₀ + h) '' U = Φ h '' V := by
    intro h hh
    rw [hVdef, image_image]
    refine image_congr fun x hx => ?_
    have hxc := subset_closure hx
    have hx0 := ht₀ x hxc
    have hyK : Φ t₀ x ∈ K := ⟨x, hxc, rfl⟩
    obtain ⟨hm, hback⟩ := LVF.flow_add hΦ (mem_univ x) hx0 (b := -t₀)
      (by simpa using LVF.zero_mem hΦ (mem_univ x))
    rw [add_neg_cancel, LVF.flow_zero hΦ (mem_univ x)] at hback
    have hhy := (hJ _ hyK h hh).1
    obtain ⟨-, hfin⟩ := LVF.flow_add hΦ (mem_univ _) hm (b := t₀ + h)
      (by rwa [neg_add_cancel_left])
    rw [hback, neg_add_cancel_left] at hfin
    exact hfin
  have hJc : ∀ h ∈ Ioo (-ε) ε, ContinuousOn (fun y => LVF.Jac Φ y h) K := by
    intro h hh y hy
    have h1 := (hJ y hy h hh).2.2.2.1
    exact (h1.comp (f := fun y => (y, h)) (by fun_prop)).continuousWithinAt
  have hJint : ∀ h ∈ Ioo (-ε) ε, IntegrableOn (fun y => LVF.Jac Φ y h) V := fun h hh =>
    ((hJc h hh).integrableOn_compact hK).mono_set hVK
  have hvol : ∀ h ∈ Ioo (-ε) ε,
      (volume (Φ (t₀ + h) '' U)).toReal = ∫ y in V, LVF.Jac Φ y h := by
    intro h hh
    rw [hshift h hh]
    have hcv := lintegral_abs_det_fderiv_eq_addHaar_image volume hVm
      (fun y hy => (hJ y (hVK hy) h hh).2.2.1.hasFDerivWithinAt)
      ((LVF.flow_injOn hΦ h).mono fun y hy =>
        (show y ∈ univ ∧ h ∈ I y from ⟨mem_univ y, (hJ y (hVK hy) h hh).1⟩))
    rw [← hcv]
    have e : ∫⁻ y in V, ENNReal.ofReal |(fderiv ℝ (Φ h) y).det| =
        ∫⁻ y in V, ENNReal.ofReal (LVF.Jac Φ y h) := by
      refine setLIntegral_congr_fun hVm fun y hy => ?_
      have hp := (hJ y (hVK hy) h hh).2.2.2.2.2.2
      rw [LVF.Jac] at hp ⊢
      rw [abs_of_pos hp]
    have hnn : ∀ y ∈ V, 0 ≤ LVF.Jac Φ y h := fun y hy => (hJ y (hVK hy) h hh).2.2.2.2.2.2.le
    rw [e, ← ofReal_integral_eq_lintegral_ofReal (hJint h hh)
      (ae_restrict_of_forall_mem hVm hnn), ENNReal.toReal_ofReal (setIntegral_nonneg hVm hnn)]
  -- differentiate under the integral sign at `h = 0`
  have hε2 : Icc (-(ε / 2)) (ε / 2) ⊆ Ioo (-ε) ε := fun h hh =>
    ⟨by linarith [hh.1], by linarith [hh.2]⟩
  set F' : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun h y =>
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (fderiv ℝ f (Φ h y) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) *
      LVF.Jac Φ y h with hF'
  have hF'c : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => F' p.2 p.1)
      (K ×ˢ Icc (-(ε / 2)) (ε / 2)) := by
    intro p hp
    have h1 := (hJ p.1 hp.1 p.2 (hε2 hp.2)).2.2.2.1
    have h2 := (hJ p.1 hp.1 p.2 (hε2 hp.2)).2.2.2.2.1
    have h3 : ContinuousAt (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          (fderiv ℝ f (Φ q.2 q.1) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) p :=
      (LVF.continuous_trace.comp (hf.continuous_fderiv (by norm_num))).continuousAt.comp h2
    exact (h3.mul h1).continuousWithinAt
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hF'c
  have hfinV : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.2 hVfin.ne
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict V)
    (F := fun h y => LVF.Jac Φ y h) (F' := F') (x₀ := 0) (bound := fun _ => M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) hε) fun h hh =>
      ((hJc h hh).mono hVK).aestronglyMeasurable hVm)
    (hJint 0 ⟨by linarith, hε⟩)
    (by
      have hc : ContinuousOn (F' 0) K := fun y hy =>
        (hF'c.comp (f := fun y => (y, (0 : ℝ))) (by fun_prop)
          (fun y hy => ⟨hy, by constructor <;> linarith⟩) y hy)
      exact (hc.mono hVK).aestronglyMeasurable hVm)
    (ae_restrict_of_forall_mem hVm fun y hy h hh => hM (y, h) ⟨hVK hy, hh⟩)
    (integrable_const M)
    (ae_restrict_of_forall_mem hVm fun y hy h hh => (hJ y (hVK hy) h (hε2 hh)).2.2.2.2.2.1)
  obtain ⟨-, hd⟩ := hder
  -- identify the derivative
  have hF'0 : ∀ y ∈ V, F' 0 y = divergence f y := by
    intro y hy
    have hid : Φ 0 = id := funext fun x => LVF.flow_zero hΦ (mem_univ x)
    simp only [hF', LVF.Jac, hid, fderiv_id, id, divergence_eq_trace]
    rw [LVF.det_id', mul_one]
  rw [setIntegral_congr_fun hVm hF'0] at hd
  -- transport to time `t₀`
  have hd0 : HasDerivAt (fun h => ∫ y in V, LVF.Jac Φ y h)
      (∫ x in V, divergence f x) (t₀ - t₀) := by rw [sub_self]; exact hd
  have hd' := hd0.comp_sub_const t₀ t₀
  refine hd'.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show t₀ - ε < t₀ by linarith) (show t₀ < t₀ + ε by linarith)]
    with t ht
  have hh : t - t₀ ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have := hvol (t - t₀) hh
  rw [add_sub_cancel] at this
  exact this

end TeschlODE.HigherDim
open MeasureTheory TeschlODE.HigherDim in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f Set.univ I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (t₀ : ℝ) (ht₀ : ∀ x ∈ closure U, t₀ ∈ I x) :
    volume (Φ t₀ '' U) < ⊤ ∧ IntegrableOn (divergence f) (Φ t₀ '' U) ∧
      HasDerivAt (fun t : ℝ => (volume (Φ t '' U)).toReal)
        (∫ x in Φ t₀ '' U, divergence f x) t₀ :=
  volume_hasDerivAt' f hf I Φ hΦ U hU hUb t₀ ht₀

