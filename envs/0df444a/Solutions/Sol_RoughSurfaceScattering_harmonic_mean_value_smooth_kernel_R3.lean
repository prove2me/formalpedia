-- Prove2me | solution 1 for RoughSurfaceScattering.harmonic_mean_value_smooth_kernel_R3
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T11:09:14.891047+00:00
-- url     : https://prove2.me/submissions/ad166295-fa76-4421-98b0-3231e6b6caa4

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric InnerProductSpace Laplacian
open RoughSurfaceScattering

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- A function continuous on `B̄(0,r)` and vanishing outside is integrable. -/
lemma integrable_of_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : R3 → E) (r : ℝ) (hc : ContinuousOn φ (closedBall 0 r))
    (h0 : ∀ y, y ∉ closedBall (0 : R3) r → φ y = 0) : Integrable φ := by
  have hind : Set.indicator (closedBall (0 : R3) r) φ = φ := by
    funext y
    by_cases hy : y ∈ closedBall (0 : R3) r
    · simp [hy]
    · simp [hy, h0 y hy]
  rw [← hind, integrable_indicator_iff measurableSet_closedBall]
  exact hc.integrableOn_compact (isCompact_closedBall 0 r)

/-- `H(u) = ½ ∫_{r²}^u h`, so that `H' = h/2` and `H = 0` on `[r², ∞)`. -/
noncomputable def Hfun (h : ℝ → ℝ) (r : ℝ) (u : ℝ) : ℝ := (1 / 2) * ∫ v in (r ^ 2)..u, h v

lemma Hfun_hasDerivAt (h : ℝ → ℝ) (hh : Continuous h) (r u : ℝ) :
    HasDerivAt (Hfun h r) ((1 / 2) * h u) u :=
  ((hh.integral_hasStrictDerivAt (r ^ 2) u).hasDerivAt).const_mul (1 / 2)

lemma Hfun_zero (h : ℝ → ℝ) (r : ℝ) (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0) (u : ℝ)
    (hu : r ^ 2 ≤ u) : Hfun h r u = 0 := by
  unfold Hfun
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => by
    rw [Set.uIcc_of_le hu] at hv; exact hsupp v hv.1)]
  simp

/-- `Ψ(y) = H(|y|²)`. -/
noncomputable def Psi (h : ℝ → ℝ) (r : ℝ) (y : R3) : ℝ := Hfun h r (‖y‖ ^ 2)

lemma Psi_hasFDerivAt (h : ℝ → ℝ) (hh : Continuous h) (r : ℝ) (y : R3) :
    HasFDerivAt (Psi h r) (h (‖y‖ ^ 2) • innerSL ℝ y) y := by
  have hn : HasFDerivAt (fun y : R3 => ‖y‖ ^ 2) (2 • innerSL ℝ y) y := by
    simpa using (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have := (Hfun_hasDerivAt h hh r (‖y‖ ^ 2)).comp_hasFDerivAt y hn
  refine this.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

lemma fderiv_Psi_apply (h : ℝ → ℝ) (hh : Continuous h) (r : ℝ) (y v : R3) :
    fderiv ℝ (Psi h r) y v = h (‖y‖ ^ 2) * @inner ℝ R3 _ y v := by
  rw [(Psi_hasFDerivAt h hh r y).fderiv]
  simp

lemma Psi_continuous (h : ℝ → ℝ) (hh : Continuous h) (r : ℝ) : Continuous (Psi h r) :=
  continuous_iff_continuousAt.mpr fun y => (Psi_hasFDerivAt h hh r y).continuousAt

lemma Psi_zero (h : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0)
    (y : R3) (hy : y ∉ closedBall (0 : R3) r) : Psi h r y = 0 := by
  apply Hfun_zero h r hsupp
  rw [mem_closedBall, dist_zero_right, not_le] at hy
  nlinarith

lemma h_zero_out (h : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0)
    (y : R3) (hy : y ∉ closedBall (0 : R3) r) : h (‖y‖ ^ 2) = 0 := by
  apply hsupp
  rw [mem_closedBall, dist_zero_right, not_le] at hy
  nlinarith

lemma tsupport_Psi (h : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0) :
    tsupport (Psi h r) ⊆ closedBall 0 r :=
  closure_minimal (fun y hy => by_contra fun hn => hy (Psi_zero h r hr hsupp y hn))
    isClosed_closedBall

lemma mem_of_small (z y : R3) (t r : ℝ) (ht : |t| ≤ 1) (hy : y ∈ closedBall (0 : R3) r) :
    z - t • y ∈ closedBall z r := by
  rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  rw [mem_closedBall, dist_zero_right] at hy
  calc |t| * ‖y‖ ≤ 1 * r := mul_le_mul ht hy (norm_nonneg _) zero_le_one
    _ = r := one_mul r

/-- The key cancellation: `∫ h(|y|²) Df(z - t y) y dy = 0` for `t ∈ [0,1]`. -/
lemma key_zero (f : R3 → ℂ) (U : Set R3) (hU : IsOpen U) (hC2 : ContDiffOn ℝ 2 f U)
    (hΔ : ∀ w ∈ U, Δ f w = 0) (h : ℝ → ℝ) (hh : Continuous h) (r : ℝ) (hr : 0 < r)
    (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0) (z : R3) (hz : closedBall z r ⊆ U) (t : ℝ)
    (ht : |t| ≤ 1) :
    ∫ y, h (‖y‖ ^ 2) • fderiv ℝ f (z - t • y) y = 0 := by
  set e : Fin 3 → R3 := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hmem : ∀ y ∈ closedBall (0 : R3) r, z - t • y ∈ U := fun y hy =>
    hz (mem_of_small z y t r ht hy)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) U := hC2.fderiv_of_isOpen hU (by norm_num)
  have hDfc : ContinuousOn (fderiv ℝ f) U := hDf.continuousOn
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U :=
    hDf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hDfd : ∀ w ∈ U, DifferentiableAt ℝ (fderiv ℝ f) w := fun w hw =>
    (hDf.differentiableOn one_ne_zero w hw).differentiableAt (hU.mem_nhds hw)
  have hcomp : ContinuousOn (fun y : R3 => z - t • y) (closedBall 0 r) := by fun_prop
  -- `G i y = ∂ᵢf(z - t y)` and its derivative
  set G : Fin 3 → R3 → ℂ := fun i y => fderiv ℝ f (z - t • y) (e i) with hG
  have hGd : ∀ i, ∀ y ∈ closedBall (0 : R3) r, HasFDerivAt (G i)
      (-(t • ((fderiv ℝ (fderiv ℝ f) (z - t • y)).flip (e i)))) y := by
    intro i y hy
    have hw := hmem y hy
    have h1 : HasFDerivAt (fun y : R3 => z - t • y) (-(t • ContinuousLinearMap.id ℝ R3)) y := by
      have := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul t).const_sub z
      simpa using this
    have h2 : HasFDerivAt (fun w => fderiv ℝ f w (e i))
        ((fderiv ℝ (fderiv ℝ f) (z - t • y)).flip (e i)) (z - t • y) := by
      have := (hDfd _ hw).hasFDerivAt.clm_apply (hasFDerivAt_const (e i) (z - t • y))
      simpa using this
    have := h2.comp y h1
    refine this.congr_fderiv ?_
    ext v
    simp
  -- pointwise expansion of the integrand
  have hexp : ∀ y, h (‖y‖ ^ 2) • fderiv ℝ f (z - t • y) y =
      ∑ i, fderiv ℝ (Psi h r) y (e i) • G i y := by
    intro y
    have hy : y = ∑ i, y i • e i := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y]
      simp [he]
    have hD : fderiv ℝ f (z - t • y) y = fderiv ℝ f (z - t • y) (∑ i, y i • e i) := by
      rw [← hy]
    rw [hD, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_Psi_apply h hh r, map_smul, smul_smul]
    congr 1
    simp [he, EuclideanSpace.inner_single_right]
  -- integrability of the pieces
  have hint1 : ∀ i, Integrable fun y => fderiv ℝ (Psi h r) y (e i) • G i y := by
    intro i
    refine integrable_of_closedBall _ r ?_ fun y hy => ?_
    · have hc1 : ContinuousOn (fun y : R3 => fderiv ℝ (Psi h r) y (e i)) (closedBall 0 r) := by
        simp only [fderiv_Psi_apply h hh r]
        fun_prop
      have hc2 : ContinuousOn (G i) (closedBall 0 r) :=
        ((continuous_id.clm_apply continuous_const).comp_continuousOn
          (hDfc.comp hcomp fun y hy => hmem y hy))
      exact hc1.smul hc2
    · simp [fderiv_Psi_apply h hh r, h_zero_out h r hr hsupp y hy]
  have hDGc : ∀ i, ContinuousOn
      (fun y => -(t • fderiv ℝ (fderiv ℝ f) (z - t • y) (e i) (e i))) (closedBall 0 r) := by
    intro i
    have : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ f) (z - t • y)) (closedBall 0 r) :=
      hD2c.comp hcomp fun y hy => hmem y hy
    have hX : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ f) (z - t • y) (e i) (e i))
        (closedBall 0 r) :=
      (continuous_id.clm_apply continuous_const).comp_continuousOn
        ((continuous_id.clm_apply continuous_const).comp_continuousOn this)
    exact (hX.const_smul t).neg
  have hint2 : ∀ i, Integrable fun y => Psi h r y • fderiv ℝ (G i) y (e i) := by
    intro i
    refine integrable_of_closedBall _ r ?_ fun y hy => ?_
    · refine ((Psi_continuous h hh r).continuousOn).smul ((hDGc i).congr fun y hy => ?_)
      rw [(hGd i y hy).fderiv]
      simp
    · simp [Psi_zero h r hr hsupp y hy]
  have hint3 : ∀ i, Integrable fun y => Psi h r y • G i y := by
    intro i
    refine integrable_of_closedBall _ r ?_ fun y hy => ?_
    · exact ((Psi_continuous h hh r).continuousOn).smul
        ((continuous_id.clm_apply continuous_const).comp_continuousOn
          (hDfc.comp hcomp fun y hy => hmem y hy))
    · simp [Psi_zero h r hr hsupp y hy]
  -- integration by parts in each direction
  have hibp : ∀ i, ∫ y, fderiv ℝ (Psi h r) y (e i) • G i y =
      -∫ y, Psi h r y • fderiv ℝ (G i) y (e i) := by
    intro i
    have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (μ := volume) (f := Psi h r) (g := G i) (v := e i)
      (B := ContinuousLinearMap.lsmul ℝ ℝ) (hint1 i) (hint2 i) (hint3 i)
      (fun y _ => (Psi_hasFDerivAt h hh r y).differentiableAt)
      (fun y hy => (hGd i y (tsupport_Psi h r hr hsupp hy)).differentiableAt)
    simp only [ContinuousLinearMap.lsmul_apply] at this
    rw [this, neg_neg]
  -- the Laplacian appears and vanishes
  have hlap : ∀ y, Psi h r y • ∑ i, fderiv ℝ (G i) y (e i) = 0 := by
    intro y
    by_cases hy : y ∈ closedBall (0 : R3) r
    · have hw := hmem y hy
      have hsum : ∑ i, fderiv ℝ (G i) y (e i) = -t • Δ f (z - t • y) := by
        simp only [fun i => (hGd i y hy).fderiv]
        rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
        simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          EuclideanSpace.basisFun_apply, Finset.smul_sum, he]
        exact Finset.sum_congr rfl fun i _ => by simp [neg_smul]
      rw [hsum, hΔ _ hw, smul_zero, smul_zero]
    · simp [Psi_zero h r hr hsupp y hy]
  calc ∫ y, h (‖y‖ ^ 2) • fderiv ℝ f (z - t • y) y
      = ∫ y, ∑ i, fderiv ℝ (Psi h r) y (e i) • G i y := by simp only [hexp]
    _ = ∑ i, ∫ y, fderiv ℝ (Psi h r) y (e i) • G i y :=
        integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i, -∫ y, Psi h r y • fderiv ℝ (G i) y (e i) := Finset.sum_congr rfl fun i _ => hibp i
    _ = -∫ y, ∑ i, Psi h r y • fderiv ℝ (G i) y (e i) := by
        rw [integral_finsetSum _ fun i _ => hint2 i, Finset.sum_neg_distrib]
    _ = 0 := by
        simp only [← Finset.smul_sum, hlap, integral_zero, neg_zero]

theorem solution (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) (h : ℝ → ℝ) (hh : Continuous h)
    (r : ℝ) (hr : 0 < r) (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0)
    (hint : ∫ y : EuclideanSpace ℝ (Fin 3), h (‖y‖ ^ 2) = 1)
    (z : EuclideanSpace ℝ (Fin 3)) (hz : Metric.closedBall z r ⊆ U) :
    f z = ∫ y, h (‖y‖ ^ 2) • f (z - y) := by
  -- regularity of `f`
  have hC2 : ContDiffOn ℝ 2 f U := fun w hw => (hf w hw).1.contDiffWithinAt
  have hΔ : ∀ w ∈ U, Δ f w = 0 := fun w hw => (hf w hw).2.self_of_nhds
  have hfc : ContinuousOn f U := hC2.continuousOn
  have hDfc : ContinuousOn (fderiv ℝ f) U :=
    (hC2.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn
  have hfd : ∀ w ∈ U, DifferentiableAt ℝ f w := fun w hw =>
    (hC2.differentiableOn (by norm_num) w hw).differentiableAt (hU.mem_nhds hw)
  -- a slightly larger ball inside `U`
  obtain ⟨δ, hδ, hcth⟩ := (isCompact_closedBall z r).exists_cthickening_subset_open hU hz
  rw [cthickening_closedBall hδ.le hr.le] at hcth
  set r' := δ + r with hr'
  set T := r' / r with hT
  have hT1 : 1 < T := by rw [hT, one_lt_div hr]; linarith
  have hmemT : ∀ t : ℝ, |t| < T → ∀ y ∈ closedBall (0 : R3) r, z - t • y ∈ closedBall z r' := by
    intro t ht y hy
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
    rw [mem_closedBall, dist_zero_right] at hy
    have : |t| * ‖y‖ ≤ T * r := mul_le_mul ht.le hy (norm_nonneg _) (by linarith)
    rw [hT, div_mul_cancel₀ _ hr.ne'] at this
    exact this
  have hmemU : ∀ t : ℝ, |t| < T → ∀ y ∈ closedBall (0 : R3) r, z - t • y ∈ U :=
    fun t ht y hy => hcth (hmemT t ht y hy)
  -- bounds
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r').exists_bound_of_continuousOn (hDfc.mono hcth)
  obtain ⟨Hm, hHm⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r ^ 2)).exists_bound_of_continuousOn
    hh.continuousOn
  set M' := max M 0
  set Hm' := max Hm 0
  -- the function `F` and its derivative
  set F : ℝ → R3 → ℂ := fun t y => h (‖y‖ ^ 2) • f (z - t • y) with hFdef
  set F' : ℝ → R3 → ℂ := fun t y => h (‖y‖ ^ 2) • fderiv ℝ f (z - t • y) (-y) with hF'def
  have hcomp : ∀ t : ℝ, ContinuousOn (fun y : R3 => z - t • y) (closedBall 0 r) := by
    intro t; fun_prop
  have hhc : Continuous fun y : R3 => h (‖y‖ ^ 2) := hh.comp (by fun_prop)
  have hFint : ∀ t : ℝ, |t| < T → Integrable (F t) := by
    intro t ht
    refine integrable_of_closedBall _ r ?_ fun y hy => ?_
    · exact hhc.continuousOn.smul (hfc.comp (hcomp t) fun y hy => hmemU t ht y hy)
    · simp [hFdef, h_zero_out h r hr hsupp y hy]
  have hF'int : ∀ t : ℝ, |t| < T → Integrable (F' t) := by
    intro t ht
    refine integrable_of_closedBall _ r ?_ fun y hy => ?_
    · refine hhc.continuousOn.smul ?_
      exact ((hDfc.comp (hcomp t) fun y hy => hmemU t ht y hy).clm_apply
        (continuous_neg.continuousOn))
    · simp [hF'def, h_zero_out h r hr hsupp y hy]
  set s : Set ℝ := {t | |t| < T} with hs
  have hsopen : IsOpen s := isOpen_lt continuous_abs continuous_const
  have hderiv : ∀ t0 ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => ∫ y, F t y) 0 t0 := by
    intro t0 ht0
    have ht0T : |t0| < T := by
      rw [abs_of_nonneg ht0.1]; linarith [ht0.2]
    have hsn : s ∈ nhds t0 := hsopen.mem_nhds ht0T
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
      (bound := Set.indicator (closedBall (0 : R3) r) fun _ => Hm' * M' * r) (x₀ := t0) hsn
      (Filter.eventually_of_mem hsn fun t ht => (hFint t ht).aestronglyMeasurable)
      (hFint t0 ht0T) (hF'int t0 ht0T).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y t ht => by
        by_cases hy : y ∈ closedBall (0 : R3) r
        · rw [Set.indicator_of_mem hy]
          have hw := hmemT t ht y hy
          have hyr : ‖y‖ ≤ r := by rwa [mem_closedBall, dist_zero_right] at hy
          have hv : ‖y‖ ^ 2 ∈ Set.Icc (0 : ℝ) (r ^ 2) :=
            ⟨by positivity, pow_le_pow_left₀ (norm_nonneg _) hyr 2⟩
          simp only [hF'def, norm_smul]
          calc ‖h (‖y‖ ^ 2)‖ * ‖fderiv ℝ f (z - t • y) (-y)‖
              ≤ Hm' * (M' * r) := by
                refine mul_le_mul ((hHm _ hv).trans (le_max_left _ _)) ?_ (norm_nonneg _)
                  (le_max_right _ _)
                calc _ ≤ ‖fderiv ℝ f (z - t • y)‖ * ‖-y‖ := ContinuousLinearMap.le_opNorm _ _
                  _ ≤ M' * r := by
                    rw [norm_neg]
                    exact mul_le_mul ((hM _ hw).trans (le_max_left _ _)) hyr (norm_nonneg _)
                      (le_max_right _ _)
            _ = Hm' * M' * r := by ring
        · rw [Set.indicator_of_notMem hy]
          simp [hF'def, h_zero_out h r hr hsupp y hy])
      ((integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const measure_closedBall_lt_top.ne))
      (Filter.Eventually.of_forall fun y t ht => by
        by_cases hy : y ∈ closedBall (0 : R3) r
        · have hw := hmemU t ht y hy
          have hline : HasDerivAt (fun t : ℝ => z - t • y) (-y) t := by
            have := ((hasDerivAt_id t).smul_const y).const_sub z
            simpa using this
          have := ((hfd _ hw).hasFDerivAt.comp_hasDerivAt t hline).const_smul (h (‖y‖ ^ 2))
          exact this
        · have h0 := h_zero_out h r hr hsupp y hy
          have : (fun t => F t y) = fun _ => 0 := by funext t; simp [hFdef, h0]
          rw [this]
          simpa [hF'def, h0] using hasDerivAt_const t (0 : ℂ))
    have hzero : ∫ y, F' t0 y = 0 := by
      have := key_zero f U hU hC2 hΔ h hh r hr hsupp z hz t0
        (by rw [abs_of_nonneg ht0.1]; exact ht0.2)
      simp only [hF'def, map_neg, smul_neg, integral_neg, this, neg_zero]
    rw [← hzero]
    exact key.2
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => ∫ y, F t y) (a := 0) (b := 1)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1
    ⟨zero_le_one, le_rfl⟩
  simp only [hFdef, one_smul, zero_smul, sub_zero] at hconst
  rw [hconst, integral_smul_const, hint, one_smul]
