-- Prove2me | solution 1 for ProxNewton.Inexact.inexact_prox_newton_local_convergence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:58:54.81009+00:00
-- url     : https://prove2.me/submissions/3e869da3-db32-4873-b6e6-d83d6a17c006

import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_ProxNewton_Inexact_Method
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open Filter Topology

open scoped RealInnerProductSpace

theorem aux_cgm_hasFDerivAt_grad {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gradient g) (hessian g y) y := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (gradient g) := by
    have : gradient g = fun x =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ g x) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ _).symm.contDiff.comp h1
  exact (h2.differentiable (by norm_num) y).hasFDerivAt

theorem aux_cgm_hess_symm {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) (y u w : EuclideanSpace ℝ (Fin n)) :
    ⟪hessian g y u, w⟫ = ⟪hessian g y w, u⟫ := by
  have hsymm : IsSymmSndFDerivAt ℝ g y := hg.contDiffAt.isSymmSndFDerivAt (by simp)
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) y) y :=
    (h1.differentiable (by norm_num) y).hasFDerivAt
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.toContinuousLinearMap
    with hLdef
  have hL : HasFDerivAt (fun x => L (fderiv ℝ g x)) (L.comp (fderiv ℝ (fderiv ℝ g) y)) y :=
    L.hasFDerivAt.comp y hd
  have heq : hessian g y = L.comp (fderiv ℝ (fderiv ℝ g) y) := by
    unfold hessian
    exact hL.fderiv
  rw [heq]
  simp only [ContinuousLinearMap.comp_apply, hLdef]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    InnerProductSpace.toDual_symm_apply]
  exact hsymm u w

theorem aux_cgm_quad_grad {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) (xk x : EuclideanSpace ℝ (Fin n)) :
    gradient (quadModel g xk) x = gradient g xk + hessian g xk (x - xk) := by
  set H := hessian g xk with hH
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y - xk)
      (ContinuousLinearMap.id ℝ _) x := (hasFDerivAt_id x).sub_const xk
  have h2 : HasFDerivAt (fun y => H (y - xk)) (H.comp (ContinuousLinearMap.id ℝ _)) x :=
    H.hasFDerivAt.comp x h1
  have h3 := h1.inner ℝ h2
  have h4 := (hasFDerivAt_const (gradient g xk) x).inner ℝ h1
  have h5 := (h4.const_add (g xk)).add (h3.const_mul (1 / 2 : ℝ))
  have hd : HasFDerivAt (quadModel g xk)
      (InnerProductSpace.toDual ℝ _ (gradient g xk + H (x - xk))) x := by
    refine h5.congr_fderiv ?_
    ext u
    simp
    have hs : ⟪x - xk, H u⟫ = ⟪H x - H xk, u⟫ := by
      rw [← real_inner_comm (x - xk) (H u), ← map_sub]
      exact aux_cgm_hess_symm g hg xk u (x - xk)
    rw [hs, inner_sub_left, inner_sub_right, real_inner_comm u (H x), real_inner_comm u (H xk)]
    ring
  have hgrad : HasGradientAt (quadModel g xk) (gradient g xk + H (x - xk)) x :=
    hasGradientAt_iff_hasFDerivAt.mpr hd
  exact hgrad.gradient

theorem aux_cgm_taylor {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L2 : ℝ)
    (hg : ContDiff ℝ 2 g)
    (hlip : ∀ x y, ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖)
    (xk x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient g x - gradient g xk - hessian g xk (x - xk)‖ ≤ L2 / 2 * ‖x - xk‖ ^ 2 := by
  set v := x - xk with hv
  let f : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t => gradient g (xk + t • v) - gradient g xk - t • hessian g xk v
  let f' : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t => hessian g (xk + t • v) v - hessian g xk v
  have hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    have hin : HasDerivAt (fun s : ℝ => xk + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add xk
    have hA : HasDerivAt ((gradient g) ∘ (fun s : ℝ => xk + s • v)) (hessian g (xk + t • v) v) t :=
      (aux_cgm_hasFDerivAt_grad g hg (xk + t • v)).comp_hasDerivAt t hin
    have hB : HasDerivAt (fun s : ℝ => s • hessian g xk v) (hessian g xk v) t := by
      simpa using (hasDerivAt_id t).smul_const (hessian g xk v)
    exact (hA.sub_const (gradient g xk)).sub hB
  let B : ℝ → ℝ := fun t => L2 / 2 * t ^ 2 * ‖v‖ ^ 2
  let B' : ℝ → ℝ := fun t => L2 * t * ‖v‖ ^ 2
  have hBd : ∀ t : ℝ, HasDerivAt B (B' t) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (L2 / 2)).mul_const (‖v‖ ^ 2)
    refine this.congr_deriv ?_
    simp only [B']
    push_cast
    ring
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (f' := f')
    (a := 0) (b := 1) (B := B) (B' := B')
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (by simp [f, B])
    hBd
    (by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have h1 : f' t = (hessian g (xk + t • v) - hessian g xk) v := by
        simp [f']
      rw [h1]
      calc ‖(hessian g (xk + t • v) - hessian g xk) v‖
          ≤ ‖hessian g (xk + t • v) - hessian g xk‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L2 * ‖xk + t • v - xk‖) * ‖v‖ := by
            gcongr
            exact hlip _ _
        _ = B' t := by
            simp only [B', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
            ring)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  have hf1 : f 1 = gradient g x - gradient g xk - hessian g xk (x - xk) := by
    simp [f, hv]
  rw [← hf1]
  simpa [B] using hmain

theorem aux_cgm_vi {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hD : Convex ℝ D) (hh : ConvexOn ℝ D h)
    (v p : EuclideanSpace ℝ (Fin n)) (hp : IsProxPoint D h v p)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ D) :
    h p - h z ≤ ⟪p - v, z - p⟫ := by
  set a := p - v with ha
  set d := z - p with hd
  -- for every t ∈ (0,1]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → h p - h z ≤ ⟪a, d⟫ + t / 2 * ‖d‖ ^ 2 := by
    intro t ht0 ht1
    have hmem : (1 - t) • p + t • z ∈ D := hD hp.1 hz (by linarith) ht0.le (by ring)
    have hconv : h ((1 - t) • p + t • z) ≤ (1 - t) • h p + t • h z :=
      hh.2 hp.1 hz (by linarith) ht0.le (by ring)
    have hopt := hp.2 _ hmem
    have hrw : (1 - t) • p + t • z - v = a + t • d := by
      simp only [ha, hd]; module
    rw [hrw] at hopt
    have hexp : ‖a + t • d‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * ⟪a, d⟫ + t ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, abs_of_pos ht0]
      ring
    rw [hexp] at hopt
    simp only [smul_eq_mul] at hconv
    have h2 : t * (h p - h z) ≤ t * (⟪a, d⟫ + t / 2 * ‖d‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h2 ht0
  apply le_of_forall_pos_le_add
  intro ε hε
  set K := ‖d‖ ^ 2 / 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  set t := min 1 (ε / K) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hε hKpos)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ ε / K := min_le_right _ _
  have h1 := key t ht0 ht1
  have h2 : t / 2 * ‖d‖ ^ 2 ≤ ε := by
    have : t * K ≤ ε := by rwa [le_div_iff₀ hKpos] at htK
    nlinarith [sq_nonneg ‖d‖]
  linarith

theorem aux_cgm_nonexp {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hD : Convex ℝ D) (hh : ConvexOn ℝ D h)
    (v1 v2 p1 p2 : EuclideanSpace ℝ (Fin n))
    (h1 : IsProxPoint D h v1 p1) (h2 : IsProxPoint D h v2 p2) : ‖p1 - p2‖ ≤ ‖v1 - v2‖ := by
  have e1 := aux_cgm_vi D h hD hh v1 p1 h1 p2 h2.1
  have e2 := aux_cgm_vi D h hD hh v2 p2 h2 p1 h1.1
  have hsum : ‖p1 - p2‖ ^ 2 ≤ ⟪v1 - v2, p1 - p2⟫ := by
    have hid : ⟪p1 - v1, p2 - p1⟫ + ⟪p2 - v2, p1 - p2⟫ = ⟪v1 - v2, p1 - p2⟫ - ‖p1 - p2‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      have : p2 - p1 = -(p1 - p2) := by abel
      rw [this, inner_neg_right, neg_add_eq_sub, ← inner_sub_left, ← inner_sub_left]
      congr 1
      abel
    linarith
  have hcs : ⟪v1 - v2, p1 - p2⟫ ≤ ‖v1 - v2‖ * ‖p1 - p2‖ := real_inner_le_norm _ _
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ‖p1 - p2‖ := lt_of_le_of_lt (norm_nonneg _) hcon
  nlinarith

theorem aux_cgs_foc {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (hD : Convex ℝ D) (hconv : ConvexOn ℝ D h)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : IsMinimizer g D h xs) :
    ∀ y ∈ D, 0 ≤ h y - h xs + ⟪gradient g xs, y - xs⟫ := by
  intro y hy
  let ψ : ℝ → ℝ := fun t => g (xs + t • (y - xs))
  have hψ : HasDerivAt ψ ⟪gradient g xs, y - xs⟫ 0 := by
    have h1 : HasDerivAt (fun t : ℝ => xs + t • (y - xs)) (y - xs) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - xs)).const_add xs
    have h2 : HasFDerivAt g (fderiv ℝ g (xs + (0:ℝ) • (y - xs))) (xs + (0:ℝ) • (y - xs)) :=
      (hg _).hasFDerivAt
    have := h2.comp_hasDerivAt (0:ℝ) h1
    simp only [zero_smul, add_zero] at this
    rw [inner_gradient_left (𝕜 := ℝ) (f := g) (x := xs) (y := y - xs)]
    exact this
  have hT := hψ.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), -(h y - h xs) ≤ t⁻¹ • (ψ (0 + t) - ψ 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have heq : (1 - t) • xs + t • y = xs + t • (y - xs) := by module
    have hzt : xs + t • (y - xs) ∈ D := by
      have := hD hxs.1 hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
      rwa [heq] at this
    have hmin := hxs.2 _ hzt
    have hc := hconv.2 hxs.1 hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    rw [heq, smul_eq_mul, smul_eq_mul] at hc
    simp only [ψ, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    nlinarith
  have := ge_of_tendsto hT hev
  linarith

/-- A minimizer is a fixed point of the forward-backward map. -/
theorem aux_cgs_fixed {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (hD : Convex ℝ D) (hconv : ConvexOn ℝ D h)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : IsMinimizer g D h xs) :
    IsProxPoint D h (xs - gradient g xs) xs := by
  refine ⟨hxs.1, fun z hz => ?_⟩
  have hb := aux_cgs_foc hg hD hconv hxs z hz
  have e1 : xs - (xs - gradient g xs) = gradient g xs := by abel
  have e2 : z - (xs - gradient g xs) = (z - xs) + gradient g xs := by abel
  rw [e1, e2, norm_add_sq_real]
  have := sq_nonneg ‖z - xs‖
  rw [real_inner_comm] at hb
  nlinarith

open Classical in
/-- Existence of a prox point, given an affine minorant of `h` on `D`. -/
theorem aux_pncgs_exists {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : IsProperClosedConvex D h) (t : ℝ) (ht : 0 < t)
    (v : EuclideanSpace ℝ (Fin n)) : ∃ p, IsProxPoint D (fun y => t * h y) v p := by
  obtain ⟨⟨y0, hy0⟩, hDc, hconv, hlsc⟩ := hh
  -- local lower bound from lower semicontinuity
  have hev := hlsc y0 ((h y0 - 1 : ℝ) : EReal)
    (by simp only [if_pos hy0]; exact EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hloc : ∀ y ∈ D, dist y y0 < r → h y0 - 1 < h y := by
    intro y hy hdist
    have := hball hdist
    simp only [if_pos hy] at this
    exact EReal.coe_lt_coe_iff.1 this
  -- global affine-type lower bound
  have hlow : ∀ y ∈ D, h y0 - 1 - 2 / r * ‖y - y0‖ ≤ h y := by
    intro y hy
    by_cases hyr : ‖y - y0‖ < r
    · have := hloc y hy (by rwa [dist_eq_norm])
      have : 0 ≤ 2 / r * ‖y - y0‖ := by positivity
      linarith
    · push Not at hyr
      have hρpos : 0 < ‖y - y0‖ := lt_of_lt_of_le hr hyr
      have hl0 : 0 < r / (2 * ‖y - y0‖) := by positivity
      have hl1 : r / (2 * ‖y - y0‖) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hzD : (1 - r / (2 * ‖y - y0‖)) • y0 + (r / (2 * ‖y - y0‖)) • y ∈ D :=
        hDc hy0 hy (by linarith) hl0.le (by ring)
      have hconvz := hconv.2 hy0 hy (by linarith : 0 ≤ 1 - r / (2 * ‖y - y0‖)) hl0.le
        (by ring : 1 - r / (2 * ‖y - y0‖) + r / (2 * ‖y - y0‖) = 1)
      simp only [smul_eq_mul] at hconvz
      have hdz : dist ((1 - r / (2 * ‖y - y0‖)) • y0 + (r / (2 * ‖y - y0‖)) • y) y0 < r := by
        rw [dist_eq_norm]
        have : (1 - r / (2 * ‖y - y0‖)) • y0 + (r / (2 * ‖y - y0‖)) • y - y0
            = (r / (2 * ‖y - y0‖)) • (y - y0) := by module
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
        have : r / (2 * ‖y - y0‖) * ‖y - y0‖ = r / 2 := by field_simp
        linarith
      have hz := hloc _ hzD hdz
      have e : r / (2 * ‖y - y0‖) * (2 / r * ‖y - y0‖) = 1 := by field_simp
      have key : 0 < r / (2 * ‖y - y0‖) * (h y - h y0 + 2 / r * ‖y - y0‖) := by
        nlinarith
      have := pos_of_mul_pos_right key hl0.le
      linarith
  -- coercivity
  have hc : 0 ≤ 2 / r := by positivity
  have htc : 0 ≤ t * (2 / r) := by positivity
  have ha0 : 0 ≤ ‖y0 - v‖ := norm_nonneg _
  have hcoer : ∀ z ∈ D, 2 * ‖y0 - v‖ + 2 * (t * (2 / r)) + 2 * t + 1 < ‖z - y0‖ →
      t * h y0 + ‖y0 - v‖ ^ 2 / 2 < t * h z + ‖z - v‖ ^ 2 / 2 := by
    intro z hz hR
    have h1 := hlow z hz
    have h2 : ‖z - y0‖ - ‖y0 - v‖ ≤ ‖z - v‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub z v y0
      rw [norm_sub_rev v y0] at this
      linarith
    have h3 : (‖z - y0‖ - ‖y0 - v‖) ^ 2 ≤ ‖z - v‖ ^ 2 :=
      pow_le_pow_left₀ (by linarith) h2 2
    have h4 : 1 < ‖z - y0‖ - 2 * ‖y0 - v‖ - 2 * (t * (2 / r)) := by linarith
    have h5 : ‖z - y0‖ * 1 < ‖z - y0‖ * (‖z - y0‖ - 2 * ‖y0 - v‖ - 2 * (t * (2 / r))) :=
      mul_lt_mul_of_pos_left h4 (by linarith)
    have h6 : t * (h y0 - 1 - 2 / r * ‖z - y0‖) ≤ t * h z := mul_le_mul_of_nonneg_left h1 ht.le
    nlinarith
  -- minimize on a compact ball
  set R := 2 * ‖y0 - v‖ + 2 * (t * (2 / r)) + 2 * t + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hcont : LowerSemicontinuous fun z : EuclideanSpace ℝ (Fin n) =>
      ((‖z - v‖ ^ 2 / (2 * t) : ℝ) : EReal) :=
    (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
  have hΨ := hlsc.add' hcont (fun x => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _)))
  have hy0K : y0 ∈ Metric.closedBall y0 R := Metric.mem_closedBall_self hR0
  obtain ⟨p, hpK, hpmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨y0, hy0K⟩
    (isCompact_closedBall y0 R) (hΨ.lowerSemicontinuousOn _)
  have hpy0 := isMinOn_iff.1 hpmin y0 hy0K
  simp only [if_pos hy0] at hpy0
  have hpD : p ∈ D := by
    by_contra hpD
    simp only [if_neg hpD, EReal.top_add_coe] at hpy0
    rw [← EReal.coe_add] at hpy0
    exact EReal.coe_ne_top _ (top_le_iff.1 hpy0)
  have hreal : ∀ z ∈ D, z ∈ Metric.closedBall y0 R →
      h p + ‖p - v‖ ^ 2 / (2 * t) ≤ h z + ‖z - v‖ ^ 2 / (2 * t) := by
    intro z hz hzK
    have := isMinOn_iff.1 hpmin z hzK
    simp only [if_pos hz, if_pos hpD] at this
    rw [← EReal.coe_add, ← EReal.coe_add] at this
    exact EReal.coe_le_coe_iff.1 this
  have hscale : ∀ z, t * (h z + ‖z - v‖ ^ 2 / (2 * t)) = t * h z + ‖z - v‖ ^ 2 / 2 := by
    intro z
    field_simp
  refine ⟨p, hpD, fun z hz => ?_⟩
  show t * h p + ‖p - v‖ ^ 2 / 2 ≤ t * h z + ‖z - v‖ ^ 2 / 2
  have hp' : t * h p + ‖p - v‖ ^ 2 / 2 ≤ t * h y0 + ‖y0 - v‖ ^ 2 / 2 := by
    rw [← hscale, ← hscale]; exact mul_le_mul_of_nonneg_left (hreal y0 hy0 hy0K) ht.le
  by_cases hzK : z ∈ Metric.closedBall y0 R
  · rw [← hscale, ← hscale]; exact mul_le_mul_of_nonneg_left (hreal z hz hzK) ht.le
  · have : R < ‖z - y0‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hzK
      exact hzK
    have := hcoer z hz this
    linarith


lemma pni_grad_mono {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ)
    (hsc : ∀ x y, g x + ⟪gradient g x, y-x⟫ + m/2*‖x-y‖^2 ≤ g y) (x y : EuclideanSpace ℝ (Fin n)) :
    m*‖x-y‖^2 ≤ ⟪gradient g x-gradient g y,x-y⟫ := by
  have h1 := hsc x y
  have h2 := hsc y x
  rw [norm_sub_rev y x] at h2
  have he : y-x = -(x-y) := by abel
  rw [he,inner_neg_right] at h1
  rw [inner_sub_left]
  linarith
lemma pni_hessian_lower {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ)
    (hg : ContDiff ℝ 2 g) (hsc : ∀ x y, g x + ⟪gradient g x, y-x⟫ + m/2*‖x-y‖^2 ≤ g y) (x v : EuclideanSpace ℝ (Fin n)) :
    m*‖v‖^2 ≤ ⟪hessian g x v,v⟫ := by
  let f : ℝ → ℝ := fun t => ⟪gradient g (x+t • v),v⟫
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd : HasDerivAt f ⟪hessian g x v,v⟫ 0 := by
    have hh := (aux_cgm_hasFDerivAt_grad g hg (x+(0:ℝ) • v)).comp_hasDerivAt (0:ℝ) hl
    convert! hh.inner ℝ (hasDerivAt_const (0:ℝ) v) using 1 <;> simp [f,hessian]
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hm := pni_grad_mono g m hsc (x+t • v) x
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,mul_pow,inner_smul_right,inner_sub_left] at hm
  change m*‖v‖^2 ≤ t⁻¹*(f (0+t)-f 0)
  simp only [f,zero_add,zero_smul,add_zero]
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ ht0).mpr
  exact (mul_le_mul_iff_left₀ ht0).mp (by nlinarith [hm])
lemma pni_hessian_norm {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖) (x : EuclideanSpace ℝ (Fin n)) :
    ‖hessian g x‖ ≤ L := norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun y => hlip y x))

lemma pni_scaled_eq {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : ℝ) (y : EuclideanSpace ℝ (Fin n)) (hg : DifferentiableAt ℝ g y) :
    scaledStep g D h M y = y-prox D (fun z => h z/M) (y-M⁻¹ • gradient g y) := by
  have he : (fun z => g z/M) = fun z => M⁻¹*g z := by funext z; ring
  have hd : gradient (fun z => g z/M) y = M⁻¹ • gradient g y := by
    rw [he]
    unfold gradient
    rw [fderiv_const_mul hg]
    change (InnerProductSpace.toDual ℝ _).symm (M⁻¹ • fderiv ℝ g y) = _
    exact map_smul _ _ _
  simp only [scaledStep, compGradStep, inv_one, one_smul, one_mul, hd]

lemma pni_scaled_convex {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : IsProperClosedConvex D h)
    {M : ℝ} (hM : 0 < M) : ConvexOn ℝ D (fun z => h z/M) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.2.2.1.smul (inv_nonneg.mpr hM.le)

lemma pni_scaled_spec {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : IsProperClosedConvex D h)
    {M : ℝ} (hM : 0 < M) (v : EuclideanSpace ℝ (Fin n)) :
    IsProxPoint D (fun z => h z/M) v (prox D (fun z => h z/M) v) := by
  apply Classical.epsilon_spec
  simpa only [div_eq_mul_inv, mul_comm] using aux_pncgs_exists D h hh M⁻¹ (inv_pos.mpr hM) v

lemma pni_scaled_vi {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : IsProperClosedConvex D h)
    {M : ℝ} (hM : 0 < M) (y w : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ D) :
    let p := prox D (fun z => h z/M) (y-M⁻¹ • w)
    h p-h z ≤ ⟪w-M • (y-p),z-p⟫ := by
  dsimp only
  let p := prox D (fun z => h z/M) (y-M⁻¹ • w)
  have hv := aux_cgm_vi D (fun z => h z/M) hh.2.1 (pni_scaled_convex hh hM)
    (y-M⁻¹ • w) p (pni_scaled_spec hh hM _) z hz
  have hmul := mul_le_mul_of_nonneg_left hv hM.le
  have hne : M ≠ 0 := ne_of_gt hM
  change h p-h z ≤ ⟪w-M • (y-p),z-p⟫
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right] at hmul ⊢
  field_simp at hmul
  nlinarith

lemma pni_fixed {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (hh : IsProperClosedConvex D h)
    {xs : EuclideanSpace ℝ (Fin n)} (hs : IsMinimizer g D h xs)
    {M : ℝ} (hM : 0 < M) :
    IsProxPoint D (fun z => h z/M) (xs-M⁻¹ • gradient g xs) xs := by
  refine ⟨hs.1, fun z hz => ?_⟩
  have hf := aux_cgs_foc hg hh.2.1 hh.2.2.1 hs z hz
  have h1 : xs-(xs-M⁻¹ • gradient g xs) = M⁻¹ • gradient g xs := by abel
  have h2 : z-(xs-M⁻¹ • gradient g xs) = (z-xs)+M⁻¹ • gradient g xs := by abel
  rw [h1,h2,norm_add_sq_real,inner_smul_right]
  rw [← real_inner_comm (z-xs)]
  have hm := mul_nonneg (inv_nonneg.mpr hM.le) hf
  have hn := sq_nonneg ‖z-xs‖
  simp only [div_eq_mul_inv]
  nlinarith

lemma pni_norm_upper {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m L1 L2 M : ℝ} (hg : SmoothPartAssumptions g m L1 L2)
    (hh : IsProperClosedConvex D h) {xs : EuclideanSpace ℝ (Fin n)}
    (hs : IsMinimizer g D h xs) (hM : 0 < M) (y : EuclideanSpace ℝ (Fin n)) :
    ‖scaledStep g D h M y‖ ≤ (2+L1/M)*‖y-xs‖ := by
  rw [pni_scaled_eq g D h M y (hg.contDiff.differentiable (by norm_num) y)]
  let p := prox D (fun z => h z/M) (y-M⁻¹ • gradient g y)
  have hp := pni_scaled_spec hh hM (y-M⁻¹ • gradient g y)
  have hq := pni_fixed (hg.contDiff.differentiable (by norm_num)) hh hs hM
  have hn := aux_cgm_nonexp D (fun z => h z/M) hh.2.1 (pni_scaled_convex hh hM)
    _ _ p xs hp hq
  have he : (y-M⁻¹ • gradient g y)-(xs-M⁻¹ • gradient g xs) =
      (y-xs)-M⁻¹ • (gradient g y-gradient g xs) := by rw [smul_sub]; abel
  rw [he] at hn
  have hu := norm_sub_le (y-xs) (M⁻¹ • (gradient g y-gradient g xs))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)] at hu
  have hl := mul_le_mul_of_nonneg_left (hg.grad_lipschitz y xs) (inv_nonneg.mpr hM.le)
  have ht : ‖y-p‖ ≤ ‖y-xs‖+‖p-xs‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub y xs p
    rwa [norm_sub_rev xs p] at this
  change ‖y-p‖ ≤ _
  simp only [div_eq_mul_inv]
  nlinarith

lemma pni_residual_inverse {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : IsProperClosedConvex D h)
    {M m L T : ℝ} (hM : 0 < M) (hm : 0 < m) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (y xs w gs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ D)
    (hfoc : ∀ z ∈ D, 0 ≤ h z-h xs+⟪gs,z-xs⟫)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hlo : ∀ v, m*‖v‖^2 ≤ ⟪H v,v⟫) (hhi : ‖H‖ ≤ L)
    (he : ‖w-gs-H (y-xs)‖ ≤ T) :
    ‖y-xs‖ ≤ (1+(M+L)/m)*‖y-prox D (fun z => h z/M) (y-M⁻¹ • w)‖+T/m := by
  let p := prox D (fun z => h z/M) (y-M⁻¹ • w)
  let r := y-p
  let d := p-xs
  let e := w-gs-H (y-xs)
  have hp := pni_scaled_spec hh hM (y-M⁻¹ • w)
  have hv := pni_scaled_vi hh hM y w xs hxs
  change h p-h xs ≤ ⟪w-M • r,xs-p⟫ at hv
  have hf := hfoc p hp.1
  have hid : w-gs = H d+H r+e := by
    dsimp [r,d,e]
    rw [← map_add]
    have : (p-xs)+(y-p) = y-xs := by abel
    rw [this]; abel
  have hb : ⟪H d,d⟫ ≤ ⟪M • r-H r-e,d⟫ := by
    have hh1 : xs-p = -d := by dsimp [d]; abel
    rw [hh1,inner_neg_right,inner_sub_left] at hv
    change 0 ≤ h p-h xs+⟪gs,d⟫ at hf
    have heq : ⟪M • r-w,d⟫+⟪gs,d⟫ = ⟪M • r-H r-e,d⟫-⟪H d,d⟫ := by
      rw [← inner_add_left]
      have : M • r-w+gs = (M • r-H r-e)-H d := by
        calc M • r-w+gs = M • r-(w-gs) := by abel
          _ = _ := by rw [hid]; abel
      rw [this,inner_sub_left]
    simp only [inner_sub_left] at heq ⊢
    linarith
  have hn : ‖M • r-H r-e‖ ≤ (M+L)*‖r‖+T := by
    have h1 := norm_sub_le (M • r-H r) e
    have h2 := norm_sub_le (M • r) (H r)
    have h3 := H.le_opNorm r
    have h4 := mul_le_mul_of_nonneg_right hhi (norm_nonneg r)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hM] at h2
    change ‖e‖ ≤ T at he
    nlinarith
  have hbound : ‖d‖ ≤ ((M+L)*‖r‖+T)/m := by
    have h1 := (hlo d).trans hb
    have h2 := real_inner_le_norm (M • r-H r-e) d
    have h3 := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
    apply (le_div_iff₀ hm).mpr
    by_cases hd : ‖d‖ = 0
    · rw [hd,zero_mul]; positivity
    · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      nlinarith
  have ht : ‖y-xs‖ ≤ ‖r‖+‖d‖ := by
    have heq : y-xs = r+d := by dsimp [r,d]; abel
    rw [heq]; exact norm_add_le _ _
  change ‖y-xs‖ ≤ (1+(M+L)/m)*‖r‖+T/m
  have halg : ‖r‖+((M+L)*‖r‖+T)/m = (1+(M+L)/m)*‖r‖+T/m := by ring
  rw [← halg]
  linarith

lemma pni_model_diff {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Differentiable ℝ (quadModel g x) := by
  have hl : Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin n) => y-x) := differentiable_id.sub_const x
  exact ((differentiable_const _).add ((differentiable_const _).inner ℝ hl)).add
    ((hl.inner ℝ ((hessian g x).differentiable.comp hl)).const_mul _)

lemma pni_model_error {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m L1 L2 M : ℝ} (hg : SmoothPartAssumptions g m L1 L2)
    (hh : IsProperClosedConvex D h) {xs : EuclideanSpace ℝ (Fin n)}
    (hs : IsMinimizer g D h xs) (hM : 0 < M) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖y-xs‖ ≤ (1+(M+L1)/m)*‖scaledStep (quadModel g x) D h M y‖
      +L2/(2*m)*‖x-xs‖^2 := by
  have ht := aux_cgm_taylor g L2 hg.contDiff hg.hessian_lipschitz x xs
  have he : gradient (quadModel g x) y-gradient g xs-hessian g x (y-xs) =
      -(gradient g xs-gradient g x-hessian g x (xs-x)) := by
    rw [aux_cgm_quad_grad g hg.contDiff]
    have hh : hessian g x (y-x)-hessian g x (y-xs) = hessian g x (xs-x) := by
      rw [← map_sub]; congr 1; abel
    calc _ = gradient g x-gradient g xs+(hessian g x (y-x)-hessian g x (y-xs)) := by abel
      _ = _ := by rw [hh]; abel
  have hr := pni_residual_inverse hh hM hg.m_pos hg.L1_nonneg
    (show 0 ≤ L2/2*‖x-xs‖^2 by have := hg.L2_nonneg; positivity)
    y xs (gradient (quadModel g x) y) (gradient g xs) hs.1
    (aux_cgs_foc (hg.contDiff.differentiable (by norm_num)) hh.2.1 hh.2.2.1 hs)
    (hessian g x) (pni_hessian_lower g m hg.contDiff hg.strongConvex x)
    (pni_hessian_norm g L1 hg.L1_nonneg hg.grad_lipschitz x)
    (by rw [he,norm_neg,norm_sub_rev x xs]; exact ht)
  rw [pni_scaled_eq _ D h M y (pni_model_diff g x y)]
  convert hr using 1 <;> ring

lemma pni_actual_inverse {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m L1 L2 M : ℝ} (hg : SmoothPartAssumptions g m L1 L2)
    (hh : IsProperClosedConvex D h) {xs : EuclideanSpace ℝ (Fin n)}
    (hs : IsMinimizer g D h xs) (hM : 0 < M) (y : EuclideanSpace ℝ (Fin n)) :
    ‖y-xs‖ ≤ (1+(M+L1)/m)*‖scaledStep g D h M y‖ := by
  rw [pni_scaled_eq g D h M y (hg.contDiff.differentiable (by norm_num) y)]
  let p := prox D (fun z => h z/M) (y-M⁻¹ • gradient g y)
  let r := y-p
  let d := p-xs
  have hp := pni_scaled_spec hh hM (y-M⁻¹ • gradient g y)
  have hv := pni_scaled_vi hh hM y (gradient g y) xs hs.1
  change h p-h xs ≤ ⟪gradient g y-M • r,xs-p⟫ at hv
  have hf := aux_cgs_foc (hg.contDiff.differentiable (by norm_num)) hh.2.1 hh.2.2.1 hs p hp.1
  have hm := pni_grad_mono g m hg.strongConvex p xs
  have hb : m*‖d‖^2 ≤ ⟪M • r-(gradient g y-gradient g p),d⟫ := by
    have he : xs-p = -d := by dsimp [d]; abel
    rw [he,inner_neg_right,inner_sub_left] at hv
    change 0 ≤ h p-h xs+⟪gradient g xs,d⟫ at hf
    change m*‖d‖^2 ≤ ⟪gradient g p-gradient g xs,d⟫ at hm
    simp only [inner_sub_left] at hm ⊢
    linarith
  have hn : ‖M • r-(gradient g y-gradient g p)‖ ≤ (M+L1)*‖r‖ := by
    have h1 := norm_sub_le (M • r) (gradient g y-gradient g p)
    have h2 := hg.grad_lipschitz y p
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hM] at h1
    change ‖gradient g y-gradient g p‖ ≤ L1*‖r‖ at h2
    nlinarith
  have hd : m*‖d‖ ≤ (M+L1)*‖r‖ := by
    have h1 := real_inner_le_norm (M • r-(gradient g y-gradient g p)) d
    have h2 := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
    by_cases hd : ‖d‖ = 0
    · rw [hd,mul_zero]; have := hg.L1_nonneg; positivity
    · have hdp : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      nlinarith
  have ht : ‖y-xs‖ ≤ ‖r‖+‖d‖ := by
    have he : y-xs = r+d := by dsimp [r,d]; abel
    rw [he]; exact norm_add_le _ _
  change ‖y-xs‖ ≤ (1+(M+L1)/m)*‖r‖
  have hh1 := (le_div_iff₀ hg.m_pos).mpr (show ‖d‖*m ≤ (M+L1)*‖r‖ by nlinarith [hd])
  have he : ‖r‖+(M+L1)*‖r‖/m = (1+(M+L1)/m)*‖r‖ := by ring
  rw [← he]; linarith

lemma pni_model_approx {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m L1 L2 M : ℝ} (hg : SmoothPartAssumptions g m L1 L2)
    (hh : IsProperClosedConvex D h) (hM : 0 < M) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖scaledStep (quadModel g x) D h M y-scaledStep g D h M y‖ ≤ L2/(2*M)*‖y-x‖^2 := by
  rw [pni_scaled_eq _ D h M y (pni_model_diff g x y),
    pni_scaled_eq g D h M y (hg.contDiff.differentiable (by norm_num) y),sub_sub_sub_cancel_left]
  have hn := aux_cgm_nonexp D (fun z => h z/M) hh.2.1 (pni_scaled_convex hh hM)
    (y-M⁻¹ • gradient g y) (y-M⁻¹ • gradient (quadModel g x) y) _ _
    (pni_scaled_spec hh hM _) (pni_scaled_spec hh hM _)
  have he : (y-M⁻¹ • gradient g y)-(y-M⁻¹ • gradient (quadModel g x) y) =
      -M⁻¹ • (gradient g y-gradient g x-hessian g x (y-x)) := by
    rw [aux_cgm_quad_grad g hg.contDiff]
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hM)] at hn
  have ht := mul_le_mul_of_nonneg_left
    (aux_cgm_taylor g L2 hg.contDiff hg.hessian_lipschitz x y) (inv_nonneg.mpr hM.le)
  calc _ ≤ M⁻¹*‖gradient g y-gradient g x-hessian g x (y-x)‖ := hn
    _ ≤ M⁻¹*(L2/2*‖y-x‖^2) := ht
    _ = _ := by ring

lemma pni_run_bound {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m L1 L2 M : ℝ} (hg : SmoothPartAssumptions g m L1 L2)
    (hh : IsProperClosedConvex D h) {xs : EuclideanSpace ℝ (Fin n)}
    (hs : IsMinimizer g D h xs) (hM : 0 < M)
    {η : ℕ → ℝ} {x Δ : ℕ → EuclideanSpace ℝ (Fin n)}
    (hη : ∀ k, 0 ≤ η k) (hr : IsInexactProxNewtonRun g D h M η x Δ) (k : ℕ) :
    ‖x (k+1)-xs‖ ≤ ((1+(M+L1)/m)*(2+L1/M)*η k+L2/(2*m)*‖x k-xs‖)*‖x k-xs‖ := by
  have h1 := pni_model_error hg hh hs hM (x k) (x (k+1))
  have h2 := (hr.2 k).2.1
  change ‖scaledStep (quadModel g (x k)) D h M (x k+Δ k)‖ ≤ η k*‖scaledStep g D h M (x k)‖ at h2
  rw [← (hr.2 k).2.2] at h2
  have h3 := mul_le_mul_of_nonneg_left (pni_norm_upper hg hh hs hM (x k)) (hη k)
  have hK : 0 ≤ 1+(M+L1)/m := by have := hg.m_pos; have := hg.L1_nonneg; positivity
  have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hK
  nlinarith

lemma pni_ew_nonneg {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m M : ℝ} (hm : 0 < m) (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    0 ≤ ewForcingTerm g D h M m x k := by
  unfold ewForcingTerm
  apply le_min <;> positivity

lemma pni_ew_bound {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {m L1 L2 M : ℝ} (hg : SmoothPartAssumptions g m L1 L2)
    (hh : IsProperClosedConvex D h) {xs : EuclideanSpace ℝ (Fin n)}
    (hs : IsMinimizer g D h xs) (hM : 0 < M)
    {η : ℕ → ℝ} {x Δ : ℕ → EuclideanSpace ℝ (Fin n)}
    (hη : ∀ k, 0 ≤ η k) (hr : IsInexactProxNewtonRun g D h M η x Δ) (k : ℕ)
    (hcap : η k ≤ m/2) (he : ‖x k-xs‖ ≤ 1) :
    let K := 1+(M+L1)/m
    let A := K*(2+L1/M)
    let B := L2/(2*m)
    ewForcingTerm g D h M m x k ≤ L2/(2*M)*K*(1+A*(m/2)+B)^2*‖x k-xs‖ := by
  dsimp only
  let K := 1+(M+L1)/m
  let A := K*(2+L1/M)
  let B := L2/(2*m)
  let F := 1+A*(m/2)+B
  have hm := hg.m_pos
  have hL1 := hg.L1_nonneg
  have hL2 := hg.L2_nonneg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hrec := pni_run_bound hg hh hs hM hη hr k
  change ‖x (k+1)-xs‖ ≤ (A*η k+B*‖x k-xs‖)*‖x k-xs‖ at hrec
  have hcoeff : A*η k+B*‖x k-xs‖ ≤ A*(m/2)+B := by
    have h1 := mul_le_mul_of_nonneg_left hcap hA
    have h2 := mul_le_mul_of_nonneg_left he hB
    linarith
  have he1 := hrec.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
  have hstep : ‖x (k+1)-x k‖ ≤ F*‖x k-xs‖ := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (x (k+1)) xs (x k)
    rw [norm_sub_rev xs (x k)] at htri
    dsimp [F]
    nlinarith
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hstep 2
  rw [mul_pow] at hsquare
  have happ := pni_model_approx hg hh hM (x k) (x (k+1))
  have hinv := pni_actual_inverse hg hh hs hM (x k)
  change ‖x k-xs‖ ≤ K*‖scaledStep g D h M (x k)‖ at hinv
  change ewForcingTerm g D h M m x k ≤ L2/(2*M)*K*F^2*‖x k-xs‖
  unfold ewForcingTerm
  apply (min_le_right _ _).trans
  by_cases hz : ‖scaledStep g D h M (x k)‖ = 0
  · rw [hz,div_zero]; positivity
  · have hp : 0 < ‖scaledStep g D h M (x k)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    have hD : 0 ≤ L2/(2*M) := by positivity
    have hsq : ‖x k-xs‖^2 ≤ K*‖scaledStep g D h M (x k)‖*‖x k-xs‖ := by
      have := mul_le_mul_of_nonneg_right hinv (norm_nonneg (x k-xs))
      nlinarith
    calc _ ≤ L2/(2*M)*‖x (k+1)-x k‖^2 := happ
      _ ≤ L2/(2*M)*(F^2*‖x k-xs‖^2) := mul_le_mul_of_nonneg_left hsquare hD
      _ ≤ L2/(2*M)*(F^2*(K*‖scaledStep g D h M (x k)‖*‖x k-xs‖)) := by gcongr
      _ = _ := by ring

end ProxNewton.Inexact

open Filter
open scoped Topology
namespace CScalar

theorem geometric_of_step (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (q : ℝ)
    (hq : 0 ≤ q) (hs : ∀ k, e (k+1) ≤ q*e k) :
    ∀ k, e k ≤ q^k*e 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      e (k+1) ≤ q*e k := hs k
      _ ≤ q*(q^k*e 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q^(k+1)*e 0 := by rw [pow_succ]; ring

theorem zero_of_step (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hs : ∀ k, e (k+1) ≤ q*e k) :
    Tendsto e atTop (𝓝 0) := by
  apply squeeze_zero he (geometric_of_step e he q hq hs)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (e 0)

theorem contraction (A B r q : ℝ) (hB : 0 ≤ B) (hr : 0 ≤ r) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (eta e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (h0 : e 0 ≤ r)
    (hrec : ∀ k, e (k+1) ≤ (A*eta k+B*e k)*e k)
    (hcap : ∀ k, A*eta k+B*r ≤ q) :
    (∀ k, e k ≤ r) ∧ (∀ k, e (k+1) ≤ q*e k) ∧ (∀ k, e k ≤ q^k*e 0) := by
  have hb : ∀ k, e k ≤ r := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hcoef : A*eta k+B*e k ≤ q := by nlinarith [hcap k]
      have hn := (hrec k).trans (mul_le_mul_of_nonneg_right hcoef (he k))
      exact hn.trans ((mul_le_of_le_one_left (he k) hq1).trans ih)
  have hs (k : ℕ) : e (k+1) ≤ q*e k := by
    apply (hrec k).trans
    apply mul_le_mul_of_nonneg_right _ (he k)
    nlinarith [hcap k,hb k]
  exact ⟨hb,hs,geometric_of_step e he q hq hs⟩

theorem superlinear (A B : ℝ) (eta e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k)
    (hrec : ∀ k, e (k+1) ≤ (A*eta k+B*e k)*e k)
    (heta : Tendsto eta atTop (𝓝 0)) (he0 : Tendsto e atTop (𝓝 0)) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, e (k+1) ≤ eps*e k := by
  have hc : Tendsto (fun k => A*eta k+B*e k) atTop (𝓝 0) := by
    simpa using (heta.const_mul A).add (he0.const_mul B)
  intro eps heps
  filter_upwards [hc.eventually_le_const heps] with k hk
  exact (hrec k).trans (mul_le_mul_of_nonneg_right hk (he k))

theorem uniform_local (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ etaBar r : ℝ, 0 < etaBar ∧ 0 < r ∧
      ∀ eta e : ℕ → ℝ, (∀ k, 0 ≤ e k) → e 0 ≤ r →
        (∀ k, eta k ≤ etaBar) →
        (∀ k, e (k+1) ≤ (A*eta k+B*e k)*e k) →
        Tendsto e atTop (𝓝 0) ∧ ∀ k, e (k+1) ≤ (1/2:ℝ)*e k := by
  let r := 1/(4*(B+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hBr : B*r ≤ 1/4 := by
    have hden : 0 < 4*(B+1) := by positivity
    dsimp [r]
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  refine ⟨1/(4*A),r,by positivity,hr,?_⟩
  intro eta e he h0 hcap hrec
  have hc (k : ℕ) : A*eta k+B*r ≤ (1/2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hcap k) hA.le
    have hid : A*(1/(4*A))=(1/4:ℝ) := by field_simp
    rw [hid] at hh
    linarith
  have hh := contraction A B r (1/2) hB hr.le (by norm_num) (by norm_num) eta e he h0 hrec hc
  exact ⟨zero_of_step e he (1/2) (by norm_num) (by norm_num) hh.2.1,hh.2.1⟩


theorem prefix_barrier (A B R K : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) (hK : 1 ≤ K)
    (eta e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (N : ℕ) (h0 : e 0 ≤ R/K^N)
    (hrec : ∀ k, e (k+1) ≤ (A*eta k+B*e k)*e k)
    (hcap : ∀ k, A*eta k+B*R ≤ K) : e N ≤ R := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hinit : K^N*e 0 ≤ R := by
    have hh := (le_div_iff₀ (pow_pos hK0 N)).mp h0
    simpa only [mul_comm] using hh
  have hg : ∀ k, k ≤ N → e k ≤ K^k*e 0 := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hik := ih (by omega)
      have hpow : K^k ≤ K^N := pow_le_pow_right₀ hK (by omega)
      have hkr : e k ≤ R := hik.trans ((mul_le_mul_of_nonneg_right hpow (he 0)).trans hinit)
      have hcoef : A*eta k+B*e k ≤ K := by nlinarith [hcap k]
      calc
        e (k+1) ≤ (A*eta k+B*e k)*e k := hrec k
        _ ≤ K*e k := mul_le_mul_of_nonneg_right hcoef (he k)
        _ ≤ K*(K^k*e 0) := mul_le_mul_of_nonneg_left hik hK0.le
        _ = K^(k+1)*e 0 := by rw [pow_succ]; ring
  exact (hg N le_rfl).trans hinit

theorem vanishing_local (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧ ∀ e : ℕ → ℝ, (∀ k, 0 ≤ e k) → e 0 ≤ r →
      (∀ k, e (k+1) ≤ (A*eta k+B*e k)*e k) →
      Tendsto e atTop (𝓝 0) ∧ ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, e (k+1) ≤ eps*e k := by
  let R := 1/(4*(B+1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hBR : B*R ≤ 1/4 := by
    dsimp [R]
    rw [mul_one_div]
    apply (div_le_iff₀ (show 0 < 4*(B+1) by positivity)).mpr
    linarith
  obtain ⟨U,hU⟩ := heta.bddAbove_range
  let K := max 1 (A*U+B*R)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hcap (k : ℕ) : A*eta k+B*R ≤ K := by
    have hh := hU (Set.mem_range_self k)
    have hm := le_max_right (1:ℝ) (A*U+B*R)
    dsimp [K]
    nlinarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (heta.eventually_le_const (show (0:ℝ) < 1/(4*A) by positivity))
  refine ⟨R/K^N,div_pos hR (pow_pos hK0 N),?_⟩
  intro e he h0 hrec
  have hEN : e N ≤ R := prefix_barrier A B R K hB hR.le hK eta e he N h0 hrec hcap
  have htailcap (k : ℕ) : A*eta (k+N)+B*R ≤ (1/2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hN (k+N) (by omega)) hA.le
    have hid : A*(1/(4*A))=(1/4:ℝ) := by field_simp
    rw [hid] at hh
    linarith
  have htailrec (k : ℕ) : e ((k+1)+N) ≤ (A*eta (k+N)+B*e (k+N))*e (k+N) := by
    simpa only [Nat.add_right_comm] using hrec (k+N)
  have hh := contraction A B R (1/2) hB hR.le (by norm_num) (by norm_num)
    (fun k => eta (k+N)) (fun k => e (k+N)) (fun k => he _) (by simpa using hEN) htailrec htailcap
  have helim : Tendsto e atTop (𝓝 0) := (tendsto_add_atTop_iff_nat N).mp
    (zero_of_step (fun k => e (k+N)) (fun k => he _) (1/2) (by norm_num) (by norm_num) hh.2.1)
  exact ⟨helim,superlinear A B eta e he hrec heta helim⟩



theorem ew_local (A B C H : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ ∀ eta e : ℕ → ℝ, (∀ k, 0 ≤ eta k) → (∀ k, 0 ≤ e k) →
      e 0 ≤ r → eta 0 ≤ H →
      (∀ k, e (k+1) ≤ (A*eta k+B*e k)*e k) →
      (∀ k, e k ≤ 1 → eta (k+1) ≤ C*e k) →
      Tendsto e atTop (𝓝 0) ∧ Tendsto eta atTop (𝓝 0) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, e (k+1) ≤ eps*e k := by
  let R := 1/(4*(A*C+B+1))
  have hACB : 0 ≤ A*C+B := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    dsimp [R]
    apply (div_le_one (show 0 < 4*(A*C+B+1) by positivity)).mpr
    linarith
  have hsmall : (A*C+B)*R ≤ (1/2:ℝ) := by
    dsimp [R]
    rw [mul_one_div]
    apply (div_le_iff₀ (show 0 < 4*(A*C+B+1) by positivity)).mpr
    linarith
  let K := max 1 (A*H+B)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨R/K,div_pos hR hK0,?_⟩
  intro eta e hn he h0 heta0 hrec hforce
  have h0R : e 0 ≤ R := h0.trans (div_le_self hR.le hK)
  have h01 : e 0 ≤ 1 := h0R.trans hR1
  have h1R : e 1 ≤ R := by
    have hc : A*eta 0+B*e 0 ≤ K := by
      have hh := le_max_right (1:ℝ) (A*H+B)
      dsimp [K]
      nlinarith
    have hh := (hrec 0).trans (mul_le_mul_of_nonneg_right hc (he 0))
    have hh0 := (le_div_iff₀ hK0).mp h0
    nlinarith
  have heta1 : eta 1 ≤ C*R := (hforce 0 h01).trans (mul_le_mul_of_nonneg_left h0R hC)
  have hinv : ∀ k, e (k+1) ≤ R ∧ eta (k+1) ≤ C*R := by
    intro k
    induction k with
    | zero => exact ⟨h1R,heta1⟩
    | succ k ih =>
      have hc : A*eta (k+1)+B*e (k+1) ≤ (1/2:ℝ) := by nlinarith [hsmall]
      have hs := (hrec (k+1)).trans (mul_le_mul_of_nonneg_right hc (he (k+1)))
      constructor
      · nlinarith [ih.1,he (k+1)]
      · exact (hforce (k+1) (ih.1.trans hR1)).trans (mul_le_mul_of_nonneg_left ih.1 hC)
  have hstep (k : ℕ) : e ((k+1)+1) ≤ (1/2:ℝ)*e (k+1) := by
    have hc : A*eta (k+1)+B*e (k+1) ≤ (1/2:ℝ) := by
      have hh := hinv k
      nlinarith [hsmall]
    exact (hrec (k+1)).trans (mul_le_mul_of_nonneg_right hc (he (k+1)))
  have helim : Tendsto e atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mp
    (zero_of_step (fun k => e (k+1)) (fun k => he _) (1/2) (by norm_num) (by norm_num) hstep)
  have he1 (k : ℕ) : e k ≤ 1 := by
    cases k with
    | zero => exact h01
    | succ k => exact (hinv k).1.trans hR1
  have hetalim : Tendsto eta atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply squeeze_zero (fun k => hn (k+1)) (fun k => hforce k (he1 k))
    simpa using helim.const_mul C
  exact ⟨helim,hetalim,superlinear A B eta e he hrec hetalim helim⟩
end CScalar
open Filter Topology ProxNewton.Inexact
theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 M : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (hxstar : IsMinimizer g D h xstar) (hM : 0 < M) (hHM : HessianLE g M) :
    (∃ ηbar : ℝ, 0 < ηbar ∧ ηbar < m / 2 ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ (η : ℕ → ℝ) (x Δ : ℕ → EuclideanSpace ℝ (Fin n)),
        (∀ k, 0 ≤ η k ∧ η k ≤ ηbar) → IsInexactProxNewtonRun g D h M η x Δ →
        ‖x 0 - xstar‖ < δ → ∀ k, ‖x (k + 1) - xstar‖ ≤ r * ‖x k - xstar‖) ∧
    (∀ η : ℕ → ℝ, (∀ k, 0 ≤ η k) → Tendsto η atTop (𝓝 0) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x Δ : ℕ → EuclideanSpace ℝ (Fin n),
        IsInexactProxNewtonRun g D h M η x Δ → ‖x 0 - xstar‖ < δ →
        Tendsto x atTop (𝓝 xstar) ∧
          ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ ε * ‖x k - xstar‖) := by
  let A := (1+(M+L1)/m)*(2+L1/M)
  let B := L2/(2*m)
  have hm := hg.m_pos
  have hL1 := hg.L1_nonneg
  have hL2 := hg.L2_nonneg
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  constructor
  · obtain ⟨etaBar,r,hetaBar,hr,hu⟩ := CScalar.uniform_local A B hA hB
    refine ⟨min etaBar (m/4),lt_min hetaBar (by positivity),?_,r,hr,1/2,by norm_num,by norm_num,?_⟩
    · exact (min_le_right _ _).trans_lt (by linarith)
    · intro eta x d heta hrun hx
      have hn := hu eta (fun k => ‖x k-xstar‖) (fun k => norm_nonneg _) hx.le
        (fun k => (heta k).2.trans (min_le_left _ _))
        (fun k => pni_run_bound hg hh hxstar hM (fun k => (heta k).1) hrun k)
      exact hn.2
  · intro eta heta hetalim
    obtain ⟨r,hr,hu⟩ := CScalar.vanishing_local A B hA hB eta hetalim
    refine ⟨r,hr,?_⟩
    intro x d hrun hx
    have hn := hu (fun k => ‖x k-xstar‖) (fun k => norm_nonneg _) hx.le
      (fun k => pni_run_bound hg hh hxstar hM heta hrun k)
    exact ⟨tendsto_iff_norm_sub_tendsto_zero.mpr hn.1,hn.2⟩


