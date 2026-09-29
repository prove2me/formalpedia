-- Prove2me | solution 1 for ProxNewton.Inexact.compGradStep_model_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:55:14.436914+00:00
-- url     : https://prove2.me/submissions/dacdcd6c-5f33-4854-a8fc-4b576f4a213e

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

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

open Classical in
theorem aux_cgm_lower {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : IsProperClosedConvex D h)
    (y0 : EuclideanSpace ℝ (Fin n)) (hy0 : y0 ∈ D) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ D, h y0 - 1 - c * ‖y - y0‖ ≤ h y := by
  obtain ⟨-, hDc, hhc, hlsc⟩ := hh
  have hF : ((h y0 - 1 : ℝ) : EReal) <
      (fun x => if x ∈ D then (h x : EReal) else ⊤) y0 := by
    simp only [hy0, if_true]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hev := hlsc y0 _ hF
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hnear : ∀ y ∈ D, dist y y0 < ε → h y0 - 1 < h y := by
    intro y hy hdist
    have := hball hdist
    simp only [hy, if_true] at this
    exact EReal.coe_lt_coe_iff.mp this
  refine ⟨2 / ε, by positivity, ?_⟩
  intro y hy
  by_cases hyc : ‖y - y0‖ < ε
  · have h1 := hnear y hy (by rwa [dist_eq_norm])
    have h2 : 0 ≤ 2 / ε * ‖y - y0‖ := by positivity
    linarith
  · push Not at hyc
    set d := ‖y - y0‖ with hd
    have hdpos : 0 < d := lt_of_lt_of_le hε hyc
    set t := ε / (2 * d) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
    have hzD : (1 - t) • y0 + t • y ∈ D := hDc hy0 hy (by linarith) ht0.le (by ring)
    have hzdist : dist ((1 - t) • y0 + t • y) y0 < ε := by
      rw [dist_eq_norm]
      have : (1 - t) • y0 + t • y - y0 = t • (y - y0) := by module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← hd, ht]
      field_simp
      linarith
    have hz := hnear _ hzD hzdist
    have hconv := hhc.2 hy0 hy (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at hconv
    have htd : t * (2 / ε * d) = 1 := by rw [ht]; field_simp
    have hkey : 0 < t * (h y - h y0 + 2 / ε * d) := by nlinarith
    have := pos_of_mul_pos_right hkey ht0.le
    linarith

open Classical in
theorem aux_cgm_prox_exists {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : IsProperClosedConvex D h)
    (v : EuclideanSpace ℝ (Fin n)) : ∃ y, IsProxPoint D h v y := by
  obtain ⟨y0, hy0⟩ := hh.1
  obtain ⟨c, hc, hlow⟩ := aux_cgm_lower D h hh y0 hy0
  set F : EuclideanSpace ℝ (Fin n) → EReal :=
    fun x => if x ∈ D then (h x : EReal) else ⊤ with hFdef
  set G : EuclideanSpace ℝ (Fin n) → EReal :=
    fun x => F x + ((‖x - v‖ ^ 2 / 2 : ℝ) : EReal) with hGdef
  have hGlsc : LowerSemicontinuous G := by
    apply LowerSemicontinuous.add' hh.2.2.2
    · exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
    · intro x
      exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  set P := h y0 + ‖y0 - v‖ ^ 2 / 2 with hP
  set a := h y0 - 1 with ha
  set b := ‖y0 - v‖ with hb
  have hb0 : 0 ≤ b := norm_nonneg _
  set M := |a - P| + c * b + 1 with hM
  have hM0 : 1 ≤ M := by
    have := abs_nonneg (a - P)
    have := mul_nonneg hc hb0
    linarith
  set R := b + 2 * c + 2 * M + 2 with hR
  have hRpos : 0 ≤ R := by linarith
  have hfar : ∀ z ∈ D, R < ‖z - y0‖ → P < h z + ‖z - v‖ ^ 2 / 2 := by
    intro z hz hzR
    set d := ‖z - y0‖ with hd
    have h1 := hlow z hz
    have htri : d ≤ ‖z - v‖ + b := by
      calc d = ‖(z - v) + (v - y0)‖ := by rw [hd]; congr 1; abel
        _ ≤ ‖z - v‖ + ‖v - y0‖ := norm_add_le _ _
        _ = ‖z - v‖ + b := by rw [norm_sub_rev v y0]
    have hs2 : 2 * c + 2 * M + 2 < d - b := by linarith
    have hs : 0 < d - b := by linarith
    have hsq : (d - b) ^ 2 ≤ ‖z - v‖ ^ 2 := by
      apply pow_le_pow_left₀ hs.le; linarith
    have habs : P - a ≤ |a - P| := by rw [abs_sub_comm]; exact le_abs_self _
    have hprod : (d - b) * ((d - b) / 2 - c) ≥ 2 * (M + 1) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - b - 2) (by linarith : (0:ℝ) ≤ (d - b) / 2 - c)]
    nlinarith
  obtain ⟨ys, hysK, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Metric.closedBall y0 R) ⟨y0, Metric.mem_closedBall_self hRpos⟩
    (isCompact_closedBall y0 R) (hGlsc.lowerSemicontinuousOn _)
  rw [isMinOn_iff] at hmin
  have hGy0 : G y0 = ((P : ℝ) : EReal) := by
    simp only [hGdef, hFdef, hy0, if_true, hP, hb, EReal.coe_add]
  have hle0 : G ys ≤ G y0 := hmin y0 (Metric.mem_closedBall_self hRpos)
  have hysD : ys ∈ D := by
    by_contra hn
    have : G ys = ⊤ := by simp [hGdef, hFdef, hn]
    rw [this, hGy0] at hle0
    exact EReal.coe_ne_top _ (top_le_iff.mp hle0)
  have hGys : G ys = ((h ys + ‖ys - v‖ ^ 2 / 2 : ℝ) : EReal) := by
    simp only [hGdef, hFdef, hysD, if_true, EReal.coe_add]
  refine ⟨ys, hysD, ?_⟩
  intro z hz
  by_cases hzK : z ∈ Metric.closedBall y0 R
  · have h1 := hmin z hzK
    have hGz : G z = ((h z + ‖z - v‖ ^ 2 / 2 : ℝ) : EReal) := by
      simp only [hGdef, hFdef, hz, if_true, EReal.coe_add]
    rw [hGys, hGz] at h1
    exact EReal.coe_le_coe_iff.mp h1
  · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hzK
    have h1 := hfar z hz hzK
    rw [hGys, hGy0] at hle0
    have h2 := EReal.coe_le_coe_iff.mp hle0
    linarith

end ProxNewton.Inexact

open ProxNewton.Inexact

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 : ℝ)
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (xk x : EuclideanSpace ℝ (Fin n)) :
    ‖compGradStep g D h 1 x - compGradStep (quadModel g xk) D h 1 x‖ ≤
      L2 / 2 * ‖x - xk‖ ^ 2 := by
  have hh1 : (fun y => (1 : ℝ) * h y) = h := by funext y; ring
  have hspec : ∀ v, IsProxPoint D h v (prox D h v) := fun v =>
    Classical.epsilon_spec (aux_cgm_prox_exists D h hh v)
  unfold compGradStep
  simp only [hh1, inv_one, one_smul]
  rw [sub_sub_sub_cancel_left]
  calc ‖prox D h (x - gradient (quadModel g xk) x) - prox D h (x - gradient g x)‖
      ≤ ‖(x - gradient (quadModel g xk) x) - (x - gradient g x)‖ :=
        aux_cgm_nonexp D h hh.2.1 hh.2.2.1 _ _ _ _ (hspec _) (hspec _)
    _ = ‖gradient g x - gradient g xk - hessian g xk (x - xk)‖ := by
        rw [aux_cgm_quad_grad g hg.contDiff xk x, sub_sub_sub_cancel_left]
        congr 1
        abel
    _ ≤ L2 / 2 * ‖x - xk‖ ^ 2 := aux_cgm_taylor g L2 hg.contDiff hg.hessian_lipschitz xk x
