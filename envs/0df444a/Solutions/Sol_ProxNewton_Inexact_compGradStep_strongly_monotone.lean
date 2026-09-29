-- Prove2me | solution 1 for ProxNewton.Inexact.compGradStep_strongly_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:51:26.508666+00:00
-- url     : https://prove2.me/submissions/fde98a99-2b89-46ff-b8db-bef83ed8abda

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

/-- Descent lemma for a function with Lipschitz gradient. -/
theorem aux_pncgs_descent {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hd : Differentiable ℝ g)
    (hL : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (y z : EuclideanSpace ℝ (Fin n)) :
    g z ≤ g y + ⟪gradient g y, z - y⟫ + L / 2 * ‖z - y‖ ^ 2 := by
  have hf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (y + s • (z - y)))
      ⟪gradient g (y + s • (z - y)), z - y⟫ s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • (z - y)) (z - y) s := by
      simpa using ((hasDerivAt_id s).smul_const (z - y)).const_add y
    have h2 := (hd (y + s • (z - y))).hasFDerivAt.comp_hasDerivAt s h1
    rw [inner_gradient_left]
    exact h2
  have hB : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => g y + s * ⟪gradient g y, z - y⟫ + L / 2 * s ^ 2 * ‖z - y‖ ^ 2)
      (⟪gradient g y, z - y⟫ + L * s * ‖z - y‖ ^ 2) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s * ⟪gradient g y, z - y⟫) ⟪gradient g y, z - y⟫ s := by
      simpa using (hasDerivAt_id s).mul_const ⟪gradient g y, z - y⟫
    have h2 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖z - y‖ ^ 2) (L * s * ‖z - y‖ ^ 2) s :=
      (((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖z - y‖ ^ 2)).congr_deriv
        (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    exact (h1.const_add (g y)).add h2
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun s : ℝ => g (y + s • (z - y)))
    (f' := fun s => ⟪gradient g (y + s • (z - y)), z - y⟫)
    (fun s _ => (hf s).continuousAt.continuousWithinAt)
    (fun s _ => (hf s).hasDerivWithinAt)
    (B := fun s : ℝ => g y + s * ⟪gradient g y, z - y⟫ + L / 2 * s ^ 2 * ‖z - y‖ ^ 2)
    (B' := fun s => ⟪gradient g y, z - y⟫ + L * s * ‖z - y‖ ^ 2)
    (by simp)
    (fun s _ => (hB s).continuousAt.continuousWithinAt)
    (fun s _ => (hB s).hasDerivWithinAt)
    (by
      intro s hs
      have h1 : ⟪gradient g (y + s • (z - y)) - gradient g y, z - y⟫ ≤
          ‖gradient g (y + s • (z - y)) - gradient g y‖ * ‖z - y‖ := real_inner_le_norm _ _
      have h2 : ‖gradient g (y + s • (z - y)) - gradient g y‖ ≤ L * (s * ‖z - y‖) := by
        have := hL (y + s • (z - y)) y
        simpa [norm_smul, abs_of_nonneg hs.1] using this
      rw [inner_sub_left] at h1
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (z - y))
      nlinarith)
    (x := 1) (by simp)
  simpa using key

/-- Co-coercivity of the gradient (Baillon–Haddad type inequality) with step `t`, `t L ≤ 1`. -/
theorem aux_pncgs_cocoercive {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L t : ℝ)
    (hd : Differentiable ℝ g)
    (hL : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ x w, g x + ⟪gradient g x, w - x⟫ ≤ g w)
    (ht : 0 < t) (htL : t * L ≤ 1) (x y : EuclideanSpace ℝ (Fin n)) :
    t * ‖gradient g x - gradient g y‖ ^ 2 ≤ ⟪x - y, gradient g x - gradient g y⟫ := by
  have one : ∀ x y : EuclideanSpace ℝ (Fin n),
      g x + ⟪gradient g x, y - x⟫ + t / 2 * ‖gradient g y - gradient g x‖ ^ 2 ≤ g y := by
    intro x y
    have h1 := hconv x (y - t • (gradient g y - gradient g x))
    have h2 := aux_pncgs_descent g L hd hL y (y - t • (gradient g y - gradient g x))
    have hzy : y - t • (gradient g y - gradient g x) - y = -(t • (gradient g y - gradient g x)) := by
      abel
    have hzx : y - t • (gradient g y - gradient g x) - x
        = (y - x) - t • (gradient g y - gradient g x) := by abel
    rw [hzx, inner_sub_right, real_inner_smul_right] at h1
    rw [hzy, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht] at h2
    have h3 : ⟪gradient g y, gradient g y - gradient g x⟫ - ⟪gradient g x, gradient g y - gradient g x⟫
        = ‖gradient g y - gradient g x‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have h4 : L * t ^ 2 * ‖gradient g y - gradient g x‖ ^ 2 ≤ t * ‖gradient g y - gradient g x‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right htL
        (by positivity : 0 ≤ t * ‖gradient g y - gradient g x‖ ^ 2)
      nlinarith
    nlinarith
  have a := one x y
  have b := one y x
  have e1 : ⟪x - y, gradient g x - gradient g y⟫
      = -(⟪gradient g x, y - x⟫ + ⟪gradient g y, x - y⟫) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  rw [norm_sub_rev (gradient g y) (gradient g x)] at a
  linarith

/-- One-sided variational inequality for a prox point. -/
theorem aux_pncgs_var {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (k : EuclideanSpace ℝ (Fin n) → ℝ) (hk : ConvexOn ℝ D k)
    (u p q : EuclideanSpace ℝ (Fin n)) (hp : IsProxPoint D k u p) (hq : q ∈ D)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    0 ≤ k q - k p + ⟪p - u, q - p⟫ + l / 2 * ‖q - p‖ ^ 2 := by
  have hz : p + l • (q - p) = (1 - l) • p + l • q := by module
  have hzD : p + l • (q - p) ∈ D := by
    rw [hz]; exact hk.1 hp.1 hq (by linarith) hl0.le (by ring)
  have hkz : k (p + l • (q - p)) ≤ (1 - l) * k p + l * k q := by
    rw [hz]
    have := hk.2 hp.1 hq (by linarith : (0:ℝ) ≤ 1 - l) hl0.le (by ring)
    simpa [smul_eq_mul] using this
  have hnorm : ‖p + l • (q - p) - u‖ ^ 2
      = ‖p - u‖ ^ 2 + 2 * l * ⟪p - u, q - p⟫ + l ^ 2 * ‖q - p‖ ^ 2 := by
    have : p + l • (q - p) - u = (p - u) + l • (q - p) := by abel
    rw [this, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hopt := hp.2 _ hzD
  rw [hnorm] at hopt
  have : 0 ≤ l * (k q - k p + ⟪p - u, q - p⟫ + l / 2 * ‖q - p‖ ^ 2) := by
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hl0).1 this

/-- Firm nonexpansiveness of prox points. -/
theorem aux_pncgs_firm {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (k : EuclideanSpace ℝ (Fin n) → ℝ) (hk : ConvexOn ℝ D k)
    (u v p q : EuclideanSpace ℝ (Fin n)) (hp : IsProxPoint D k u p) (hq : IsProxPoint D k v q) :
    ‖p - q‖ ^ 2 ≤ ⟪u - v, p - q⟫ := by
  have key : ∀ l : ℝ, 0 < l → l ≤ 1 → ‖p - q‖ ^ 2 - ⟪u - v, p - q⟫ ≤ l * ‖p - q‖ ^ 2 := by
    intro l hl0 hl1
    have a := aux_pncgs_var D k hk u p q hp hq.1 l hl0 hl1
    have b := aux_pncgs_var D k hk v q p hq hp.1 l hl0 hl1
    have e : ⟪p - u, q - p⟫ + ⟪q - v, p - q⟫ = ⟪u - v, p - q⟫ - ‖p - q‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    rw [norm_sub_rev q p] at a
    linarith
  by_contra hcon
  push Not at hcon
  have hX : 0 < ‖p - q‖ ^ 2 - ⟪u - v, p - q⟫ := by linarith
  have hN : ‖p - q‖ ^ 2 - ⟪u - v, p - q⟫ ≤ ‖p - q‖ ^ 2 := by simpa using key 1 one_pos le_rfl
  have hNpos : 0 < ‖p - q‖ ^ 2 := lt_of_lt_of_le hX hN
  have h := key ((‖p - q‖ ^ 2 - ⟪u - v, p - q⟫) / (2 * ‖p - q‖ ^ 2)) (by positivity)
    (by rw [div_le_one (by positivity)]; linarith)
  have e2 : (‖p - q‖ ^ 2 - ⟪u - v, p - q⟫) / (2 * ‖p - q‖ ^ 2) * ‖p - q‖ ^ 2
      = (‖p - q‖ ^ 2 - ⟪u - v, p - q⟫) / 2 := by
    have hne : ‖p - q‖ ≠ 0 := fun h0 => by rw [h0] at hNpos; simp at hNpos
    field_simp
  linarith

/-- Existence of prox points for a proper closed convex function. -/
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

end ProxNewton.Inexact

open ProxNewton.Inexact
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 t : ℝ)
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (ht : 0 < t) (htL1 : t * L1 ≤ 1) (x y : EuclideanSpace ℝ (Fin n)) :
    m / 2 * ‖x - y‖ ^ 2 ≤ ⟪x - y, compGradStep g D h t x - compGradStep g D h t y⟫ := by
  have hd : Differentiable ℝ g := hg.contDiff.differentiable (by norm_num)
  have hconvg : ∀ x w, g x + ⟪gradient g x, w - x⟫ ≤ g w := fun x w => by
    have h1 := hg.strongConvex x w
    have h2 : 0 ≤ m / 2 * ‖x - w‖ ^ 2 := by have := hg.m_pos; positivity
    linarith
  have hk : ConvexOn ℝ D (fun y => t * h y) := by
    have := hh.2.2.1.smul ht.le
    simpa [smul_eq_mul] using this
  have hP : IsProxPoint D (fun y => t * h y) (x - t • gradient g x)
      (prox D (fun y => t * h y) (x - t • gradient g x)) :=
    Classical.epsilon_spec (aux_pncgs_exists D h hh t ht _)
  have hQ : IsProxPoint D (fun y => t * h y) (y - t • gradient g y)
      (prox D (fun y => t * h y) (y - t • gradient g y)) :=
    Classical.epsilon_spec (aux_pncgs_exists D h hh t ht _)
  have hfirm := aux_pncgs_firm D _ hk _ _ _ _ hP hQ
  have hco := aux_pncgs_cocoercive g L1 t hd hg.grad_lipschitz hconvg ht htL1 x y
  have hsm : m * ‖x - y‖ ^ 2 ≤ ⟪x - y, gradient g x - gradient g y⟫ := by
    have a := hg.strongConvex x y
    have b := hg.strongConvex y x
    have e1 : ⟪x - y, gradient g x - gradient g y⟫
        = -(⟪gradient g x, y - x⟫ + ⟪gradient g y, x - y⟫) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    rw [norm_sub_rev y x] at b
    linarith
  have hG : compGradStep g D h t x - compGradStep g D h t y
      = t⁻¹ • ((x - y) - (prox D (fun y => t * h y) (x - t • gradient g x)
          - prox D (fun y => t * h y) (y - t • gradient g y))) := by
    simp only [compGradStep]
    rw [← smul_sub]
    congr 1
    abel
  have huw : (x - t • gradient g x) - (y - t • gradient g y)
      = (x - y) - t • (gradient g x - gradient g y) := by
    rw [smul_sub]; abel
  rw [huw] at hfirm
  rw [hG, real_inner_smul_right]
  set d := x - y
  set γ := gradient g x - gradient g y
  set δ := prox D (fun y => t * h y) (x - t • gradient g x)
      - prox D (fun y => t * h y) (y - t • gradient g y)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, le_inv_mul_iff₀ ht]
  have f1 : 0 ≤ ‖d - δ‖ ^ 2 := by positivity
  rw [norm_sub_sq_real] at f1
  have f2 : 0 ≤ ‖(d - t • γ) - δ‖ ^ 2 := by positivity
  rw [norm_sub_sq_real] at f2
  have f3 : ‖d - t • γ‖ ^ 2 = ‖d‖ ^ 2 - 2 * (t * ⟪d, γ⟫) + t ^ 2 * ‖γ‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have f4 := mul_le_mul_of_nonneg_left hco ht.le
  have f5 := mul_le_mul_of_nonneg_left hsm ht.le
  nlinarith
