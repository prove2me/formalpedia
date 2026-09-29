-- Prove2me | solution 1 for ProxNewton.Inexact.compGradStep_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:31:37.55129+00:00
-- url     : https://prove2.me/submissions/64017d8d-66ca-4001-b92c-126914f80338

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace
open Filter Topology Set Metric

/-- Right-sided difference quotients converge to the directional derivative. -/
theorem aux_cgs_slope {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (x d : EuclideanSpace ℝ (Fin n))
    (hd : DifferentiableAt ℝ g x) :
    Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t) (𝓝[>] 0) (𝓝 ⟪gradient g x, d⟫) := by
  have h1 := (hd.hasFDerivAt.hasLineDerivAt d).tendsto_slope_zero_right
  rw [inner_gradient_left]
  refine h1.congr (fun t => ?_)
  simp [smul_eq_mul, div_eq_inv_mul]

/-- First-order characterization of convexity. -/
theorem aux_cgs_convex_first {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hgconv : ConvexOn ℝ Set.univ g) (x z : EuclideanSpace ℝ (Fin n))
    (hd : DifferentiableAt ℝ g x) :
    g x + ⟪gradient g x, z - x⟫ ≤ g z := by
  have hT := aux_cgs_slope g x (z - x) hd
  have hle : ⟪gradient g x, z - x⟫ ≤ g z - g x := by
    refine le_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hc := hgconv.2 (Set.mem_univ x) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring)
    have heq : (1 - t) • x + t • z = x + t • (z - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hc
    rw [div_le_iff₀ ht0]
    nlinarith
  linarith

/-- Uniqueness of the proximal point. -/
theorem aux_cgs_unique {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hD : Convex ℝ D) (hhc : ConvexOn ℝ D h)
    (v p q : EuclideanSpace ℝ (Fin n)) (hp : IsProxPoint D h v p) (hq : IsProxPoint D h v q) :
    p = q := by
  obtain ⟨hpD, hpmin⟩ := hp
  obtain ⟨hqD, hqmin⟩ := hq
  set m := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q with hm
  have hmD : m ∈ D := hD hpD hqD (by norm_num) (by norm_num) (by norm_num)
  have hhm : h m ≤ (1 / 2 : ℝ) • h p + (1 / 2 : ℝ) • h q :=
    hhc.2 hpD hqD (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hhm
  have h1 := hpmin m hmD
  have h2 := hqmin m hmD
  set a := p - v
  set b := q - v
  have hmv : m - v = (1 / 2 : ℝ) • (a + b) := by
    simp only [hm, a, b]
    module
  have hpq : p - q = a - b := by simp [a, b]
  have hnm : ‖m - v‖ = (1 / 2) * ‖a + b‖ := by
    rw [hmv, norm_smul]; norm_num
  have hpl := parallelogram_law_with_norm ℝ a b
  rw [hnm] at h1 h2
  have key : ‖a - b‖ * ‖a - b‖ ≤ 0 := by nlinarith
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  rw [← hpq, norm_eq_zero, sub_eq_zero] at this
  exact this

/-- Linear lower bound for a proper closed convex function. -/
theorem aux_cgs_lower {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : IsProperClosedConvex D h)
    (y0 : EuclideanSpace ℝ (Fin n)) (hy0 : y0 ∈ D) :
    ∃ c K : ℝ, 0 ≤ K ∧ c + K = h y0 ∧ ∀ y ∈ D, c - K * ‖y - y0‖ ≤ h y := by
  obtain ⟨_, hDc, hhc, hlsc⟩ := hh
  obtain ⟨b, hb, hbmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := closedBall y0 1) ⟨y0, mem_closedBall_self zero_le_one⟩ (isCompact_closedBall y0 1)
    (hlsc.lowerSemicontinuousOn _)
  have hy0b : y0 ∈ closedBall y0 1 := mem_closedBall_self zero_le_one
  have hbD : b ∈ D := by
    by_contra hbD
    have := isMinOn_iff.1 hbmin _ hy0b
    simp [hbD, hy0] at this
  have hc : ∀ y ∈ D, dist y y0 ≤ 1 → h b ≤ h y := by
    intro y hy hyd
    have := isMinOn_iff.1 hbmin _ (mem_closedBall.2 hyd)
    simp only [hbD, hy, if_true] at this
    exact_mod_cast this
  have hK : 0 ≤ h y0 - h b := by
    have := hc y0 hy0 (by simp)
    linarith
  refine ⟨h b, h y0 - h b, hK, by ring, fun y hy => ?_⟩
  by_cases hr : ‖y - y0‖ ≤ 1
  · have := hc y hy (by rwa [dist_eq_norm])
    nlinarith [norm_nonneg (y - y0)]
  · push Not at hr
    set r := ‖y - y0‖ with hrdef
    have hr0 : 0 < r := by linarith
    set s := r⁻¹ with hs
    have hs0 : 0 < s := inv_pos.2 hr0
    have hsr : s * r = 1 := inv_mul_cancel₀ hr0.ne'
    have hs1 : s ≤ 1 := by
      rw [hs]; exact inv_le_one_of_one_le₀ hr.le
    have hy'D : (1 - s) • y0 + s • y ∈ D := hDc hy0 hy (by linarith) hs0.le (by ring)
    have hy'd : dist ((1 - s) • y0 + s • y) y0 = 1 := by
      rw [dist_eq_norm]
      have : (1 - s) • y0 + s • y - y0 = s • (y - y0) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, ← hrdef, hsr]
    have h1 := hc _ hy'D hy'd.le
    have h2 := hhc.2 hy0 hy (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
    simp only [smul_eq_mul] at h2
    have h3 : h b ≤ (1 - s) * h y0 + s * h y := le_trans h1 h2
    have h4 : h b * r ≤ ((1 - s) * h y0 + s * h y) * r := mul_le_mul_of_nonneg_right h3 hr0.le
    have h5 : ((1 - s) * h y0 + s * h y) * r = (r - 1) * h y0 + h y := by
      have : ((1 - s) * h y0 + s * h y) * r = r * h y0 - (s * r) * h y0 + (s * r) * h y := by ring
      rw [this, hsr]; ring
    rw [h5] at h4
    nlinarith

open Classical in
/-- Existence of the proximal point. -/
theorem aux_cgs_exists {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : IsProperClosedConvex D h)
    (v : EuclideanSpace ℝ (Fin n)) : ∃ y, IsProxPoint D h v y := by
  obtain ⟨⟨y0, hy0⟩, hDc, hhc, hlsc⟩ := hh
  obtain ⟨c, K, hK, hcK, hlow⟩ := aux_cgs_lower D h ⟨⟨y0, hy0⟩, hDc, hhc, hlsc⟩ y0 hy0
  set F : EuclideanSpace ℝ (Fin n) → EReal := fun x => if x ∈ D then (h x : EReal) else ⊤
    with hF
  set G : EuclideanSpace ℝ (Fin n) → EReal := fun y => ((‖y - v‖ ^ 2 / 2 : ℝ) : EReal) with hG
  have hGc : Continuous G := continuous_coe_real_ereal.comp (by fun_prop)
  have hΦ : LowerSemicontinuous (fun y => F y + G y) := by
    refine LowerSemicontinuous.add' hlsc hGc.lowerSemicontinuous (fun y => ?_)
    refine EReal.continuousAt_add (Or.inr ?_) (Or.inr ?_)
    · simp [G]
    · simp [G]
  set d := ‖y0 - v‖ with hd
  set R := 2 * (K + d + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  have hy0R : y0 ∈ closedBall y0 R := mem_closedBall_self hR0
  obtain ⟨a, ha, hamin⟩ := (hΦ.lowerSemicontinuousOn _).exists_isMinOn ⟨y0, hy0R⟩
    (isCompact_closedBall y0 R)
  have haD : a ∈ D := by
    by_contra haD
    have := isMinOn_iff.1 hamin _ hy0R
    simp only [F, G, haD, hy0, if_true, if_false] at this
    rw [EReal.top_add_coe, ← EReal.coe_add, top_le_iff] at this
    exact EReal.coe_ne_top _ this
  have hval : ∀ z ∈ D, z ∈ closedBall y0 R →
      h a + ‖a - v‖ ^ 2 / 2 ≤ h z + ‖z - v‖ ^ 2 / 2 := by
    intro z hz hzR
    have := isMinOn_iff.1 hamin _ hzR
    simp only [F, G, haD, hz, if_true] at this
    exact_mod_cast this
  refine ⟨a, haD, fun z hz => ?_⟩
  by_cases hzR : z ∈ closedBall y0 R
  · exact hval z hz hzR
  · have h0 := hval y0 hy0 hy0R
    rw [mem_closedBall, dist_eq_norm, not_le] at hzR
    have hlz := hlow z hz
    set r := ‖z - y0‖ with hr
    have htri : r ≤ ‖z - v‖ + d := by
      rw [hr, hd]
      calc ‖z - y0‖ = ‖(z - v) + -(y0 - v)‖ := by congr 1; abel
        _ ≤ ‖z - v‖ + ‖-(y0 - v)‖ := norm_add_le _ _
        _ = ‖z - v‖ + ‖y0 - v‖ := by rw [norm_neg]
    have hrd : 0 ≤ r - d := by nlinarith
    have hsq : (r - d) ^ 2 ≤ ‖z - v‖ ^ 2 := by
      have : r - d ≤ ‖z - v‖ := by linarith
      nlinarith
    have hdz : ‖y0 - y0‖ = 0 := by simp
    rw [← hd] at h0
    have hd0 : 0 ≤ d := norm_nonneg _
    have hrr : r * 1 ≤ r * (r / 2 - K - d) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith

theorem aux_cgs_prox_iff {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (x G : EuclideanSpace ℝ (Fin n)) :
    IsProxPoint D h (x - G) x ↔ x ∈ D ∧ ∀ z ∈ D, h x ≤ h z + ⟪G, z - x⟫ + ‖z - x‖ ^ 2 / 2 := by
  have key : ∀ z, ‖z - (x - G)‖ ^ 2 = ‖z - x‖ ^ 2 + 2 * ⟪G, z - x⟫ + ‖G‖ ^ 2 := by
    intro z
    have : z - (x - G) = (z - x) + G := by abel
    rw [this, norm_add_sq_real, real_inner_comm]
  have hx : ‖x - (x - G)‖ = ‖G‖ := by congr 1; abel
  constructor
  · rintro ⟨hxD, hmin⟩
    refine ⟨hxD, fun z hz => ?_⟩
    have := hmin z hz
    rw [hx, key] at this
    linarith
  · rintro ⟨hxD, hmin⟩
    refine ⟨hxD, fun z hz => ?_⟩
    have := hmin z hz
    rw [hx, key]
    linarith

end ProxNewton.Inexact

open ProxNewton.Inexact
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgconv : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hh : IsProperClosedConvex D h) (x : EuclideanSpace ℝ (Fin n)) :
    compGradStep g D h 1 x = 0 ↔ IsMinimizer g D h x := by
  have hdiff : DifferentiableAt ℝ g x := (hg.differentiable one_ne_zero) x
  have hstep : compGradStep g D h 1 x = x - prox D h (x - gradient g x) := by
    unfold compGradStep
    simp only [inv_one, one_smul, one_mul]
  rw [hstep, sub_eq_zero]
  obtain ⟨hDne, hDc, hhc, hlsc⟩ := hh
  set G := gradient g x with hGdef
  constructor
  · intro hfix
    have hspec : IsProxPoint D h (x - G) (prox D h (x - G)) :=
      Classical.epsilon_spec (aux_cgs_exists D h ⟨hDne, hDc, hhc, hlsc⟩ (x - G))
    rw [← hfix] at hspec
    obtain ⟨hxD, hmin⟩ := (aux_cgs_prox_iff D h x G).1 hspec
    refine ⟨hxD, fun z hz => ?_⟩
    have hA := aux_cgs_convex_first g hgconv x z hdiff
    have hB : h x ≤ h z + ⟪G, z - x⟫ := by
      have hT : Filter.Tendsto (fun t : ℝ => h z + ⟪G, z - x⟫ + t * (‖z - x‖ ^ 2 / 2))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (h z + ⟪G, z - x⟫)) := by
        have : Filter.Tendsto (fun t : ℝ => h z + ⟪G, z - x⟫ + t * (‖z - x‖ ^ 2 / 2))
            (nhds 0) (nhds (h z + ⟪G, z - x⟫ + 0 * (‖z - x‖ ^ 2 / 2))) := by
          exact (tendsto_const_nhds.add (Filter.tendsto_id.mul tendsto_const_nhds))
        simpa using this.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hT ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      have hzt : x + t • (z - x) ∈ D := by
        have : x + t • (z - x) = (1 - t) • x + t • z := by
          rw [smul_sub, sub_smul, one_smul]; abel
        rw [this]
        exact hDc hxD hz (by linarith) ht0.le (by ring)
      have h1 := hmin _ hzt
      have heq : x + t • (z - x) - x = t • (z - x) := by abel
      rw [heq, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h1
      have h2 := hhc.2 hxD hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      have heq2 : (1 - t) • x + t • z = x + t • (z - x) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [heq2, smul_eq_mul, smul_eq_mul] at h2
      have h3 : t * h x ≤ t * (h z + ⟪G, z - x⟫ + t * (‖z - x‖ ^ 2 / 2)) := by nlinarith
      exact le_of_mul_le_mul_left h3 ht0
    linarith
  · rintro ⟨hxD, hmin⟩
    have hprox : IsProxPoint D h (x - G) x := by
      refine (aux_cgs_prox_iff D h x G).2 ⟨hxD, fun z hz => ?_⟩
      have hB : h x - h z ≤ ⟪G, z - x⟫ := by
        have hT := aux_cgs_slope g x (z - x) hdiff
        refine ge_of_tendsto hT ?_
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
        obtain ⟨ht0, ht1⟩ := ht
        have heq2 : (1 - t) • x + t • z = x + t • (z - x) := by
          rw [smul_sub, sub_smul, one_smul]; abel
        have hzt : x + t • (z - x) ∈ D := by
          rw [← heq2]
          exact hDc hxD hz (by linarith) ht0.le (by ring)
        have h1 := hmin _ hzt
        have h2 := hhc.2 hxD hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
        rw [heq2, smul_eq_mul, smul_eq_mul] at h2
        rw [le_div_iff₀ ht0]
        nlinarith
      nlinarith [sq_nonneg ‖z - x‖]
    have hspec : IsProxPoint D h (x - G) (prox D h (x - G)) :=
      Classical.epsilon_spec ⟨x, hprox⟩
    exact aux_cgs_unique D h hDc hhc (x - G) _ _ hprox hspec
