-- Prove2me | solution 1 for ProxAlg.FixedPoint.minimizer_iff_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:27:10.601105+00:00
-- url     : https://prove2.me/submissions/b96b4638-06ec-44f7-9dfb-f493fa708b9a

import Mathlib
import Definitions.Def_ProxAlg_FixedPoint_Basic

set_option autoImplicit false

open scoped InnerProductSpace Topology
open Filter
open MoreauProx.Decomposition ProxAlg.FixedPoint

lemma pa_cases (e : EReal) (h : e ≠ ⊥) : e = ⊤ ∨ ∃ a : ℝ, e = (a : EReal) := by
  induction e using EReal.rec with
  | bot => exact absurd rfl h
  | top => exact Or.inl rfl
  | coe a => exact Or.inr ⟨a, rfl⟩

lemma pa_aux (c K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ c + t * K) : 0 ≤ c := by
  by_contra hc
  push_neg at hc
  have hK1 : 0 < 2 * (K + 1) := by linarith
  set t : ℝ := min 1 (-c / (2 * (K + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hK1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (2 * (K + 1)) ≤ -c := by
    calc t * (2 * (K + 1)) ≤ (-c / (2 * (K + 1))) * (2 * (K + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hK1.le
      _ = -c := by field_simp
  have := h t ht0 ht1
  nlinarith

lemma pa_convex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : GammaZero f)
    (x z : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (hx : f x = a) (hz : f z = b) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • z) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have := hf.convex_epigraph (x := (x, a)) (y := (z, b)) (show f x ≤ (a : EReal) by rw [hx])
    (show f z ≤ (b : EReal) by rw [hz]) (sub_nonneg.2 ht1) ht0 (by ring)
  exact this

lemma pa_dir {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfd : Differentiable ℝ f)
    (x d : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) ⟪gradient f x, d⟫_ℝ 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • d) := by
    simpa using (hfd x).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have e : ⟪gradient f x, d⟫_ℝ = fderiv ℝ f x d := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [e]; exact h3

lemma pa_gradineq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (x y : EuclideanSpace ℝ (Fin n)) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
    have hβ' : β = 1 - α := by linarith
    have := hf.2 (Set.mem_univ (x + a • (y - x))) (Set.mem_univ (x + b • (y - x))) hα hβ hαβ
    have e : x + (α • a + β • b) • (y - x) = α • (x + a • (y - x)) + β • (x + b • (y - x)) := by
      subst hβ'; simp only [smul_eq_mul]; module
    simp only [hφ]
    rw [e]
    exact this
  have hder : HasDerivAt φ ⟪gradient f x, y - x⟫_ℝ 0 := pa_dir f hfd x (y - x)
  have h1 := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hder
  have e1 : φ 1 = f y := by simp [hφ]
  have e0 : φ 0 = f x := by simp [hφ]
  rw [slope_def_field, e1, e0] at h1
  have h10 : (1 : ℝ) - 0 = 1 := by norm_num
  rw [h10, div_one] at h1
  linarith

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : MoreauProx.Decomposition.GammaZero g)
    (xs : EuclideanSpace ℝ (Fin n)) :
    (∀ y, ((f xs : ℝ) : EReal) + g xs ≤ ((f y : ℝ) : EReal) + g y) ↔
      ∃ v ∈ subdifferential g xs, gradient f xs + v = 0 := by
  constructor
  · intro hmin
    obtain ⟨x0, hx0⟩ := hg.exists_ne_top
    have hxtop : g xs ≠ ⊤ := by
      intro h
      have h1 := hmin x0
      rw [h, EReal.coe_add_top] at h1
      rcases pa_cases (g x0) (hg.ne_bot x0) with h2 | ⟨c, h2⟩
      · exact hx0 h2
      · rw [h2, ← EReal.coe_add] at h1
        exact EReal.coe_ne_top _ (top_le_iff.1 h1)
    rcases pa_cases (g xs) (hg.ne_bot xs) with h | ⟨a, ha⟩
    · exact absurd h hxtop
    refine ⟨-gradient f xs, ⟨lt_top_iff_ne_top.2 hxtop, fun z => ?_⟩, add_neg_cancel _⟩
    rcases pa_cases (g z) (hg.ne_bot z) with hz | ⟨b, hb⟩
    · rw [hz]; exact le_top
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_neg_left]
    have hder := pa_dir f hfd xs (z - xs)
    have hlim := hder.tendsto_slope_zero_right
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤
        t⁻¹ • ((fun t : ℝ => f (xs + t • (z - xs))) (0 + t) -
          (fun t : ℝ => f (xs + t • (z - xs))) 0) + (b - a) := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      have hconv := pa_convex g hg xs z a b ha hb t ht.1.le ht.2.le
      have h1 := hmin ((1 - t) • xs + t • z)
      have h2 := h1.trans (add_le_add le_rfl hconv)
      rw [ha, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
      have hu : (1 - t) • xs + t • z = xs + t • (z - xs) := by module
      rw [hu] at h2
      have h0 : xs + (0 : ℝ) • (z - xs) = xs := by simp
      simp only [zero_add, smul_eq_mul, h0]
      have h3 : t⁻¹ * (f (xs + t • (z - xs)) - f xs) + (b - a) =
          t⁻¹ * (f (xs + t • (z - xs)) - f xs + t * (b - a)) := by
        have ht0 : t ≠ 0 := ht.1.ne'
        field_simp
      rw [h3]
      exact mul_nonneg (inv_nonneg.2 ht.1.le) (by nlinarith [h2])
    have := ge_of_tendsto (hlim.add_const (b - a)) hev
    linarith
  · rintro ⟨v, ⟨hxtop, hsub⟩, hv⟩ y
    have hv' : v = -gradient f xs := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hv
    rcases pa_cases (g xs) (hg.ne_bot xs) with h | ⟨a, ha⟩
    · rw [h] at hxtop; exact absurd hxtop (lt_irrefl _)
    rcases pa_cases (g y) (hg.ne_bot y) with hy | ⟨b, hb⟩
    · rw [hy, EReal.coe_add_top]; exact le_top
    have h := hsub y
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff, hv', inner_neg_left] at h
    rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have := pa_gradineq f hf hfd xs y
    linarith
