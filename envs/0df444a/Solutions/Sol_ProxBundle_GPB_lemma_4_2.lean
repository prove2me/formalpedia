-- Prove2me | solution 1 for ProxBundle.GPB.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:52:35.12357+00:00
-- url     : https://prove2.me/submissions/043c77cb-eadd-4b23-8669-c37258cb381f

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_corollary_B_2

open ProxBundle.GPB
open scoped InnerProductSpace RealInnerProductSpace

lemma gpb_l42_sq_comb {n : ℕ} (x u c : E n) (t : ℝ) :
    ‖(1 - t) • x + t • u - c‖ ^ 2 =
      (1 - t) * ‖x - c‖ ^ 2 + t * ‖u - c‖ ^ 2 - t * (1 - t) * ‖u - x‖ ^ 2 := by
  have h1 : (1 - t) • x + t • u - c = (1 - t) • (x - c) + t • (u - c) := by module
  have h2 : u - x = (u - c) - (x - c) := by abel
  rw [h1, h2]
  generalize x - c = p
  generalize u - c = q
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_comm q]
  ring

/-- Quadratic growth of a `(μ + 1/λ)`-strongly convex proximal objective at its minimizer
(Theorem 5.25(b) of Beck, as used in (46) and (52)). -/
lemma gpb_l42_qgrowth {n : ℕ} (D : Set (E n)) (μ lam : ℝ) (G : E n → ℝ) (c x : E n)
    (hG : StrongConvexOn D μ G) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hx : x ∈ D)
    (hmin : ∀ u ∈ D, G x + ‖x - c‖ ^ 2 / (2 * lam) ≤ G u + ‖u - c‖ ^ 2 / (2 * lam))
    (u : E n) (hu : u ∈ D) :
    G x + ‖x - c‖ ^ 2 / (2 * lam) + (μ + 1 / lam) / 2 * ‖u - x‖ ^ 2 ≤
      G u + ‖u - c‖ ^ 2 / (2 * lam) := by
  set K := (μ + 1 / lam) / 2 * ‖u - x‖ ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 - t) * K ≤ (G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam)) := by
    intro t ht0 ht1
    have hw := hG.2 hx hu (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    have hwD : (1 - t) • x + t • u ∈ D := hG.1 hx hu (by linarith) ht0.le (by ring)
    have hm := hmin _ hwD
    rw [gpb_l42_sq_comb] at hm
    simp only [smul_eq_mul] at hw
    rw [norm_sub_rev x u] at hw
    have h : 0 ≤ t * ((G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam))
        - (1 - t) * K) := by
      rw [hKdef]
      have e : t * ((G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam))
          - (1 - t) * ((μ + 1 / lam) / 2 * ‖u - x‖ ^ 2)) =
          (t * G u + (1 - t) * G x - (1 - t) * t * (μ / 2 * ‖u - x‖ ^ 2) -
              G ((1 - t) • x + t • u)) +
          (G ((1 - t) • x + t • u) +
            ((1 - t) * ‖x - c‖ ^ 2 + t * ‖u - c‖ ^ 2 - t * (1 - t) * ‖u - x‖ ^ 2) /
              (2 * lam) - (G x + ‖x - c‖ ^ 2 / (2 * lam))) := by
        field_simp
        ring
      rw [e]
      have := hw
      linarith
    have := (mul_nonneg_iff_of_pos_left ht0).mp h
    linarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hKδ : 0 < K + δ := by linarith
  have ht0 : 0 < δ / (K + δ) := by positivity
  have ht1 : δ / (K + δ) ≤ 1 := by rw [div_le_one hKδ]; linarith
  have h := key _ ht0 ht1
  have h2 : δ / (K + δ) * K ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hKδ]; nlinarith
  have e : (1 - δ / (K + δ)) * K = K - δ / (K + δ) * K := by ring
  linarith


theorem solution {n : ℕ} (P : Instance n) (μ lam ε : ℝ)
    (x0 u : E n) (xh yh : ℕ → E n) (Γh : ℕ → E n → ℝ)
    (hμ : 0 ≤ μ) (hA1 : P.A1 μ) (hlam : 0 < lam) (hε : 0 < ε)
    (hhat : IsHat P μ lam ε x0 xh yh Γh) (hu : u ∈ P.D) :
    (∀ k : ℕ, 1 ≤ k →
      P.φ (yh k) - P.φ u ≤
        ‖xh (k - 1) - u‖ ^ 2 / (2 * lam) -
        ‖xh k - u‖ ^ 2 / (2 * lamMu μ lam) + ε / 2) ∧
    (∀ K : ℕ, 1 ≤ K → serBound μ lam ε (‖x0 - u‖ ^ 2) ≤ (K : ℝ) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ P.φ (yh k) - P.φ u ≤ ε) ∧
    (P.IsOpt u → ∀ k : ℕ, 1 ≤ k →
      ‖xh k - u‖ ^ 2 ≤ ‖x0 - u‖ ^ 2 + lam * (k : ℝ) * ε) := by
  obtain ⟨hx0, hhk⟩ := hhat
  have hlm : 0 < 1 + lam * μ := by positivity
  have hcoef : 1 / (2 * lamMu μ lam) = (1 + lam * μ) / (2 * lam) := by
    unfold lamMu; field_simp
  -- part (a), inequality (45)
  have ha : ∀ k : ℕ, 1 ≤ k →
      P.φ (yh k) - P.φ u ≤
        ‖xh (k - 1) - u‖ ^ 2 / (2 * lam) -
        ‖xh k - u‖ ^ 2 / (2 * lamMu μ lam) + ε / 2 := by
    intro k hk
    obtain ⟨hconv, hle, hprox, -, hgap⟩ := hhk k hk
    have hq := gpb_l42_qgrowth P.D μ lam (Γh k) (xh (k - 1)) (xh k) hconv.1 hlam hμ
      hprox.1 hprox.2 u hu
    have hΓu := hle u hu
    rw [norm_sub_rev u (xh k), norm_sub_rev u (xh (k - 1))] at hq
    have e : ‖xh k - u‖ ^ 2 / (2 * lamMu μ lam) = (μ + 1 / lam) / 2 * ‖xh k - u‖ ^ 2 := by
      rw [div_eq_mul_one_div, hcoef]; field_simp; ring
    rw [e]
    linarith
  -- the recursion (77) data
  set θ : ℝ := 1 + lam * μ with hθ
  have hθ1 : 1 ≤ θ := by rw [hθ]; nlinarith
  have hrec : ∀ k : ℕ, 1 ≤ k →
      P.φ (yh k) - P.φ u ≤ ‖xh (k - 1) - u‖ ^ 2 / (2 * lam) -
        θ * (‖xh k - u‖ ^ 2 / (2 * lam)) + ε / 2 := by
    intro k hk
    have := ha k hk
    have e : ‖xh k - u‖ ^ 2 / (2 * lamMu μ lam) = θ * (‖xh k - u‖ ^ 2 / (2 * lam)) := by
      rw [div_eq_mul_one_div, hcoef, hθ]; ring
    rw [e] at this; exact this
  have hthr : (if θ = 1 then ‖xh 0 - u‖ ^ 2 / (2 * lam) / (ε / 2)
       else min (‖xh 0 - u‖ ^ 2 / (2 * lam) / (ε / 2))
         (θ / (θ - 1) * Real.log (‖xh 0 - u‖ ^ 2 / (2 * lam) * (θ - 1) / (ε / 2) + 1))) =
      serBound μ lam ε (‖x0 - u‖ ^ 2) := by
    rw [hx0]
    unfold serBound
    have e1 : ‖x0 - u‖ ^ 2 / (2 * lam) / (ε / 2) = ‖x0 - u‖ ^ 2 / (lam * ε) := by
      field_simp
    rcases eq_or_lt_of_le hμ with h0 | hpos
    · subst h0
      simp [hθ, e1]
    · have hθne : θ ≠ 1 := by rw [hθ]; intro h; nlinarith [mul_pos hlam hpos]
      rw [if_neg hθne, if_neg hpos.ne', e1]
      congr 2
      · rw [hθ]; unfold lamMu; field_simp; ring
      · congr 1; rw [hθ]; field_simp; ring
  refine ⟨ha, ?_, ?_⟩
  · -- part (b)
    intro K hK hS
    by_contra hcon
    push Not at hcon
    let η : ℕ → ℝ := fun j => if 1 ≤ j ∧ j ≤ K then P.φ (yh j) - P.φ u else 0
    let α : ℕ → ℝ := fun j => if j ≤ K then ‖xh j - u‖ ^ 2 / (2 * lam) else 0
    have hη : ∀ j, 0 ≤ η j := by
      intro j; simp only [η]; split_ifs with h
      · have := hcon j h.1 h.2; linarith
      · exact le_rfl
    have hα : ∀ j, 0 ≤ α j := by
      intro j; simp only [α]; split_ifs <;> positivity
    have hr : ∀ j, 1 ≤ j → η j ≤ α (j - 1) - θ * α j + ε / 2 := by
      intro j hj
      simp only [η, α]
      by_cases hjK : j ≤ K
      · rw [if_pos ⟨hj, hjK⟩, if_pos hjK, if_pos (by omega)]
        exact hrec j hj
      · rw [if_neg (fun h => hjK h.2), if_neg hjK]
        split_ifs <;> nlinarith [div_nonneg (sq_nonneg ‖xh (j - 1) - u‖) (by positivity : (0:ℝ) ≤ 2 * lam)]
    obtain ⟨hB, -⟩ := ProxBundle.GPB.corollary_B_2 θ (ε / 2) η α hθ1 (by positivity) hη hα hr
    have hα0 : α 0 = ‖xh 0 - u‖ ^ 2 / (2 * lam) := by simp [α]
    rw [hα0, hthr] at hB
    obtain ⟨j, hj1, hjK, hjη⟩ := hB K hK hS
    simp only [η, if_pos (And.intro hj1 hjK)] at hjη
    have := hcon j hj1 hjK
    linarith
  · -- part (c)
    intro hopt k hk
    let η : ℕ → ℝ := fun j => if 1 ≤ j then P.φ (yh j) - P.φ u else 0
    let α : ℕ → ℝ := fun j => ‖xh j - u‖ ^ 2 / (2 * lam)
    have hη : ∀ j, 0 ≤ η j := by
      intro j; simp only [η]; split_ifs with h
      · have := hopt.2 (yh j) (hhk j h).2.2.2.1; linarith
      · exact le_rfl
    have hr : ∀ j, 1 ≤ j → η j ≤ α (j - 1) - θ * α j + ε / 2 := by
      intro j hj
      simp only [η, α, if_pos hj]
      exact hrec j hj
    obtain ⟨-, hB⟩ := ProxBundle.GPB.corollary_B_2 θ (ε / 2) η α hθ1 (by positivity) hη
      (fun j => by positivity) hr
    have h := hB k hk
    simp only [α, hx0] at h
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * lam)
    have e1 : 2 * lam * (‖xh k - u‖ ^ 2 / (2 * lam)) = ‖xh k - u‖ ^ 2 := by field_simp
    have e2 : 2 * lam * (‖x0 - u‖ ^ 2 / (2 * lam) + (k:ℝ) * (ε / 2)) =
        ‖x0 - u‖ ^ 2 + lam * (k:ℝ) * ε := by field_simp
    rw [e1, e2] at h2
    exact h2
