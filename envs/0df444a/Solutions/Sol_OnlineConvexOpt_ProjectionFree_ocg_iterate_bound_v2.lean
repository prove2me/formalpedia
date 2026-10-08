-- Prove2me | solution 1 for OnlineConvexOpt.ProjectionFree.ocg_iterate_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:26:51.684525+00:00
-- url     : https://prove2.me/submissions/0dcc343f-61cc-4a86-8784-616719e9da21

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

lemma ocgi_quad (a B c h' d : ℝ) (ha : 0 < a) (h1 : h' ≤ B + a * d) (hd : 0 ≤ d)
    (hd2 : d ^ 2 ≤ 2 * h') (hE : a ^ 2 ≤ c - B) (hE2 : 2 * a ^ 2 * c ≤ (c - B) ^ 2) :
    h' ≤ c := by
  by_contra hcon
  push_neg at hcon
  have hz : c - B < a * d := by linarith
  have hz2 : (a * d) ^ 2 ≤ 2 * a ^ 2 * (B + a * d) := by
    have : a ^ 2 * d ^ 2 ≤ a ^ 2 * (2 * h') := mul_le_mul_of_nonneg_left hd2 (by positivity)
    nlinarith
  nlinarith [mul_pos (sub_pos.mpr hz) (show 0 < a * d + (c - B) - 2 * a ^ 2 by linarith)]

lemma ocgi_sqrt_le (n : ℕ) (hn : n ≤ 4) : Real.sqrt n ≤ 2 := by
  rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hn)

lemma ocgi_sqrt_ge (n : ℕ) (hn : 4 ≤ n) : 2 ≤ Real.sqrt n := by
  rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hn)

lemma ocgi_num (t T : ℕ) (ht : 1 ≤ t) (htT : t + 1 ≤ T) :
    let σ := min 1 (2 / Real.sqrt t)
    let σ' := min 1 (2 / Real.sqrt ((t + 1 : ℕ) : ℝ))
    let p := (T : ℝ) ^ (3 / 4 : ℝ)
    let Δ := 2 * σ' - 2 * σ + σ ^ 2
    1 ≤ Δ * (4 * p ^ 2) ∧ σ' ≤ Δ ^ 2 * p ^ 2 := by
  intro σ σ' p Δ
  have hT1 : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hp1 : 1 ≤ p := Real.one_le_rpow hT1 (by norm_num)
  have hp4 : p ^ 4 = (T:ℝ) ^ 3 := by
    simp only [p]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rcases Nat.lt_or_ge t 4 with h | h
  · have hs1 : σ = 1 := by
      apply min_eq_left
      have := ocgi_sqrt_le t (by omega)
      have hpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < t by omega))
      rw [le_div_iff₀ hpos]; linarith
    have hs2 : σ' = 1 := by
      apply min_eq_left
      have := ocgi_sqrt_le (t+1) (by omega)
      have hpos : 0 < Real.sqrt ((t+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      rw [le_div_iff₀ hpos]; linarith
    have hΔ : Δ = 1 := by simp only [Δ, hs1, hs2]; norm_num
    rw [hΔ, hs2]
    constructor <;> nlinarith
  · set r := Real.sqrt t with hr
    set s := Real.sqrt ((t + 1 : ℕ) : ℝ) with hs
    have hr2 : 2 ≤ r := ocgi_sqrt_ge t h
    have hs2 : 2 ≤ s := ocgi_sqrt_ge (t+1) (by omega)
    have hrr : r ^ 2 = t := Real.sq_sqrt (by positivity)
    have hss : s ^ 2 = (t:ℝ) + 1 := by rw [hs, Real.sq_sqrt (by positivity)]; push_cast; ring
    have hσ : σ = 2 / r := by
      apply min_eq_right; rw [div_le_one (by linarith)]; linarith
    have hσ' : σ' = 2 / s := by
      apply min_eq_right; rw [div_le_one (by linarith)]; linarith
    have hsr : (s - r) * (s + r) = 1 := by nlinarith
    have hsr0 : r < s := by nlinarith
    have k1 : 2 * r * (s - r) ≤ 1 := by nlinarith
    -- Δ * s^2 ≥ 2
    have hΔs : 2 ≤ Δ * s ^ 2 := by
      simp only [Δ, hσ, hσ']
      have e : (2 * (2 / s) - 2 * (2 / r) + (2 / r) ^ 2) * s ^ 2
          = (4 * r ^ 2 * s - 4 * r * s ^ 2 + 4 * s ^ 2) / r ^ 2 := by
        field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left k1 (show (0:ℝ) ≤ 2 * s by linarith)]
    have hps : s ^ 3 ≤ p ^ 2 := by
      have h6 : (s ^ 3) ^ 2 ≤ (p ^ 2) ^ 2 := by
        have : (s ^ 3) ^ 2 = ((t:ℝ) + 1) ^ 3 := by rw [← hss]; ring
        rw [this, ← pow_mul, show 2 * 2 = 4 by rfl, hp4]
        have : ((t:ℝ) + 1) ≤ T := by exact_mod_cast htT
        exact pow_le_pow_left₀ (by positivity) this 3
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h6
    have hΔpos : 0 < Δ := by
      have : 0 < Δ * s ^ 2 := by linarith
      exact pos_of_mul_pos_left this (by positivity) |> fun h => by
        rcases lt_or_ge 0 Δ with h' | h'
        · exact h'
        · nlinarith [sq_nonneg s]
    constructor
    · nlinarith
    · rw [hσ']
      have h3 : 4 ≤ (Δ * s ^ 2) ^ 2 := by nlinarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hps (show 0 ≤ Δ ^ 2 * s by positivity)]

lemma ocgi_Q {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gradf : ℕ → E) (x1 : E) (η : ℝ) (t : ℕ) (x y : E) :
    AggregateFunction gradf x1 η t y = AggregateFunction gradf x1 η t x +
      ⟪AggregateGradient gradf x1 η t x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
  unfold AggregateFunction AggregateGradient
  have e1 : y - x1 = (y - x) + (x - x1) := by abel
  rw [e1, norm_add_sq_real, inner_add_left, inner_smul_left, inner_smul_left, sum_inner]
  have e2 : ∑ τ ∈ Finset.Ico 1 t, ⟪gradf τ, y⟫_ℝ = ∑ τ ∈ Finset.Ico 1 t, ⟪gradf τ, x⟫_ℝ
      + ∑ τ ∈ Finset.Ico 1 t, ⟪gradf τ, y - x⟫_ℝ := by
    rw [← Finset.sum_add_distrib]; congr 1; funext τ; rw [inner_sub_right]; ring
  rw [e2, real_inner_comm (x - x1) (y - x)]
  simp only [RCLike.conj_to_real]
  ring

lemma ocgi_S {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gradf : ℕ → E) (x1 : E) (η : ℝ) (t : ℕ) (ht : 1 ≤ t) (y : E) :
    AggregateFunction gradf x1 η (t + 1) y = AggregateFunction gradf x1 η t y +
      η * ⟪gradf t, y⟫_ℝ := by
  unfold AggregateFunction
  rw [Finset.sum_Ico_succ_top ht]
  ring

theorem ocgi_core
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ)
    (gradf : ℕ → E) (hgradG : ∀ t : ℕ, 1 ≤ t → ‖gradf t‖ ≤ G)
    (x1 : E)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v)
    (xstar : ℕ → E)
    (hxstar : ∀ t : ℕ, 1 ≤ t → xstar t ∈ K ∧
      ∀ y ∈ K, AggregateFunction gradf x1 η t (xstar t) ≤ AggregateFunction gradf x1 η t y)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    AggregateFunction gradf x1 η t (x t) - AggregateFunction gradf x1 η t (xstar t) ≤
      2 * D ^ 2 * σ t := by
  obtain ⟨hx1e, hx1K, _, hlo, hupd⟩ := hrun
  set F := AggregateFunction gradf x1 η with hF
  have hσ01 : ∀ t : ℕ, 1 ≤ t → 0 ≤ σ t ∧ σ t ≤ 1 := by
    intro t ht
    rw [hσ t ht]
    exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  have hxK : ∀ t : ℕ, 1 ≤ t → x t ∈ K := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [hx1e]; exact hx1K
    | succ n hn ih =>
      rw [hupd n hn]
      obtain ⟨a0, a1⟩ := hσ01 n hn
      exact hKconv ih (hlo n hn).1 (by linarith) a0 (by ring)
  have hp1 : (1:ℝ) ≤ (T : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hT) (by norm_num)
  have hηpos : 0 < η := by rw [hη]; positivity
  -- strong convexity at the minimizer
  have hsc : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ K, ‖y - xstar t‖ ^ 2 ≤ 2 * (F t y - F t (xstar t)) := by
    intro t ht y hy
    obtain ⟨hxsK, hxsmin⟩ := hxstar t ht
    have hm : xstar t + (1/2 : ℝ) • (y - xstar t) ∈ K :=
      hKconv.add_smul_sub_mem hxsK hy ⟨by norm_num, by norm_num⟩
    have h1 := hxsmin _ hm
    have q1 := ocgi_Q gradf x1 η t (xstar t) (xstar t + (1/2 : ℝ) • (y - xstar t))
    have q2 := ocgi_Q gradf x1 η t (xstar t) y
    rw [add_sub_cancel_left, inner_smul_right, norm_smul] at q1
    rw [← hF] at q1 q2
    have : ‖(1/2 : ℝ)‖ = 1/2 := by norm_num
    rw [this] at q1
    nlinarith
  induction t, ht using Nat.le_induction with
  | base =>
    have hF1 : ∀ y, F 1 y = ‖y - x1‖ ^ 2 := by intro y; simp [hF, AggregateFunction]
    rw [hF1, hF1, hx1e, sub_self, norm_zero]
    have := (hσ01 1 le_rfl).1
    nlinarith [norm_nonneg (xstar 1 - x1), sq_nonneg D]
  | succ n hn ih =>
    have ih := ih (by omega)
    obtain ⟨s0, s1⟩ := hσ01 n hn
    have hxn := hxK n hn
    obtain ⟨hvK, hvmin⟩ := hlo n hn
    have hy : x (n+1) = x n + σ n • (v n - x n) := by
      rw [hupd n hn, smul_sub, sub_smul, one_smul]; abel
    -- CG step on F n
    have hstep : F n (x (n+1)) - F n (xstar n) ≤
        (1 - σ n) * (F n (x n) - F n (xstar n)) + σ n ^ 2 * D ^ 2 := by
      have q1 := ocgi_Q gradf x1 η n (x n) (x (n+1))
      rw [hy, add_sub_cancel_left, inner_smul_right, norm_smul,
        Real.norm_of_nonneg s0] at q1
      have q2 := ocgi_Q gradf x1 η n (x n) (xstar n)
      rw [← hF] at q1 q2
      have hvx := hvmin _ (hxstar n hn).1
      have e1 : ⟪AggregateGradient gradf x1 η n (x n), v n - x n⟫_ℝ ≤
          F n (xstar n) - F n (x n) := by
        rw [inner_sub_right]; rw [inner_sub_right] at q2
        nlinarith [norm_nonneg (xstar n - x n)]
      have hdist : ‖v n - x n‖ ≤ D := by rw [← dist_eq_norm]; exact hD _ hvK _ hxn
      have hsq : ‖v n - x n‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (v n - x n)]
      have a1 := mul_le_mul_of_nonneg_left e1 s0
      have a2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (σ n))
      rw [← hy] at q1
      nlinarith
    set d := ‖x (n+1) - xstar (n+1)‖ with hd
    have hxsK' := (hxstar (n+1) (by omega)).1
    have hgr : η * ⟪gradf n, x (n+1) - xstar (n+1)⟫_ℝ ≤ η * G * d := by
      have := real_inner_le_norm (gradf n) (x (n+1) - xstar (n+1))
      have h2 : ‖gradf n‖ * d ≤ G * d :=
        mul_le_mul_of_nonneg_right (hgradG n hn) (norm_nonneg _)
      nlinarith
    have hmin : F n (xstar n) ≤ F n (xstar (n+1)) := (hxstar n hn).2 _ hxsK'
    have hh' : F (n+1) (x (n+1)) - F (n+1) (xstar (n+1)) ≤
        ((1 - σ n) * (2 * D ^ 2 * σ n) + σ n ^ 2 * D ^ 2) + (η * G) * d := by
      rw [hF, ocgi_S gradf x1 η n hn, ocgi_S gradf x1 η n hn, ← hF]
      rw [inner_sub_right] at hgr
      have := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 - σ n by linarith)
      nlinarith
    have hd2 := hsc (n+1) (by omega) _ (hxK (n+1) (by omega))
    rw [← hd] at hd2
    have hnum := ocgi_num n T hn (by omega)
    simp only at hnum
    rw [← hσ n hn, ← hσ (n+1) (by omega)] at hnum
    obtain ⟨c1, c2⟩ := hnum
    set p := (T : ℝ) ^ (3 / 4 : ℝ) with hp
    have hηG : η * G = D / (2 * p) := by rw [hη]; field_simp
    rw [hηG] at hh'
    apply ocgi_quad (D / (2 * p)) _ _ _ d (by positivity) hh' (norm_nonneg _) hd2
    · have e : (2 * D ^ 2 * σ (n+1)) - ((1 - σ n) * (2 * D ^ 2 * σ n) + σ n ^ 2 * D ^ 2)
          = D ^ 2 * (2 * σ (n+1) - 2 * σ n + σ n ^ 2) := by ring
      rw [e, div_pow, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left c1 (sq_nonneg D)
      nlinarith
    · have e : (2 * D ^ 2 * σ (n+1)) - ((1 - σ n) * (2 * D ^ 2 * σ n) + σ n ^ 2 * D ^ 2)
          = D ^ 2 * (2 * σ (n+1) - 2 * σ n + σ n ^ 2) := by ring
      rw [e, div_pow]
      have e2 : 2 * (D ^ 2 / (2 * p) ^ 2) * (2 * D ^ 2 * σ (n + 1)) = D ^ 4 * σ (n+1) / p ^ 2 := by
        field_simp
      rw [e2, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left c2 (show 0 ≤ D ^ 4 by positivity)
      nlinarith

end OnlineConvexOpt.ProjectionFree

open OnlineConvexOpt.ProjectionFree


theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (gradf : ℕ → E) (hgradG : ∀ t : ℕ, 1 ≤ t → ‖gradf t‖ ≤ G)
    (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v)
    (xstar : ℕ → E)
    (hxstar : ∀ t : ℕ, 1 ≤ t → xstar t ∈ K ∧
      ∀ y ∈ K, AggregateFunction gradf x1 η t (xstar t) ≤ AggregateFunction gradf x1 η t y)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    AggregateFunction gradf x1 η t (x t) - AggregateFunction gradf x1 η t (xstar t) ≤
      2 * D ^ 2 * σ t := by
  exact ocgi_core K hKconv D hDpos hD G hGpos f gradf hgradG x1 T hT η hη σ hσ x v hrun xstar hxstar t ht htT
