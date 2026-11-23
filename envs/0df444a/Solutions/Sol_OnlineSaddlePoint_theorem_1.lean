-- Prove2me | solution 1 for OnlineSaddlePoint.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T00:14:22.890026+00:00
-- url     : https://prove2.me/submissions/a5195908-4fa3-4f9b-a249-4ae19808dca2

import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun
import Definitions.Def_OnlineSaddlePoint_IsStronglyConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_spRegret
import Theorems.Thm_OnlineLearningOCO_FoReL_lemma_2_8

/-! ===== SP_Minimax ===== -/

/-! # Piece A: a strongly convex–concave Lipschitz game on compact sets has a saddle point. -/

namespace SPMinimax
open OnlineSaddlePoint

/-- Final real-number step: a quantity bounded by `c * t` for all small `t > 0` is `≤ 0`. -/
lemma nonpos_of_le_mul_small (δ c : ℝ) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → δ ≤ c * t) : δ ≤ 0 := by
  by_contra hδ
  rw [not_le] at hδ
  set t := min (1 / 2 : ℝ) (δ / (2 * c + 1)) with ht
  have hpos : 0 < δ / (2 * c + 1) := div_pos hδ (by linarith)
  have ht0 : 0 < t := lt_min (by norm_num) hpos
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t ≤ δ / (2 * c + 1) := min_le_right _ _
  have := h t ht0 ht1
  have h3 : c * t ≤ c * (δ / (2 * c + 1)) := mul_le_mul_of_nonneg_left ht2 hc
  have h4 : c * (δ / (2 * c + 1)) < δ := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The key quadratic estimate: from `(1-t) H/4 d² ≤ t G d` with `t ≤ 1/2`, get `H d ≤ 8 t G`. -/
lemma d_bound (H G t d : ℝ) (hH : 0 < H) (hG : 0 ≤ G) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hd : 0 ≤ d) (h : (1 - t) * (H / 4 * d ^ 2) ≤ t * (G * d)) : H * d ≤ 8 * t * G := by
  rcases hd.eq_or_lt with hd0 | hd0
  · subst hd0; nlinarith
  · have h1 : H / 8 * d ^ 2 ≤ (1 - t) * (H / 4 * d ^ 2) := by
      have : 0 ≤ H / 4 * d ^ 2 := by positivity
      nlinarith
    have h2 : d * (H * d - 8 * t * G) ≤ 0 := by nlinarith
    by_contra hc
    rw [not_le] at hc
    have : 0 < d * (H * d - 8 * t * G) := mul_pos hd0 (by linarith)
    linarith

theorem exists_saddle {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set E) (Y : Set F) (f : E → F → ℝ) (H G : ℝ)
    (hX : IsCompact X) (hY : IsCompact Y) (hXne : X.Nonempty) (hYne : Y.Nonempty) (hH : 0 < H)
    (hsc : IsStronglyConvexConcaveOn X Y H f) (hlip : IsLipschitzPayoff X Y G f) :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  obtain ⟨hcvx, hccv⟩ := hsc
  obtain ⟨hG, hL⟩ := hlip
  -- minimisers
  have hmin : ∀ y ∈ Y, ∃ m ∈ X, ∀ x ∈ X, f m y ≤ f x y := by
    intro y hy
    have hcont : ContinuousOn (fun x => f x y) X := by
      have : LipschitzOnWith (Real.toNNReal G) (fun x => f x y) X := by
        refine LipschitzOnWith.of_dist_le' fun x₁ h₁ x₂ h₂ => ?_
        rw [Real.dist_eq, dist_eq_norm]
        have := hL x₁ h₁ x₂ h₂ y hy y hy
        simpa using this
      exact this.continuousOn
    obtain ⟨m, hm, hm'⟩ := hX.exists_isMinOn hXne hcont
    exact ⟨m, hm, fun x hx => hm' hx⟩
  classical
  let m : F → E := fun y => if hy : y ∈ Y then Classical.choose (hmin y hy) else hXne.some
  have hmX : ∀ y ∈ Y, m y ∈ X := fun y hy => by
    simp only [m, dif_pos hy]; exact (Classical.choose_spec (hmin y hy)).1
  have hmle : ∀ y ∈ Y, ∀ x ∈ X, f (m y) y ≤ f x y := fun y hy => by
    simp only [m, dif_pos hy]; exact (Classical.choose_spec (hmin y hy)).2
  let g : F → ℝ := fun y => f (m y) y
  have hgcont : ContinuousOn g Y := by
    have : LipschitzOnWith (Real.toNNReal G) g Y := by
      refine LipschitzOnWith.of_dist_le' fun y₁ h₁ y₂ h₂ => ?_
      rw [Real.dist_eq, dist_eq_norm, abs_le]
      have a1 := hmle y₁ h₁ (m y₂) (hmX y₂ h₂)
      have a2 := hmle y₂ h₂ (m y₁) (hmX y₁ h₁)
      have b1 := (abs_le.mp (hL (m y₂) (hmX y₂ h₂) (m y₂) (hmX y₂ h₂) y₁ h₁ y₂ h₂)).2
      have b2 := (abs_le.mp (hL (m y₁) (hmX y₁ h₁) (m y₁) (hmX y₁ h₁) y₁ h₁ y₂ h₂)).1
      simp only [sub_self, norm_zero, zero_add] at b1 b2
      simp only [g]
      constructor <;> linarith
    exact this.continuousOn
  obtain ⟨b, hb, hbmax⟩ := hY.exists_isMaxOn hYne hgcont
  have hgb : ∀ y ∈ Y, g y ≤ g b := fun y hy => hbmax hy
  set a := m b with ha_def
  have ha : a ∈ X := hmX b hb
  have hab : ∀ x ∈ X, f a b ≤ f x b := hmle b hb
  refine ⟨a, ha, b, hb, fun x hx y hy => le_trans ?_ (hab x hx)⟩
  -- show f a y ≤ f a b
  have hYc : Convex ℝ Y := (hccv a ha).1
  have hXc : Convex ℝ X := (hcvx b hb).1
  suffices hδ : f a y - f a b ≤ 0 by linarith
  refine nonpos_of_le_mul_small _ (8 * G ^ 2 / H) (by positivity) fun t ht0 ht1 => ?_
  set yt := (1 - t) • b + t • y with hyt
  have hytY : yt ∈ Y := hYc hb hy (by linarith) ht0.le (by ring)
  set xt := m yt
  have hxt : xt ∈ X := hmX yt hytY
  -- concavity in y at xt
  have hconc := (hccv xt hxt).2 hb hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
  have hconc' : (1 - t) * f xt b + t * f xt y ≤ f xt yt := by
    have : 0 ≤ (1 - t) * t * (H / 2 * ‖b - y‖ ^ 2) := by
      have : 0 ≤ 1 - t := by linarith
      positivity
    simp only [smul_eq_mul] at hconc
    linarith
  have hgyt : f xt yt ≤ f a b := hgb yt hytY
  -- quadratic growth at a (midpoint strong convexity)
  have hmid := (hcvx b hb).2 ha hxt (show (0:ℝ) ≤ 1 / 2 by norm_num) (show (0:ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num)
  have hmidX : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • xt ∈ X := hXc ha hxt (by norm_num) (by norm_num)
    (by norm_num)
  have hm2 := hab _ hmidX
  simp only [smul_eq_mul] at hmid
  set d := ‖a - xt‖ with hd
  have hquad : H / 4 * d ^ 2 ≤ f xt b - f a b := by nlinarith
  -- Lipschitz
  have hlipy := (abs_le.mp (hL a ha xt hxt y hy y hy)).2
  simp only [sub_self, norm_zero, add_zero] at hlipy
  -- combine
  have he : (1 - t) * (f xt b - f a b) ≤ t * (f a b - f xt y) := by nlinarith
  have hdd : H * d ≤ 8 * t * G ∨ f a y - f a b ≤ 0 := by
    by_cases hδ : f a y - f a b ≤ 0
    · exact Or.inr hδ
    · left
      rw [not_le] at hδ
      refine d_bound H G t d hH hG ht0 ht1 (norm_nonneg _) ?_
      have h1 : (1 - t) * (H / 4 * d ^ 2) ≤ (1 - t) * (f xt b - f a b) :=
        mul_le_mul_of_nonneg_left hquad (by linarith)
      nlinarith
  rcases hdd with hdd | hdd
  · have hGd : G * d ≤ 8 * t * G ^ 2 / H := by
      rw [le_div_iff₀ hH]; nlinarith
    have : 8 * G ^ 2 / H * t = 8 * t * G ^ 2 / H := by ring
    have hxy : f xt y ≤ f a b := by
      have h0 : 0 ≤ (1 - t) * (f xt b - f a b) :=
        mul_nonneg (by linarith) (by linarith [hab xt hxt])
      have : 0 ≤ t * (f a b - f xt y) := le_trans h0 he
      nlinarith
    rw [← hd] at hlipy
    linarith
  · have : 0 ≤ 8 * G ^ 2 / H * t := by positivity
    linarith

end SPMinimax

/-! ===== SP_Stab ===== -/

/-! # Piece C: consecutive saddle points are within 4G/(Ht). -/

namespace SPStab
open OnlineSaddlePoint

lemma cumPayoff_succ {E F : Type*} (L : ℕ → E → F → ℝ) (n : ℕ) (a : E) (b : F) :
    cumPayoff L (n + 1) a b = cumPayoff L n a b + L (n + 1) a b := by
  unfold cumPayoff
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma cumPayoff_zero {E F : Type*} (L : ℕ → E → F → ℝ) (a : E) (b : F) :
    cumPayoff L 0 a b = 0 := by
  simp [cumPayoff]

/-- Final real-arithmetic step. -/
lemma final_bound (a b G c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hG : 0 ≤ G)
    (h1 : c / 2 * (a ^ 2 + b ^ 2) ≤ G * (a + b)) : a + b ≤ 4 * G / c := by
  rw [le_div_iff₀ hc]
  have h2 : c * (a + b) ^ 2 ≤ 4 * G * (a + b) := by nlinarith [sq_nonneg (a - b)]
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · rw [← h]
    linarith
  · have h3 : (a + b) * c * (a + b) ≤ 4 * G * (a + b) := by nlinarith
    exact le_of_mul_le_mul_right h3 h

theorem stability {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H G : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hH : 0 < H)
    (hΦsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y (t * H) (cumPayoff L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y)
    (hsad : ∀ t ∈ Finset.Icc 1 T, IsSaddlePointOn X Y (cumPayoff L t) (x (t + 1)) (y (t + 1))) :
    ∀ t ∈ Finset.Icc 1 T, ‖x t - x (t + 1)‖ + ‖y t - y (t + 1)‖ ≤ 4 * G / (H * t) := by
  intro t ht
  obtain ⟨hx1, hy1, hstep⟩ := hrun
  have ht' := Finset.mem_Icc.mp ht
  obtain ⟨hxt1, hyt1, -, -⟩ := hstep t ht
  -- x t ∈ X, y t ∈ Y
  have hxyt : x t ∈ X ∧ y t ∈ Y := by
    rcases Nat.lt_or_ge t 2 with h | h
    · have : t = 1 := by omega
      subst this; exact ⟨hx1, hy1⟩
    · obtain ⟨a, b, -, -⟩ := hstep (t - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have e : t - 1 + 1 = t := by omega
      rw [e] at a b; exact ⟨a, b⟩
  obtain ⟨hxt, hyt⟩ := hxyt
  set Φ := cumPayoff L t
  obtain ⟨hcvx, hccv⟩ := hΦsc t ht
  have hs := hsad t ht
  -- step 1
  have A := OnlineLearningOCO.FoReL.lemma_2_8 X (t * H) (fun u => Φ u (y (t + 1)))
    (hcvx _ hyt1) (x (t + 1)) hxt1 (fun v hv => hs v hv (y (t + 1)) hyt1) (x t) hxt
  have B := OnlineLearningOCO.FoReL.lemma_2_8 Y (t * H) (-(fun v => Φ (x (t + 1)) v))
    (UniformConcaveOn.neg (hccv _ hxt1)) (y (t + 1)) hyt1
    (fun v hv => by simpa using hs (x (t + 1)) hxt1 v hv) (y t) hyt
  simp only [Pi.neg_apply] at A B
  -- step 2
  have C : cumPayoff L (t - 1) (x t) (y (t + 1)) ≤ cumPayoff L (t - 1) (x (t + 1)) (y t) := by
    rcases Nat.lt_or_ge t 2 with h | h
    · have : t - 1 = 0 := by omega
      rw [this, cumPayoff_zero, cumPayoff_zero]
    · have hs' := hsad (t - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have e : t - 1 + 1 = t := by omega
      rw [e] at hs'
      exact hs' (x (t + 1)) hxt1 (y (t + 1)) hyt1
  -- step 3
  have e : t = t - 1 + 1 := by omega
  have hΦ : ∀ a b, Φ a b = cumPayoff L (t - 1) a b + L t a b := by
    intro a b
    simp only [Φ]
    conv_lhs => rw [e]
    rw [cumPayoff_succ, ← e]
  rw [hΦ, hΦ] at A
  rw [hΦ, hΦ] at B
  obtain ⟨hG, hL⟩ := hlip t ht
  have D := hL (x t) hxt (x (t + 1)) hxt1 (y (t + 1)) hyt1 (y t) hyt
  have D' := (abs_le.mp D).2
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  rw [show H * (t : ℝ) = t * H by ring]
  apply final_bound _ _ G _ (norm_nonneg _) (norm_nonneg _) (by positivity) hG
  rw [norm_sub_rev (y (t + 1)) (y t)] at D'
  nlinarith [norm_sub_rev (y t) (y (t + 1))]

end SPStab

/-! ===== SP_Main ===== -/

/-! # Pieces B and D: SP-FTL plays saddle points; telescoping; the regret bound. -/

namespace SPMain
open OnlineSaddlePoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Cumulative payoffs -/

theorem cum_zero (L : ℕ → E → F → ℝ) (x : E) (y : F) : cumPayoff L 0 x y = 0 := by
  simp [cumPayoff]

theorem cum_succ (L : ℕ → E → F → ℝ) (t : ℕ) (x : E) (y : F) :
    cumPayoff L (t + 1) x y = cumPayoff L t x y + L (t + 1) x y := by
  simp only [cumPayoff]
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem strong_add {s : Set E} {m n : ℝ} {f g : E → ℝ} (hf : StrongConvexOn s m f)
    (hg : StrongConvexOn s n g) : StrongConvexOn s (m + n) (f + g) := by
  have := hf.add hg
  unfold StrongConvexOn
  convert this using 1
  funext r; simp only [Pi.add_apply]; ring

theorem strongc_add {s : Set E} {m n : ℝ} {f g : E → ℝ} (hf : StrongConcaveOn s m f)
    (hg : StrongConcaveOn s n g) : StrongConcaveOn s (m + n) (f + g) := by
  have := hf.add hg
  unfold StrongConcaveOn
  convert this using 1
  funext r; simp only [Pi.add_apply]; ring

theorem cum_sc (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H : ℝ) (T : ℕ)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t)) :
    ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y (t * H) (cumPayoff L t) := by
  intro t ht
  rw [Finset.mem_Icc] at ht
  obtain ⟨ht1, htT⟩ := ht
  induction t, ht1 using Nat.le_induction with
  | base =>
    have h1 := hsc 1 (by simp; omega)
    have e : cumPayoff L 1 = L 1 := by funext x y; simp [cumPayoff]
    rw [e]; simpa using h1
  | succ t ht1 ih =>
    have ih := ih (by omega)
    have hL := hsc (t + 1) (by simp; omega)
    have e : cumPayoff L (t + 1) = fun x y => cumPayoff L t x y + L (t + 1) x y := by
      funext x y; exact cum_succ L t x y
    rw [e]
    push_cast
    rw [add_mul, one_mul]
    exact ⟨fun y hy => strong_add (ih.1 y hy) (hL.1 y hy),
      fun x hx => strongc_add (ih.2 x hx) (hL.2 x hx)⟩

theorem cum_lip (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (G : ℝ) (T : ℕ)
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t)) (hG : 0 ≤ G) :
    ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y (t * G) (cumPayoff L t) := by
  intro t ht
  refine ⟨by positivity, fun x₁ hx₁ x₂ hx₂ y₁ hy₁ y₂ hy₂ => ?_⟩
  simp only [cumPayoff, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.Icc 1 t, |L i x₁ y₁ - L i x₂ y₂|
      ≤ ∑ _i ∈ Finset.Icc 1 t, G * (‖x₁ - x₂‖ + ‖y₁ - y₂‖) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiT : i ∈ Finset.Icc 1 T := by
          simp only [Finset.mem_Icc] at hi ht ⊢; omega
        exact (hlip i hiT).2 x₁ hx₁ x₂ hx₂ y₁ hy₁ y₂ hy₂
    _ = t * G * (‖x₁ - x₂‖ + ‖y₁ - y₂‖) := by simp; ring

/-! ## Piece B: a minimax choice is a saddle point when one exists -/

theorem bdd_above_x (X : Set E) (Y : Set F) (f : E → F → ℝ) (G : ℝ) (hY : IsCompact Y)
    (hlip : IsLipschitzPayoff X Y G f) {x : E} (hx : x ∈ X) (hYne : Y.Nonempty) :
    BddAbove ((fun y => f x y) '' Y) := by
  obtain ⟨C, hC⟩ := hY.isBounded.exists_norm_le
  obtain ⟨y₁, hy₁⟩ := hYne
  refine ⟨f x y₁ + G * (C + ‖y₁‖), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h := hlip.2 x hx x hx y hy y₁ hy₁
  have h2 : ‖y - y₁‖ ≤ C + ‖y₁‖ := (norm_sub_le _ _).trans (by linarith [hC y hy])
  have := mul_le_mul_of_nonneg_left h2 hlip.1
  simp only [sub_self, norm_zero, zero_add] at h
  linarith [le_abs_self (f x y - f x y₁)]

theorem bdd_below_y (X : Set E) (Y : Set F) (f : E → F → ℝ) (G : ℝ) (hX : IsCompact X)
    (hlip : IsLipschitzPayoff X Y G f) {y : F} (hy : y ∈ Y) (hXne : X.Nonempty) :
    BddBelow ((fun x => f x y) '' X) := by
  obtain ⟨C, hC⟩ := hX.isBounded.exists_norm_le
  obtain ⟨x₁, hx₁⟩ := hXne
  refine ⟨f x₁ y - G * (C + ‖x₁‖), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h := hlip.2 x hx x₁ hx₁ y hy y hy
  have h2 : ‖x - x₁‖ ≤ C + ‖x₁‖ := (norm_sub_le _ _).trans (by linarith [hC x hx])
  have := mul_le_mul_of_nonneg_left h2 hlip.1
  simp only [sub_self, norm_zero, add_zero] at h
  linarith [neg_abs_le (f x y - f x₁ y)]

theorem saddle_of_choice (X : Set E) (Y : Set F) (f : E → F → ℝ) (G : ℝ)
    (hX : IsCompact X) (hY : IsCompact Y) (hlip : IsLipschitzPayoff X Y G f)
    (hex : ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b)
    {x₀ : E} (hx₀X : x₀ ∈ X) {y₀ : F} (hy₀Y : y₀ ∈ Y)
    (hx₀ : ∀ x' ∈ X, sSup ((fun y' => f x₀ y') '' Y) ≤ sSup ((fun y' => f x' y') '' Y))
    (hy₀ : ∀ y' ∈ Y, sInf ((fun x' => f x' y') '' X) ≤ sInf ((fun x' => f x' y₀) '' X)) :
    IsSaddlePointOn X Y f x₀ y₀ ∧ f x₀ y₀ = minimaxValue X Y f := by
  obtain ⟨a, ha, b, hb, hab⟩ := hex
  have hXne : X.Nonempty := ⟨a, ha⟩
  have hYne : Y.Nonempty := ⟨b, hb⟩
  -- sup over y at x₀ is at most f a b
  have hsupa : sSup ((fun y => f a y) '' Y) ≤ f a b :=
    csSup_le (hYne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hab a ha y hy)
  have hup : ∀ y ∈ Y, f x₀ y ≤ f a b := fun y hy =>
    (le_csSup (bdd_above_x X Y f G hY hlip hx₀X hYne) ⟨y, hy, rfl⟩).trans
      ((hx₀ a ha).trans hsupa)
  have hinfb : f a b ≤ sInf ((fun x => f x b) '' X) :=
    le_csInf (hXne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hab x hx b hb)
  have hlo : ∀ x ∈ X, f a b ≤ f x y₀ := fun x hx =>
    (hinfb.trans (hy₀ b hb)).trans (csInf_le (bdd_below_y X Y f G hX hlip hy₀Y hXne) ⟨x, hx, rfl⟩)
  refine ⟨fun x hx y hy => (hup y hy).trans (hlo x hx), ?_⟩
  have hval : f x₀ y₀ = f a b := le_antisymm (hup y₀ hy₀Y) (hlo x₀ hx₀X)
  rw [hval]
  unfold minimaxValue
  apply le_antisymm
  · apply le_csInf (hXne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact (hab x hx b hb).trans (le_csSup (bdd_above_x X Y f G hY hlip hx hYne) ⟨b, hb, rfl⟩)
  · have hbdd : BddBelow ((fun x => sSup ((fun y => f x y) '' Y)) '' X) := by
      refine ⟨f a b, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (hab x hx b hb).trans (le_csSup (bdd_above_x X Y f G hY hlip hx hYne) ⟨b, hb, rfl⟩)
    exact (csInf_le hbdd ⟨a, ha, rfl⟩).trans hsupa

/-! ## The iterates are saddle points of the cumulative games -/

theorem iterates_saddle (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H G : ℝ) (T : ℕ)
    (x : ℕ → E) (y : ℕ → F) (hX : IsCompact X) (hY : IsCompact Y) (hH : 0 < H)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t)) (hG : 0 ≤ G)
    (hrun : IsSPFTLRun L X Y T x y) :
    ∀ t ∈ Finset.Icc 1 T, IsSaddlePointOn X Y (cumPayoff L t) (x (t + 1)) (y (t + 1)) ∧
      cumPayoff L t (x (t + 1)) (y (t + 1)) = minimaxValue X Y (cumPayoff L t) := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := by simp only [Finset.mem_Icc] at ht; exact_mod_cast ht.1
  obtain ⟨hx1, hy1, hrest⟩ := hrun
  obtain ⟨hxt, hyt, hminx, hmaxy⟩ := hrest t ht
  have hlipt := cum_lip X Y L G T hlip hG t ht
  have hex := SPMinimax.exists_saddle X Y (cumPayoff L t) (t * H) (t * G) hX hY ⟨_, hx1⟩ ⟨_, hy1⟩
    (by positivity) (cum_sc X Y L H T hsc t ht) hlipt
  exact saddle_of_choice X Y (cumPayoff L t) (t * G) hX hY hlipt hex hxt hyt hminx hmaxy

/-! ## Piece D: telescoping (Lemma 1) -/

theorem telescope (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (G : ℝ) (T : ℕ)
    (x : ℕ → E) (y : ℕ → F)
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y)
    (hsad : ∀ t ∈ Finset.Icc 1 T, IsSaddlePointOn X Y (cumPayoff L t) (x (t + 1)) (y (t + 1))) :
    ∀ n ≤ T,
      -G * ∑ t ∈ Finset.Icc 1 n, ‖x t - x (t + 1)‖ ≤
          ∑ t ∈ Finset.Icc 1 n, L t (x (t + 1)) (y (t + 1)) - cumPayoff L n (x (n + 1)) (y (n + 1)) ∧
        ∑ t ∈ Finset.Icc 1 n, L t (x (t + 1)) (y (t + 1)) - cumPayoff L n (x (n + 1)) (y (n + 1)) ≤
          G * ∑ t ∈ Finset.Icc 1 n, ‖y t - y (t + 1)‖ := by
  obtain ⟨hx1, hy1, hrest⟩ := hrun
  have memX : ∀ t, 1 ≤ t → t ≤ T + 1 → x t ∈ X := by
    intro t h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact hx1
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact (hrest s (by simp; omega)).1
  have memY : ∀ t, 1 ≤ t → t ≤ T + 1 → y t ∈ Y := by
    intro t h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact hy1
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact (hrest s (by simp; omega)).2.1
  intro n
  induction n with
  | zero => intro _; simp [cum_zero]
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hmem : n + 1 ∈ Finset.Icc 1 T := by simp; omega
    have hs := hsad (n + 1) hmem
    have hL := (hlip (n + 1) hmem).2
    have xa := memX (n + 1) (by omega) (by omega)
    have xb := memX (n + 2) (by omega) (by omega)
    have ya := memY (n + 1) (by omega) (by omega)
    have yb := memY (n + 2) (by omega) (by omega)
    -- the previous cumulative game: saddle at (x (n+1), y (n+1)), or zero
    have hprev1 : cumPayoff L n (x (n + 1)) (y (n + 1 + 1)) ≤
        cumPayoff L n (x (n + 1)) (y (n + 1)) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [cum_zero]
      · exact (hsad n (by simp; omega)) (x (n + 1)) xa (y (n + 1 + 1)) yb
    have hprev2 : cumPayoff L n (x (n + 1)) (y (n + 1)) ≤
        cumPayoff L n (x (n + 1 + 1)) (y (n + 1)) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [cum_zero]
      · exact (hsad n (by simp; omega)) (x (n + 1 + 1)) xb (y (n + 1)) ya
    -- the current cumulative game at its saddle point
    have hcur1 : cumPayoff L (n + 1) (x (n + 1 + 1)) (y (n + 1)) ≤
        cumPayoff L (n + 1) (x (n + 1 + 1)) (y (n + 1 + 1)) := hs (x (n + 1 + 1)) xb (y (n + 1)) ya
    have hcur2 : cumPayoff L (n + 1) (x (n + 1 + 1)) (y (n + 1 + 1)) ≤
        cumPayoff L (n + 1) (x (n + 1)) (y (n + 1 + 1)) := hs (x (n + 1)) xa (y (n + 1 + 1)) yb
    simp only [cum_succ] at hcur1 hcur2
    have l1 := hL (x (n + 1 + 1)) xb (x (n + 1 + 1)) xb (y (n + 1)) ya (y (n + 1 + 1)) yb
    have l2 := hL (x (n + 1)) xa (x (n + 1 + 1)) xb (y (n + 1 + 1)) yb (y (n + 1 + 1)) yb
    simp only [sub_self, norm_zero, zero_add, add_zero] at l1 l2
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega), cum_succ]
    have a1 := abs_le.1 l1
    have a2 := abs_le.1 l2
    rw [mul_add, mul_add]
    constructor <;> linarith
/-! ## The regret bound -/

theorem regret_bound (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H G : ℝ) (T : ℕ)
    (x : ℕ → E) (y : ℕ → F)
    (hT : 1 ≤ T) (hX : IsCompact X) (hY : IsCompact Y) (hH : 0 < H)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y) :
    spRegret L X Y T x y ≤ 8 * G ^ 2 / H * (1 + Real.log T) := by
  have hG : 0 ≤ G := (hlip 1 (by simp; omega)).1
  have hsadv := iterates_saddle X Y L H G T x y hX hY hH hsc hlip hG hrun
  have hsad : ∀ t ∈ Finset.Icc 1 T, IsSaddlePointOn X Y (cumPayoff L t) (x (t + 1)) (y (t + 1)) :=
    fun t ht => (hsadv t ht).1
  have hstab := SPStab.stability X Y L H G T x y hH (cum_sc X Y L H T hsc) hlip hrun hsad
  obtain ⟨tl, tu⟩ := telescope X Y L G T x y hlip hrun hsad T le_rfl
  have hV := (hsadv T (by simp; omega)).2
  obtain ⟨hx1, hy1, hrest⟩ := hrun
  have memX : ∀ t ∈ Finset.Icc 1 T, x t ∈ X ∧ x (t + 1) ∈ X ∧ y t ∈ Y ∧ y (t + 1) ∈ Y := by
    intro t ht
    have h1 := (hrest t ht)
    refine ⟨?_, h1.1, ?_, h1.2.1⟩
    · rcases Nat.eq_or_lt_of_le (Finset.mem_Icc.1 ht).1 with h | h
      · subst h; exact hx1
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        exact (hrest s (by simp at ht ⊢; omega)).1
    · rcases Nat.eq_or_lt_of_le (Finset.mem_Icc.1 ht).1 with h | h
      · subst h; exact hy1
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        exact (hrest s (by simp at ht ⊢; omega)).2.1
  set Dx := ∑ t ∈ Finset.Icc 1 T, ‖x t - x (t + 1)‖
  set Dy := ∑ t ∈ Finset.Icc 1 T, ‖y t - y (t + 1)‖
  set B := ∑ t ∈ Finset.Icc 1 T, 4 * G / (H * t)
  have hDB : Dx + Dy ≤ B := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum hstab
  have hDx0 : 0 ≤ Dx := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hDy0 : 0 ≤ Dy := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the shift from playing z_t instead of z_{t+1}
  have hshift : |∑ t ∈ Finset.Icc 1 T, (L t (x t) (y t) - L t (x (t + 1)) (y (t + 1)))| ≤
      G * (Dx + Dy) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨a, b, c, d⟩ := memX t ht
    have := (hlip t ht).2 _ a _ b _ c _ d
    linarith
  have hB : B = 4 * G / H * (harmonic T : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    simp only [B, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have : (t : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.1 ht).1; positivity
    field_simp
  have hharm : (harmonic T : ℝ) ≤ 1 + Real.log T := harmonic_le_one_add_log T
  have h4 : 0 ≤ 4 * G / H := by positivity
  have hBle : B ≤ 4 * G / H * (1 + Real.log T) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hharm h4
  unfold spRegret
  rw [← hV]
  have hsplit : ∑ t ∈ Finset.Icc 1 T, L t (x t) (y t) - cumPayoff L T (x (T + 1)) (y (T + 1)) =
      ∑ t ∈ Finset.Icc 1 T, (L t (x t) (y t) - L t (x (t + 1)) (y (t + 1))) +
      (∑ t ∈ Finset.Icc 1 T, L t (x (t + 1)) (y (t + 1)) - cumPayoff L T (x (T + 1)) (y (T + 1))) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hsecond : |∑ t ∈ Finset.Icc 1 T, L t (x (t + 1)) (y (t + 1)) -
      cumPayoff L T (x (T + 1)) (y (T + 1))| ≤ G * (Dx + Dy) := by
    rw [abs_le]; constructor <;> nlinarith
  have hGB : G * (Dx + Dy) ≤ G * B := mul_le_mul_of_nonneg_left hDB hG
  have : 2 * (G * B) ≤ 8 * G ^ 2 / H * (1 + Real.log T) := by
    have := mul_le_mul_of_nonneg_left hBle hG
    have e : G * (4 * G / H * (1 + Real.log T)) * 2 = 8 * G ^ 2 / H * (1 + Real.log T) := by ring
    linarith
  linarith

end SPMain

open OnlineSaddlePoint in
theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H G : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hT : 1 ≤ T) (hX : IsCompact X) (hY : IsCompact Y) (hH : 0 < H)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y) :
    spRegret L X Y T x y ≤ 8 * G ^ 2 / H * (1 + Real.log T) :=
  SPMain.regret_bound X Y L H G T x y hT hX hY hH hsc hlip hrun
