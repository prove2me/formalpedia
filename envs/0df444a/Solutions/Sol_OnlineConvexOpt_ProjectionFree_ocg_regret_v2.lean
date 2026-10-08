-- Prove2me | solution 1 for OnlineConvexOpt.ProjectionFree.ocg_regret_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:56:54.802788+00:00
-- url     : https://prove2.me/submissions/acf8ca9c-e884-40ea-8ffd-7ce38045ecc3

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

set_option autoImplicit false

namespace OCGAux

open scoped RealInnerProductSpace

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E → ℝ} {g x : E} (hF : HasGradientAt F g x) (w : E) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪g, w⟫ 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add x
  have hF' : HasFDerivAt F (InnerProductSpace.toDual ℝ E g) (x + (0:ℝ) • w) := by
    simpa using hasGradientAt_iff_hasFDerivAt.mp hF
  have h1 := hF'.comp_hasDerivAt (0:ℝ) hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {K : Set E} {F : E → ℝ} (hc : ConvexOn ℝ K F) {g x y : E}
    (hx : x ∈ K) (hy : y ∈ K) (hF : HasGradientAt F g x) : F x + ⟪g, y - x⟫ ≤ F y := by
  have hφ := hc.comp_affineMap (AffineMap.lineMap x y)
  have e : (F ∘ AffineMap.lineMap x y) = (fun t : ℝ => F (x + t • (y - x))) := by
    funext t; simp [AffineMap.lineMap_apply, add_comm]
  rw [e] at hφ
  have h0 : (0:ℝ) ∈ (AffineMap.lineMap x y) ⁻¹' K := by simpa using hx
  have h1 : (1:ℝ) ∈ (AffineMap.lineMap x y) ⁻¹' K := by simpa using hy
  have h := hφ.le_slope_of_hasDerivAt h0 h1 zero_lt_one (line_deriv hF (y - x))
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one, add_sub_cancel] at h
  linarith

theorem exists_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Set E} (hne : S.Nonempty) (hcl : IsClosed S) (hcv : Convex ℝ S) (c : E) :
    ∃ p ∈ S, ∀ w ∈ S, ⟪c - p, w - p⟫ ≤ 0 := by
  obtain ⟨p, hp, hpe⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv c
  exact ⟨p, hp, (norm_eq_iInf_iff_real_inner_le_zero hcv hp).mp hpe⟩

theorem vi_pyth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c p w : E} (h : ⟪c - p, w - p⟫ ≤ 0) :
    ‖p - c‖ ^ 2 + ‖w - p‖ ^ 2 ≤ ‖w - c‖ ^ 2 := by
  have e : w - c = (w - p) + (p - c) := by abel
  rw [e, norm_add_sq_real]
  have : ⟪w - p, p - c⟫ = - ⟪c - p, w - p⟫ := by
    rw [show p - c = -(c - p) by abel, inner_neg_right, real_inner_comm]
  linarith

theorem vi_stab {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c c' p p' : E} (h1 : ⟪c - p, p' - p⟫ ≤ 0) (h2 : ⟪c' - p', p - p'⟫ ≤ 0) :
    ‖p - p'‖ ^ 2 ≤ ⟪c - c', p - p'⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
  linarith

theorem phi_diff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (S x1 y z : E) :
    (η * ⟪S, y⟫ + ‖y - x1‖ ^ 2) - (η * ⟪S, z⟫ + ‖z - x1‖ ^ 2) =
      ‖y - (x1 - (η / 2) • S)‖ ^ 2 - ‖z - (x1 - (η / 2) • S)‖ ^ 2 := by
  have ey : y - (x1 - (η / 2) • S) = (y - x1) + (η / 2) • S := by abel
  have ez : z - (x1 - (η / 2) • S) = (z - x1) + (η / 2) • S := by abel
  rw [ey, ez, norm_add_sq_real, norm_add_sq_real, inner_smul_right, inner_smul_right,
    inner_sub_left, inner_sub_left, real_inner_comm y S, real_inner_comm z S]
  ring

theorem fw_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x v p c x' p' g : E} {σ D η G : ℝ}
    (hσ0 : 0 ≤ σ) (hη : 0 ≤ η)
    (hx' : x' = (1 - σ) • x + σ • v)
    (hvd : ‖v - x‖ ≤ D)
    (hfw : ⟪x - c, v⟫ ≤ ⟪x - c, p⟫)
    (hpp' : ⟪c - p, p' - p⟫ ≤ 0)
    (hg : ‖g‖ ≤ G) :
    ‖x' - (c - (η / 2) • g)‖ ^ 2 - ‖p' - (c - (η / 2) • g)‖ ^ 2 ≤
      (1 - σ) * (‖x - c‖ ^ 2 - ‖p - c‖ ^ 2) + σ ^ 2 * D ^ 2 + η * G * ‖x' - p'‖ := by
  have e1 : x' - c = (x - c) + σ • (v - x) := by rw [hx']; module
  have n1 : ‖x' - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * (σ * ⟪x - c, v - x⟫) + σ ^ 2 * ‖v - x‖ ^ 2 := by
    rw [e1, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have i1 : ⟪x - c, v - x⟫ ≤ ⟪x - c, p - x⟫ := by
    rw [inner_sub_right, inner_sub_right]; linarith
  have i2 : 2 * ⟪x - c, p - x⟫ = ‖p - c‖ ^ 2 - ‖x - c‖ ^ 2 - ‖p - x‖ ^ 2 := by
    have e : p - c = (p - x) + (x - c) := by abel
    rw [e, norm_add_sq_real, real_inner_comm]; ring
  have i4 := vi_pyth hpp'
  have e2 : ‖x' - (c - (η / 2) • g)‖ ^ 2 - ‖p' - (c - (η / 2) • g)‖ ^ 2 =
      ‖x' - c‖ ^ 2 - ‖p' - c‖ ^ 2 + η * ⟪x' - p', g⟫ := by
    have ex : x' - (c - (η / 2) • g) = (x' - c) + (η / 2) • g := by abel
    have ep : p' - (c - (η / 2) • g) = (p' - c) + (η / 2) • g := by abel
    rw [ex, ep, norm_add_sq_real, norm_add_sq_real, inner_smul_right, inner_smul_right]
    simp only [inner_sub_left]
    ring
  have i5 : η * ⟪x' - p', g⟫ ≤ η * G * ‖x' - p'‖ := by
    have h1 : ⟪x' - p', g⟫ ≤ ‖x' - p'‖ * ‖g‖ := real_inner_le_norm _ _
    have h2 : ‖x' - p'‖ * ‖g‖ ≤ ‖x' - p'‖ * G := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    nlinarith
  have i6 : ‖v - x‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvd 2
  have j1 := mul_le_mul_of_nonneg_left i1 hσ0
  have j2 := mul_le_mul_of_nonneg_left i6 (sq_nonneg σ)
  have j3 : 0 ≤ σ * ‖p - x‖ ^ 2 := mul_nonneg hσ0 (sq_nonneg _)
  have j4 : σ * (2 * ⟪x - c, p - x⟫) = σ * (‖p - c‖ ^ 2 - ‖x - c‖ ^ 2 - ‖p - x‖ ^ 2) := by
    rw [i2]
  rw [e2, n1]
  nlinarith

theorem core_real {s s' σ : ℝ} (hs : 1 ≤ s) (hss : s' ^ 2 = s ^ 2 + 1) (hs'0 : 0 < s')
    (hσ : σ = min 1 (2 / s)) : (1 - σ) * (4 / s) + σ ^ 2 ≤ 4 / s' - 1 / s' ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hrhs : 4 / s' - 1 / s' ^ 2 = (4 * s' - 1) / s' ^ 2 := by field_simp
  have hss' : s ≤ s' := by nlinarith
  rcases le_or_gt s 2 with h2 | h2
  · have : (1:ℝ) ≤ 2 / s := by rw [le_div_iff₀ hs0]; linarith
    rw [hσ, min_eq_left this, hrhs, le_div_iff₀ (by positivity)]
    have hs'3 : s' ≤ 3 := by nlinarith
    nlinarith
  · have : 2 / s ≤ (1:ℝ) := by rw [div_le_iff₀ hs0]; linarith
    rw [hσ, min_eq_right this, hrhs]
    have hlhs : (1 - 2 / s) * (4 / s) + (2 / s) ^ 2 = (4 * s - 4) / s ^ 2 := by
      field_simp; ring
    rw [hlhs, div_le_div_iff₀ (by positivity) (by positivity), hss]
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hss')]

theorem step_real {D a σ h h' y' u' s : ℝ} (hD : 0 < D) (ha0 : 0 ≤ a) (hs : 0 < s)
    (hu'1 : 1 ≤ u') (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hy0 : 0 ≤ y') (hy2 : y' ^ 2 ≤ h')
    (hrec : h' ≤ (1 - σ) * h + σ ^ 2 * D ^ 2 + a * y') (hih : h ≤ 4 * D ^ 2 / s)
    (hcore : (1 - σ) * (4 / s) + σ ^ 2 ≤ 4 / u' ^ 2 - 1 / (u' ^ 2) ^ 2)
    (hau : a ≤ D / (2 * u' ^ 3)) : h' ≤ 4 * D ^ 2 / u' ^ 2 := by
  have hu' : 0 < u' := by linarith
  set m := 2 * D / u' with hm_def
  have hm : 0 < m := by positivity
  have hm2 : m ^ 2 = 4 * D ^ 2 / u' ^ 2 := by rw [hm_def]; field_simp; ring
  have ham : a * m ≤ D ^ 2 / (u' ^ 2) ^ 2 := by
    calc a * m ≤ D / (2 * u' ^ 3) * m := mul_le_mul_of_nonneg_right hau hm.le
      _ = D ^ 2 / (u' ^ 2) ^ 2 := by rw [hm_def]; field_simp
  have hD2 : D ^ 2 / (u' ^ 2) ^ 2 ≤ m ^ 2 / 4 := by
    rw [hm2, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu'1 2, sq_nonneg D,
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu'1 2)
        (sq_nonneg D)]
  have hB1 : (1 - σ) * h ≤ (1 - σ) * (4 * D ^ 2 / s) :=
    mul_le_mul_of_nonneg_left hih (by linarith)
  have hB2 : (1 - σ) * (4 * D ^ 2 / s) + σ ^ 2 * D ^ 2 ≤ m ^ 2 - D ^ 2 / (u' ^ 2) ^ 2 := by
    have : (1 - σ) * (4 * D ^ 2 / s) + σ ^ 2 * D ^ 2 = D ^ 2 * ((1 - σ) * (4 / s) + σ ^ 2) := by
      field_simp
    rw [this, hm2]
    have h3 := mul_le_mul_of_nonneg_left hcore (sq_nonneg D)
    have : D ^ 2 * (4 / u' ^ 2 - 1 / (u' ^ 2) ^ 2) = 4 * D ^ 2 / u' ^ 2 - D ^ 2 / (u' ^ 2) ^ 2 := by
      field_simp
    linarith
  have hB : (1 - σ) * h + σ ^ 2 * D ^ 2 ≤ m ^ 2 - a * m := by linarith
  have hym : y' ≤ m := by
    by_contra hc
    push_neg at hc
    have h1 : 0 < y' + m - a := by nlinarith
    nlinarith [mul_pos (sub_pos.2 hc) h1]
  have : a * y' ≤ a * m := mul_le_mul_of_nonneg_left hym ha0
  rw [← hm2]
  linarith

end OCGAux

open OCGAux in
open scoped RealInnerProductSpace in
open OnlineConvexOpt.ProjectionFree in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E) (hgradG : ∀ t : ℕ, 1 ≤ t → ‖gradf t‖ ≤ G)
    (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v) :
    (∑ t ∈ Finset.Icc 1 T, f t (x t)) -
        sInf ((fun xstar => ∑ t ∈ Finset.Icc 1 T, f t xstar) '' K) ≤
      8 * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨hx1', -, hgrad, hlin, hstep⟩ := hrun
  -- quarter powers
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ → ℝ, q = fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hq0 : ∀ n, 0 ≤ q n := fun n => by rw [hqdef]; positivity
  have hq4 : ∀ n : ℕ, q n ^ 4 = n := by
    intro n; rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hq1 : ∀ n : ℕ, 1 ≤ n → 1 ≤ q n := by
    intro n hn
    by_contra hc; push_neg at hc
    have : q n ^ 4 < 1 := pow_lt_one₀ (hq0 n) hc (by norm_num)
    rw [hq4] at this
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hqmono : ∀ m n : ℕ, m ≤ n → q m ≤ q n := by
    intro m n hmn; rw [hqdef]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmn) (by norm_num)
  have hT34 : (T : ℝ) ^ (3 / 4 : ℝ) = q T ^ 3 := by
    rw [hqdef]; dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hsqrt : ∀ n : ℕ, Real.sqrt n = q n ^ 2 := by
    intro n; rw [Real.sqrt_eq_rpow, hqdef]; dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hQ1 : 1 ≤ q T := hq1 T hT
  have hQpos : 0 < q T := by linarith
  have hηpos : 0 < η := by rw [hη, hT34]; positivity
  have hηG : η * G = D / (2 * q T ^ 3) := by rw [hη, hT34]; field_simp
  -- projections onto closure K
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → E, S = fun t => ∑ τ ∈ Finset.Ico 1 t, gradf τ := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → E, c = fun t => x1 - (η / 2) • S t := ⟨_, rfl⟩
  have hK'ne : (closure K).Nonempty := hKne.closure
  have hproj : ∀ t, ∃ p ∈ closure K, ∀ w ∈ closure K, ⟪c t - p, w - p⟫ ≤ 0 :=
    fun t => exists_proj hK'ne isClosed_closure hKconv.closure (c t)
  choose p hpK hpVI using hproj
  have hσ01 : ∀ t, 1 ≤ t → 0 ≤ σ t ∧ σ t ≤ 1 := by
    intro t ht; rw [hσ t ht]
    exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  have hvK : ∀ t, 1 ≤ t → v t ∈ K := fun t ht => (hlin t ht).1
  have hxK : ∀ t, 1 ≤ t → x t ∈ K := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [hx1']; exact hx1
    | succ t ht ih =>
      rw [hstep t ht]
      exact hKconv ih (hvK t ht) (by linarith [(hσ01 t ht).2]) (hσ01 t ht).1 (by ring)
  have hS : ∀ t, 1 ≤ t → S (t + 1) = S t + gradf t := by
    intro t ht; rw [hSdef]; exact Finset.sum_Ico_succ_top ht _
  have hc : ∀ t, 1 ≤ t → c (t + 1) = c t - (η / 2) • gradf t := by
    intro t ht; rw [hcdef]; dsimp only; rw [hS t ht, smul_add]; abel
  have hFW : ∀ t, 1 ≤ t → ⟪x t - c t, v t⟫ ≤ ⟪x t - c t, p t⟫ := by
    intro t ht
    have hAG : AggregateGradient gradf x1 η t (x t) = (2:ℝ) • (x t - c t) := by
      rw [hcdef]; simp only [AggregateGradient, hSdef]; module
    have hl := (hlin t ht).2
    rw [hAG] at hl
    have hcl : closure K ⊆ {w | ⟪(2:ℝ) • (x t - c t), v t⟫ ≤ ⟪(2:ℝ) • (x t - c t), w⟫} :=
      closure_minimal hl (isClosed_le continuous_const (continuous_const.inner continuous_id))
    have := hcl (hpK t)
    simp only [Set.mem_setOf_eq, real_inner_smul_left] at this
    linarith
  have hy2 : ∀ t, 1 ≤ t → ‖x t - p t‖ ^ 2 ≤ ‖x t - c t‖ ^ 2 - ‖p t - c t‖ ^ 2 := by
    intro t ht
    have := vi_pyth (hpVI t (x t) (subset_closure (hxK t ht)))
    linarith
  have hrec : ∀ t, 1 ≤ t →
      ‖x (t + 1) - c (t + 1)‖ ^ 2 - ‖p (t + 1) - c (t + 1)‖ ^ 2 ≤
        (1 - σ t) * (‖x t - c t‖ ^ 2 - ‖p t - c t‖ ^ 2) + σ t ^ 2 * D ^ 2 +
          η * G * ‖x (t + 1) - p (t + 1)‖ := by
    intro t ht
    rw [hc t ht]
    have hvd : ‖v t - x t‖ ≤ D := by
      have := hD (v t) (hvK t ht) (x t) (hxK t ht); rwa [dist_eq_norm] at this
    exact fw_step (hσ01 t ht).1 hηpos.le (hstep t ht) hvd (hFW t ht)
      (hpVI t (p (t + 1)) (hpK (t + 1))) (hgradG t ht)
  -- the FW gap bound
  have hbound : ∀ t, 1 ≤ t → t ≤ T →
      ‖x t - c t‖ ^ 2 - ‖p t - c t‖ ^ 2 ≤ 4 * D ^ 2 / q t ^ 2 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro _
      have hc1 : c 1 = x1 := by rw [hcdef, hSdef]; simp
      rw [hc1, hx1', sub_self, norm_zero]
      have : 0 ≤ 4 * D ^ 2 / q 1 ^ 2 := by have := hq0 1; positivity
      nlinarith [sq_nonneg ‖p 1 - x1‖]
    | succ t ht ih =>
      intro hT1
      have ih' := ih (by omega)
      have hu'1 : 1 ≤ q (t + 1) := hq1 (t + 1) (by omega)
      have hs : 1 ≤ q t ^ 2 := by nlinarith [hq1 t ht]
      have hcore := core_real (s := q t ^ 2) (s' := q (t + 1) ^ 2) (σ := σ t) hs
        (by
          rw [← pow_mul, ← pow_mul]; norm_num; rw [hq4, hq4]; push_cast; ring)
        (by positivity) (by rw [hσ t ht, hsqrt])
      have hau : η * G ≤ D / (2 * q (t + 1) ^ 3) := by
        rw [hηG]
        apply div_le_div_of_nonneg_left hDpos.le (by positivity)
        have := hqmono (t + 1) T hT1
        have := pow_le_pow_left₀ (by linarith) this 3
        linarith
      exact step_real hDpos (by positivity) (by linarith) hu'1 (hσ01 t ht).1 (hσ01 t ht).2
        (norm_nonneg _) (hy2 (t + 1) (by omega)) (hrec t ht) ih' hcore hau
  have hy : ∀ t, 1 ≤ t → t ≤ T → ‖x t - p t‖ ≤ 2 * D / q t := by
    intro t ht htT
    have h1 := hy2 t ht
    have h2 := hbound t ht htT
    have hqt : 0 < q t := by linarith [hq1 t ht]
    have hm0 : 0 < 2 * D / q t := by positivity
    have : (2 * D / q t) ^ 2 = 4 * D ^ 2 / q t ^ 2 := by field_simp; ring
    nlinarith [norm_nonneg (x t - p t)]
  -- sum of t^{-1/4}
  have hsumq : ∀ n : ℕ, ∑ t ∈ Finset.Icc 1 n, 1 / q t ≤ 4 / 3 * q n ^ 3 := by
    intro n
    induction n with
    | zero => simp; exact pow_nonneg (hq0 0) 3
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hr0 := hq0 n
      have hr' : 1 ≤ q (n + 1) := hq1 (n + 1) (by omega)
      have hrr : q n ≤ q (n + 1) := hqmono n (n + 1) (by omega)
      have h4 : q (n + 1) ^ 4 = q n ^ 4 + 1 := by rw [hq4, hq4]; push_cast; ring
      have e : (q (n + 1) - q n) * ((q (n + 1) + q n) * (q (n + 1) ^ 2 + q n ^ 2)) = 1 := by
        have : (q (n + 1) - q n) * ((q (n + 1) + q n) * (q (n + 1) ^ 2 + q n ^ 2)) =
          q (n + 1) ^ 4 - q n ^ 4 := by ring
        rw [this, h4]; ring
      have hle : 4 * q n ^ 3 ≤ (q (n + 1) + q n) * (q (n + 1) ^ 2 + q n ^ 2) := by
        have a1 : 2 * q n ≤ q (n + 1) + q n := by linarith
        have a2 : 2 * q n ^ 2 ≤ q (n + 1) ^ 2 + q n ^ 2 := by
          nlinarith [pow_le_pow_left₀ hr0 hrr 2]
        have := mul_le_mul a1 a2 (by positivity) (by positivity)
        nlinarith
      have key : (q (n + 1) - q n) * (4 * q n ^ 3) ≤ 1 := by
        rw [← e]; exact mul_le_mul_of_nonneg_left hle (by linarith)
      have hstep1 : 1 / q (n + 1) ≤ 4 / 3 * (q (n + 1) ^ 3 - q n ^ 3) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  -- stability of the projections
  have hstab : ∀ t, 1 ≤ t → ⟪gradf t, p t - p (t + 1)⟫ ≤ η * G ^ 2 / 2 := by
    intro t ht
    have h0 := vi_stab (hpVI t (p (t + 1)) (hpK (t + 1))) (hpVI (t + 1) (p t) (hpK t))
    rw [hc t ht, sub_sub_cancel, real_inner_smul_left] at h0
    set d := ‖p t - p (t + 1)‖
    set z := ⟪gradf t, p t - p (t + 1)⟫
    have hzG : z ≤ G * d := by
      have h1 : z ≤ ‖gradf t‖ * d := real_inner_le_norm _ _
      have h2 : ‖gradf t‖ * d ≤ G * d := mul_le_mul_of_nonneg_right (hgradG t ht) (norm_nonneg _)
      linarith
    have hd0 : 0 ≤ d := norm_nonneg _
    by_contra hz
    push_neg at hz
    have hd : η * G / 2 < d := by nlinarith
    have hηG0 : 0 < η * G := mul_pos hηpos hGpos
    have h3 : d * (η * G / 2) < d * d := mul_lt_mul_of_pos_left hd (by linarith)
    have h4 : η / 2 * z ≤ η / 2 * (G * d) := mul_le_mul_of_nonneg_left hzG (by linarith)
    nlinarith
  -- FTRL telescoping
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → E → ℝ, Φ = fun t y => η * ⟪S t, y⟫ + ‖y - x1‖ ^ 2 := ⟨_, rfl⟩
  have hΦmin : ∀ t, ∀ w ∈ closure K, Φ t (p t) ≤ Φ t w := by
    intro t w hw
    have h1 := phi_diff η (S t) x1 w (p t)
    have h2 := vi_pyth (hpVI t w hw)
    rw [hcdef] at h2
    rw [hΦdef]; dsimp only
    nlinarith [sq_nonneg ‖w - p t‖]
  have hΦstep : ∀ t, 1 ≤ t → ∀ y, Φ (t + 1) y = Φ t y + η * ⟪gradf t, y⟫ := by
    intro t ht y; rw [hΦdef]; dsimp only; rw [hS t ht, inner_add_left]; ring
  have htele : ∀ n : ℕ, η * ∑ t ∈ Finset.Icc 1 n, ⟪gradf t, p (t + 1)⟫ ≤ Φ (n + 1) (p (n + 1)) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1), Finset.sum_empty, mul_zero]
      rw [hΦdef, hSdef]; simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), mul_add,
        hΦstep (n + 1) (by omega)]
      have := hΦmin (n + 1) (p (n + 1 + 1)) (hpK _)
      linarith
  have hftrl : ∀ w ∈ K, ∑ t ∈ Finset.Icc 1 T, ⟪gradf t, p (t + 1) - w⟫ ≤ D ^ 2 / η := by
    intro w hw
    have h1 := htele T
    have h2 := hΦmin (T + 1) w (subset_closure hw)
    have h3 : Φ (T + 1) w = η * ∑ t ∈ Finset.Icc 1 T, ⟪gradf t, w⟫ + ‖w - x1‖ ^ 2 := by
      rw [hΦdef, hSdef]; dsimp only
      rw [sum_inner, Finset.Ico_add_one_right_eq_Icc]
    have h4 : ‖w - x1‖ ^ 2 ≤ D ^ 2 := by
      have := hD w hw x1 hx1; rw [dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have h5 : ∑ t ∈ Finset.Icc 1 T, ⟪gradf t, p (t + 1) - w⟫ =
        ∑ t ∈ Finset.Icc 1 T, ⟪gradf t, p (t + 1)⟫ - ∑ t ∈ Finset.Icc 1 T, ⟪gradf t, w⟫ := by
      rw [← Finset.sum_sub_distrib]; simp only [inner_sub_right]
    rw [h5, le_div_iff₀ hηpos]
    nlinarith
  -- convexity
  have hcvx : ∀ t, 1 ≤ t → ∀ w ∈ K, f t (x t) - f t w ≤ ⟪gradf t, x t - w⟫ := by
    intro t ht w hw
    have := convex_fo (hfconv t) (hxK t ht) hw (hgrad t ht)
    have e : ⟪gradf t, w - x t⟫ = -⟪gradf t, x t - w⟫ := by
      rw [← inner_neg_right, neg_sub]
    linarith
  -- main bound for every comparator
  have hmain : ∀ w ∈ K, ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t w ≤
      8 * D * G * q T ^ 3 := by
    intro w hw
    rw [← Finset.sum_sub_distrib]
    have hA : ∀ t ∈ Finset.Icc 1 T, f t (x t) - f t w ≤
        ⟪gradf t, x t - p t⟫ + ⟪gradf t, p t - p (t + 1)⟫ + ⟪gradf t, p (t + 1) - w⟫ := by
      intro t htm
      rw [Finset.mem_Icc] at htm
      have := hcvx t htm.1 w hw
      rw [← inner_add_right, ← inner_add_right]
      have e : x t - p t + (p t - p (t + 1)) + (p (t + 1) - w) = x t - w := by abel
      rw [e]; exact this
    have hB1 : ∀ t ∈ Finset.Icc 1 T, ⟪gradf t, x t - p t⟫ ≤ 2 * D * G * (1 / q t) := by
      intro t htm
      rw [Finset.mem_Icc] at htm
      have h1 : ⟪gradf t, x t - p t⟫ ≤ ‖gradf t‖ * ‖x t - p t‖ := real_inner_le_norm _ _
      have h2 := hgradG t htm.1
      have h3 := hy t htm.1 htm.2
      have h4 : ‖gradf t‖ * ‖x t - p t‖ ≤ G * (2 * D / q t) :=
        mul_le_mul h2 h3 (norm_nonneg _) hGpos.le
      have : G * (2 * D / q t) = 2 * D * G * (1 / q t) := by ring
      linarith
    have hB2 : ∀ t ∈ Finset.Icc 1 T, ⟪gradf t, p t - p (t + 1)⟫ ≤ η * G ^ 2 / 2 := by
      intro t htm; rw [Finset.mem_Icc] at htm; exact hstab t htm.1
    have s1 := Finset.sum_le_sum hA
    have s2 := Finset.sum_le_sum hB1
    have s3 := Finset.sum_le_sum hB2
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at s1
    rw [← Finset.mul_sum] at s2
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at s3
    have s4 := hftrl w hw
    have s5 := hsumq T
    have hTQ : ((T + 1 - 1 : ℕ) : ℝ) = q T ^ 4 := by rw [hq4]; simp
    rw [hTQ] at s3
    have e1 : q T ^ 4 * (η * G ^ 2 / 2) = D * G * q T / 4 := by
      rw [show q T ^ 4 * (η * G ^ 2 / 2) = q T ^ 4 * (η * G) * G / 2 by ring, hηG]
      field_simp; ring
    have e2 : D ^ 2 / η = 2 * D * G * q T ^ 3 := by
      rw [hη, hT34]; field_simp
    have hQQ : q T ≤ q T ^ 3 := by
      have : 1 ≤ q T ^ 2 := one_le_pow₀ hQ1
      nlinarith
    have hDG : 0 < D * G := mul_pos hDpos hGpos
    have s6 : 2 * D * G * ∑ t ∈ Finset.Icc 1 T, 1 / q t ≤ 2 * D * G * (4 / 3 * q T ^ 3) :=
      mul_le_mul_of_nonneg_left s5 (by positivity)
    nlinarith
  -- conclude
  rw [hT34]
  have hne : ((fun xstar => ∑ t ∈ Finset.Icc 1 T, f t xstar) '' K).Nonempty := hKne.image _
  have hlow : ∑ t ∈ Finset.Icc 1 T, f t (x t) - 8 * D * G * q T ^ 3 ≤
      sInf ((fun xstar => ∑ t ∈ Finset.Icc 1 T, f t xstar) '' K) := by
    apply le_csInf hne
    rintro _ ⟨w, hw, rfl⟩
    have := hmain w hw
    linarith
  linarith
