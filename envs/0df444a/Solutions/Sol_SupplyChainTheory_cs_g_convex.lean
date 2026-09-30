-- Prove2me | solution 1 for SupplyChainTheory.cs_g_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T16:35:53.570796+00:00
-- url     : https://prove2.me/submissions/03ea4ab4-72f4-404c-8cbe-321c5521563a

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

set_option autoImplicit false

lemma d4be_cont (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ a b, |F a - F b| ≤ K * |a - b|) :
    Continuous F :=
  (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) (f := F) (fun a b => by
    rw [Real.dist_eq, Real.dist_eq]
    exact hF a b)).continuous

open MeasureTheory in
lemma d4be_int (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hid : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun u => F (y - u)) μ := by
  refine Integrable.mono' (g := fun u => |F 0| + K * (|y| + |u|)) ?_ ?_ ?_
  · exact (integrable_const _).add (((integrable_const |y|).add hid.abs).const_mul K)
  · exact ((d4be_cont F K hK hF).measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  · refine ae_of_all _ (fun u => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hF (y - u) 0
    rw [sub_zero] at h1
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    have h2 : |y - u| ≤ |y| + |u| :=
      abs_le.2 ⟨by linarith [neg_abs_le y, le_abs_self u], by linarith [le_abs_self y, neg_abs_le u]⟩
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (F 0), le_abs_self (F 0)]

open MeasureTheory in
lemma d4be_lip_int (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hid : Integrable (fun x : ℝ => x) μ) (y z : ℝ) :
    |∫ u, F (y - u) ∂μ - ∫ u, F (z - u) ∂μ| ≤ K * |y - z| := by
  have hy := d4be_int F K hK hF μ hid y
  have hz := d4be_int F K hK hF μ hid z
  rw [← integral_sub hy hz]
  calc |∫ u, (F (y - u) - F (z - u)) ∂μ| ≤ ∫ u, |F (y - u) - F (z - u)| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, K * |y - z| ∂μ := by
        apply integral_mono (hy.sub hz).abs (integrable_const _)
        intro u
        have := hF (y - u) (z - u)
        simpa [show y - u - (z - u) = y - z by ring] using this
    _ = K * |y - z| := by simp

open MeasureTheory SupplyChainTheory in
lemma d4be_bar_lip (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |csBar N h p D S k x - csBar N h p D S k y| ≤ L * |x - y| := by
  induction k with
  | zero =>
    refine ⟨|p + localHolding N h 1|, abs_nonneg _, fun x y => ?_⟩
    show |(p + localHolding N h 1) * max (-x) 0 - (p + localHolding N h 1) * max (-y) 0|
      ≤ |p + localHolding N h 1| * |x - y|
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
    rw [show -x - -y = -(x - y) by ring, abs_neg]
  | succ k ih =>
    obtain ⟨L, hL, hlip⟩ := ih
    have hF : ∀ a b, |(h (k + 1) * a + csBar N h p D S k a) - (h (k + 1) * b + csBar N h p D S k b)|
        ≤ (|h (k + 1)| + L) * |a - b| := by
      intro a b
      have e : (h (k + 1) * a + csBar N h p D S k a) - (h (k + 1) * b + csBar N h p D S k b)
          = h (k + 1) * (a - b) + (csBar N h p D S k a - csBar N h p D S k b) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, add_mul]
      exact add_le_add le_rfl (hlip a b)
    refine ⟨|h (k + 1)| + L, by positivity, fun x y => ?_⟩
    have hm : |min (S (k + 1)) x - min (S (k + 1)) y| ≤ |x - y| := by
      refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
      simp
    have key := d4be_lip_int (fun t => h (k + 1) * t + csBar N h p D S k t) (|h (k + 1)| + L)
      (by positivity) hF (D (k + 1)) (hD (k + 1)) (min (S (k + 1)) x) (min (S (k + 1)) y)
    show |∫ d, (h (k + 1) * (min (S (k + 1)) x - d) + csBar N h p D S k (min (S (k + 1)) x - d))
          ∂(D (k + 1))
        - ∫ d, (h (k + 1) * (min (S (k + 1)) y - d) + csBar N h p D S k (min (S (k + 1)) y - d))
          ∂(D (k + 1))| ≤ (|h (k + 1)| + L) * |x - y|
    exact key.trans (mul_le_mul_of_nonneg_left hm (by positivity))

open MeasureTheory SupplyChainTheory in
lemma d4be_hat_lip (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, |csHat N h p D S j a - csHat N h p D S j b| ≤ K * |a - b| := by
  obtain ⟨L, hL, hlip⟩ := d4be_bar_lip N h p D S hD (j - 1)
  refine ⟨|h j| + L, by positivity, fun a b => ?_⟩
  unfold csHat
  have e : h j * a + csBar N h p D S (j - 1) a - (h j * b + csBar N h p D S (j - 1) b)
      = h j * (a - b) + (csBar N h p D S (j - 1) a - csBar N h p D S (j - 1) b) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, add_mul]
  exact add_le_add le_rfl (hlip a b)

open MeasureTheory in
lemma d4be_G_conv (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) (μ : Measure ℝ)
    (hint : ∀ y, Integrable (fun u => g (y - u)) μ) :
    ConvexOn ℝ Set.univ (fun y => ∫ u, g (y - u) ∂μ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint x).const_mul a) ((hint y).const_mul b)]
  apply integral_mono (hint _) (((hint x).const_mul a).add ((hint y).const_mul b))
  intro u
  show g (a * x + b * y - u) ≤ a * g (x - u) + b * g (y - u)
  have h := hg.2 (Set.mem_univ (x - u)) (Set.mem_univ (y - u)) ha hb hab
  simp only [smul_eq_mul] at h
  have he : a * (x - u) + b * (y - u) = a * x + b * y - u := by
    have : u = a * u + b * u := by rw [← add_mul, hab, one_mul]
    linarith
  rw [he] at h
  exact h

lemma d4be_antitoneOn (C : ℝ → ℝ) (S : ℝ) (hC : ConvexOn ℝ Set.univ C) (hmin : ∀ y, C S ≤ C y) :
    AntitoneOn C (Set.Iic S) := by
  intro x hx y hy hxy
  simp only [Set.mem_Iic] at hx hy
  rcases eq_or_lt_of_le hx with h | h
  · have : y = S := le_antisymm hy (h ▸ hxy)
    rw [this, h]
  · set t := (S - y) / (S - x) with ht
    have hSx : 0 < S - x := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hSx.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hSx]; linarith
    have hcomb : t * x + (1 - t) * S = y := by
      rw [ht]; field_simp; ring
    have h2 := hC.2 (Set.mem_univ x) (Set.mem_univ S) ht0 (by linarith) (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul] at h2
    rw [hcomb] at h2
    have h3 := hmin x
    nlinarith

lemma d4be_min_convex (C : ℝ → ℝ) (S : ℝ) (hC : ConvexOn ℝ Set.univ C) (hmin : ∀ y, C S ≤ C y) :
    ConvexOn ℝ Set.univ (fun t => C (min S t)) := by
  have hanti := d4be_antitoneOn C S hC hmin
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hp : min S x ≤ S := min_le_left _ _
  have hq : min S y ≤ S := min_le_left _ _
  have hr1 : a * min S x + b * min S y ≤ a * x + b * y := by
    have := mul_le_mul_of_nonneg_left (min_le_right S x) ha
    have := mul_le_mul_of_nonneg_left (min_le_right S y) hb
    linarith
  have hr2 : a * min S x + b * min S y ≤ S := by
    have := mul_le_mul_of_nonneg_left hp ha
    have := mul_le_mul_of_nonneg_left hq hb
    have hS : a * S + b * S = S := by rw [← add_mul, hab, one_mul]
    linarith
  have hr : a * min S x + b * min S y ≤ min S (a * x + b * y) := le_min hr2 hr1
  have h1 : C (min S (a * x + b * y)) ≤ C (a * min S x + b * min S y) :=
    hanti (Set.mem_Iic.2 hr2) (Set.mem_Iic.2 (min_le_left _ _)) hr
  have h2 := hC.2 (Set.mem_univ (min S x)) (Set.mem_univ (min S y)) ha hb hab
  simp only [smul_eq_mul] at h2
  linarith

open MeasureTheory SupplyChainTheory in
lemma d4be_G_convex_of (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (j : ℕ)
    (hB : ConvexOn ℝ Set.univ (csBar N h p D S (j - 1))) :
    ConvexOn ℝ Set.univ (csG N h p D S j) := by
  obtain ⟨K, hK, hlip⟩ := d4be_hat_lip N h p D S hD j
  have hconv : ConvexOn ℝ Set.univ (csHat N h p D S j) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h2 := hB.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h2 ⊢
    unfold csHat
    have e : h j * (a * x + b * y) = a * (h j * x) + b * (h j * y) := by ring
    nlinarith
  have hint : ∀ y, Integrable (fun u => csHat N h p D S j (y - u)) (D j) :=
    fun y => d4be_int _ K hK hlip (D j) (hD j) y
  exact d4be_G_conv (csHat N h p D S j) hconv (D j) hint

open MeasureTheory SupplyChainTheory in
lemma d4be_bar_convex (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j))
    (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (hS : CSSequential N h p D S) :
    ∀ k, k ≤ N → ConvexOn ℝ Set.univ (csBar N h p D S k) := by
  intro k
  induction k with
  | zero =>
    intro _
    have hc : 0 ≤ p + localHolding N h 1 := by
      unfold localHolding
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.Icc 1 N) => hh i)
      linarith
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    show (p + localHolding N h 1) * max (-(a * x + b * y)) 0
      ≤ a * ((p + localHolding N h 1) * max (-x) 0) + b * ((p + localHolding N h 1) * max (-y) 0)
    have hm : max (-(a * x + b * y)) 0 ≤ a * max (-x) 0 + b * max (-y) 0 := by
      have h2 : a * (-x) ≤ a * max (-x) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
      have h3 : b * (-y) ≤ b * max (-y) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hb
      have h4 : 0 ≤ a * max (-x) 0 := mul_nonneg ha (le_max_right _ _)
      have h5 : 0 ≤ b * max (-y) 0 := mul_nonneg hb (le_max_right _ _)
      exact max_le (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left hm hc
    nlinarith
  | succ k ih =>
    intro hk
    have hB := ih (by omega)
    have hG : ConvexOn ℝ Set.univ (csG N h p D S (k + 1)) :=
      d4be_G_convex_of N h p D S hD (k + 1) (by simpa using hB)
    have hmin : ∀ y, csG N h p D S (k + 1) (S (k + 1)) ≤ csG N h p D S (k + 1) y :=
      hS (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
    have e : csBar N h p D S (k + 1) = fun t => csG N h p D S (k + 1) (min (S (k + 1)) t) := by
      funext t
      rfl
    rw [e]
    exact d4be_min_convex _ _ hG hmin

open MeasureTheory SupplyChainTheory in
theorem solution (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ) (S : ℕ → ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (hS : CSSequential N h p D S) (j : ℕ) (hj : j ≤ N) :
    ConvexOn ℝ Set.univ (csG N h p D S j) := by
  exact d4be_G_convex_of N h p D S hD j
    (d4be_bar_convex N h p D S hD hh hp hS (j - 1) (by omega))
