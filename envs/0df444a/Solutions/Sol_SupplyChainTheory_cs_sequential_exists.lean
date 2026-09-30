-- Prove2me | solution 1 for SupplyChainTheory.cs_sequential_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T17:06:43.328929+00:00
-- url     : https://prove2.me/submissions/c148be37-cebf-450e-84ee-cb250925c510

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

set_option autoImplicit false

lemma b98_cont (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ a b, |F a - F b| ≤ K * |a - b|) :
    Continuous F :=
  (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) (f := F) (fun a b => by
    rw [Real.dist_eq, Real.dist_eq]
    exact hF a b)).continuous

open MeasureTheory in
lemma b98_int (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hid : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun u => F (y - u)) μ := by
  refine Integrable.mono' (g := fun u => |F 0| + K * (|y| + |u|)) ?_ ?_ ?_
  · exact (integrable_const _).add (((integrable_const |y|).add hid.abs).const_mul K)
  · exact ((b98_cont F K hK hF).measurable.comp
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
lemma b98_lip_int (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hid : Integrable (fun x : ℝ => x) μ) (y z : ℝ) :
    |∫ u, F (y - u) ∂μ - ∫ u, F (z - u) ∂μ| ≤ K * |y - z| := by
  have hy := b98_int F K hK hF μ hid y
  have hz := b98_int F K hK hF μ hid z
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
lemma b98_bar_lip (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
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
    have key := b98_lip_int (fun t => h (k + 1) * t + csBar N h p D S k t) (|h (k + 1)| + L)
      (by positivity) hF (D (k + 1)) (hD (k + 1)) (min (S (k + 1)) x) (min (S (k + 1)) y)
    show |∫ d, (h (k + 1) * (min (S (k + 1)) x - d) + csBar N h p D S k (min (S (k + 1)) x - d))
          ∂(D (k + 1))
        - ∫ d, (h (k + 1) * (min (S (k + 1)) y - d) + csBar N h p D S k (min (S (k + 1)) y - d))
          ∂(D (k + 1))| ≤ (|h (k + 1)| + L) * |x - y|
    exact key.trans (mul_le_mul_of_nonneg_left hm (by positivity))

open MeasureTheory SupplyChainTheory in
lemma b98_hat_lip (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, |csHat N h p D S j a - csHat N h p D S j b| ≤ K * |a - b| := by
  obtain ⟨L, hL, hlip⟩ := b98_bar_lip N h p D S hD (j - 1)
  refine ⟨|h j| + L, by positivity, fun a b => ?_⟩
  unfold csHat
  have e : h j * a + csBar N h p D S (j - 1) a - (h j * b + csBar N h p D S (j - 1) b)
      = h j * (a - b) + (csBar N h p D S (j - 1) a - csBar N h p D S (j - 1) b) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, add_mul]
  exact add_le_add le_rfl (hlip a b)


open MeasureTheory in
lemma b98_int_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) (F : ℝ → ℝ)
    (hFi : ∀ y, Integrable (fun u => F (y - u)) μ) (a b : ℝ) (hF : ∀ x, a * x - b ≤ F x)
    (y : ℝ) : a * y - a * (∫ u, u ∂μ) - b ≤ ∫ u, F (y - u) ∂μ := by
  have hi : Integrable (fun u : ℝ => (a * y - b) - a * u) μ :=
    (integrable_const _).sub (hid.const_mul a)
  have e : ∫ u, ((a * y - b) - a * u) ∂μ = a * y - a * (∫ u, u ∂μ) - b := by
    rw [integral_sub (integrable_const _) (hid.const_mul a), integral_const, integral_const_mul,
      probReal_univ, one_smul]
    ring
  rw [← e]
  apply integral_mono hi (hFi y)
  intro u
  have := hF (y - u)
  show (a * y - b) - a * u ≤ F (y - u)
  linarith [show a * (y - u) = a * y - a * u by ring]

open Filter Topology in
lemma b98_exists_min (f : ℝ → ℝ) (hc : Continuous f) (a b c1 c2 : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∀ y, a * y - c1 ≤ f y) (h2 : ∀ y, -b * y - c2 ≤ f y) : ∃ x, ∀ y, f x ≤ f y := by
  apply hc.exists_forall_le
  have hm : 0 < min a b := lt_min ha hb
  have hlow : ∀ y : ℝ, min a b * ‖y‖ + (-(|c1| + |c2|)) ≤ f y := by
    intro y
    rw [Real.norm_eq_abs]
    have hma : min a b ≤ a := min_le_left _ _
    have hmb : min a b ≤ b := min_le_right _ _
    have hc1 := le_abs_self c1
    have hc2 := le_abs_self c2
    have hc1' := abs_nonneg c1
    have hc2' := abs_nonneg c2
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      have := mul_le_mul_of_nonneg_right hma hy
      linarith [h1 y]
    · rw [abs_of_neg hy]
      have := mul_le_mul_of_nonneg_right hmb (le_of_lt (neg_pos.2 hy))
      linarith [h2 y]
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop hm)

open MeasureTheory SupplyChainTheory in
lemma b98_localHolding_split (N : ℕ) (h : ℕ → ℝ) (k : ℕ) (hk : k + 1 ≤ N) :
    localHolding N h (k + 1) = h (k + 1) + localHolding N h (k + 1 + 1) := by
  unfold localHolding
  rw [Finset.Icc_eq_cons_Ioc hk, Finset.sum_cons, Finset.Icc_add_one_left_eq_Ioc]

open MeasureTheory SupplyChainTheory in
lemma b98_localHolding_nonneg (N : ℕ) (h : ℕ → ℝ) (hh : ∀ j, 0 < h j) (k : ℕ) :
    0 ≤ localHolding N h k := by
  unfold localHolding
  exact Finset.sum_nonneg (fun i _ => (hh i).le)

open MeasureTheory SupplyChainTheory in
lemma b98_G_cont (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (j : ℕ) :
    Continuous (csG N h p D S j) := by
  obtain ⟨K, hK, hlip⟩ := b98_hat_lip N h p D S hD j
  exact b98_cont _ K hK (fun a b => b98_lip_int _ K hK hlip (D j) (hD j) a b)

open MeasureTheory SupplyChainTheory in
lemma b98_G_lower (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j))
    (k : ℕ) (hk : k + 1 ≤ N) (B : ℝ)
    (hB : ∀ x, -B ≤ csBar N h p D S k x ∧
      -(p + localHolding N h (k + 1)) * x - B ≤ csBar N h p D S k x) (y : ℝ) :
    h (k + 1) * y - h (k + 1) * (∫ u, u ∂(D (k + 1))) - B ≤ csG N h p D S (k + 1) y ∧
    -(p + localHolding N h (k + 1 + 1)) * y
      - (-(p + localHolding N h (k + 1 + 1))) * (∫ u, u ∂(D (k + 1))) - B
      ≤ csG N h p D S (k + 1) y := by
  obtain ⟨K, hK, hlip⟩ := b98_hat_lip N h p D S hD (k + 1)
  have hFi : ∀ y, Integrable (fun u => csHat N h p D S (k + 1) (y - u)) (D (k + 1)) :=
    fun y => b98_int _ K hK hlip (D (k + 1)) (hD (k + 1)) y
  have hsplit := b98_localHolding_split N h k hk
  have ehat : ∀ x, csHat N h p D S (k + 1) x = h (k + 1) * x + csBar N h p D S k x := by
    intro x
    rfl
  constructor
  · apply b98_int_lower (D (k + 1)) (hD (k + 1)) _ hFi
    intro x
    rw [ehat]
    linarith [(hB x).1]
  · apply b98_int_lower (D (k + 1)) (hD (k + 1)) _ hFi
    intro x
    rw [ehat]
    have := (hB x).2
    rw [hsplit] at this
    linarith

open MeasureTheory SupplyChainTheory in
lemma b98_inv (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j))
    (hh : ∀ j, 0 < h j) (hp : 0 < p) :
    ∀ k, k ≤ N → ∃ B : ℝ, ∀ x, -B ≤ csBar N h p D S k x ∧
      -(p + localHolding N h (k + 1)) * x - B ≤ csBar N h p D S k x := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, fun x => ?_⟩
    have hc : 0 ≤ p + localHolding N h 1 := by
      have := b98_localHolding_nonneg N h hh 1
      linarith
    show -0 ≤ (p + localHolding N h 1) * max (-x) 0 ∧
      -(p + localHolding N h (0 + 1)) * x - 0 ≤ (p + localHolding N h 1) * max (-x) 0
    constructor
    · have := mul_nonneg hc (le_max_right (-x) 0)
      linarith
    · have := mul_le_mul_of_nonneg_left (le_max_left (-x) 0) hc
      simp only [zero_add]
      linarith
  | succ k ih =>
    intro hk
    obtain ⟨B, hB⟩ := ih (by omega)
    have hlow := b98_G_lower N h p D S hD k hk B hB
    set E := ∫ u, u ∂(D (k + 1)) with hE
    set a' := p + localHolding N h (k + 1 + 1) with ha'
    have ha'0 : 0 ≤ a' := by
      have := b98_localHolding_nonneg N h hh (k + 1 + 1)
      linarith
    have hhk := hh (k + 1)
    refine ⟨|h (k + 1) * E| + |a' * E| + B, fun x => ?_⟩
    have ebar : csBar N h p D S (k + 1) x = csG N h p D S (k + 1) (min (S (k + 1)) x) := rfl
    rw [ebar]
    set z := min (S (k + 1)) x with hz
    have hzx : z ≤ x := min_le_right _ _
    obtain ⟨l1, l2⟩ := hlow z
    have t1 := neg_abs_le (h (k + 1) * E)
    have t2 := neg_abs_le (a' * E)
    have t3 := abs_nonneg (h (k + 1) * E)
    have t4 := abs_nonneg (a' * E)
    constructor
    · rcases le_or_gt 0 z with hz0 | hz0
      · have := mul_nonneg hhk.le hz0
        nlinarith
      · have := mul_nonneg ha'0 (le_of_lt (neg_pos.2 hz0))
        nlinarith
    · have := mul_le_mul_of_nonneg_left hzx ha'0
      nlinarith

open MeasureTheory SupplyChainTheory in
lemma b98_exists_minG (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [∀ j, IsProbabilityMeasure (D j)] (hD : ∀ j, Integrable (fun x : ℝ => x) (D j))
    (hh : ∀ j, 0 < h j) (hp : 0 < p) (n : ℕ) (hn : n + 1 ≤ N) :
    ∃ x, ∀ y, csG N h p D S (n + 1) x ≤ csG N h p D S (n + 1) y := by
  obtain ⟨B, hB⟩ := b98_inv N h p D S hD hh hp n (by omega)
  have hlow := b98_G_lower N h p D S hD n hn B hB
  have ha' : 0 < p + localHolding N h (n + 1 + 1) := by
    have := b98_localHolding_nonneg N h hh (n + 1 + 1)
    linarith
  exact b98_exists_min _ (b98_G_cont N h p D S hD (n + 1)) (h (n + 1))
    (p + localHolding N h (n + 1 + 1)) (h (n + 1) * (∫ u, u ∂(D (n + 1))) + B)
    ((-(p + localHolding N h (n + 1 + 1))) * (∫ u, u ∂(D (n + 1))) + B) (hh (n + 1)) ha'
    (fun y => by have := (hlow y).1; linarith) (fun y => by have := (hlow y).2; linarith)

open MeasureTheory SupplyChainTheory in
lemma b98_bar_congr (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S S' : ℕ → ℝ) :
    ∀ k, (∀ i, i ≤ k → S i = S' i) → csBar N h p D S k = csBar N h p D S' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hS
    have e1 := hS (k + 1) le_rfl
    have e2 := ih (fun i hi => hS i (by omega))
    funext x
    show ∫ d, (h (k + 1) * (min (S (k + 1)) x - d) + csBar N h p D S k (min (S (k + 1)) x - d))
        ∂(D (k + 1))
      = ∫ d, (h (k + 1) * (min (S' (k + 1)) x - d) + csBar N h p D S' k (min (S' (k + 1)) x - d))
        ∂(D (k + 1))
    rw [e1, e2]

open MeasureTheory SupplyChainTheory in
lemma b98_G_congr (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S S' : ℕ → ℝ) (j : ℕ)
    (hS : ∀ i, i ≤ j - 1 → S i = S' i) : csG N h p D S j = csG N h p D S' j := by
  funext y
  unfold csG csHat
  rw [b98_bar_congr N h p D S S' (j - 1) hS]

open MeasureTheory SupplyChainTheory in
theorem solution (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 < h j) (hp : 0 < p) :
    ∃ S : ℕ → ℝ, CSSequential N h p D S := by
  have key : ∀ n, n ≤ N → ∃ S : ℕ → ℝ, ∀ j ∈ Finset.Icc 1 n, ∀ y,
      csG N h p D S j (S j) ≤ csG N h p D S j y := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun _ => 0, fun j hj y => ?_⟩
      simp only [Finset.mem_Icc] at hj
      omega
    | succ n ih =>
      intro hn
      obtain ⟨S, hS⟩ := ih (by omega)
      obtain ⟨y0, hy0⟩ := b98_exists_minG N h p D S hD hh hp n hn
      refine ⟨Function.update S (n + 1) y0, fun j hj y => ?_⟩
      simp only [Finset.mem_Icc] at hj
      have hcong : csG N h p D (Function.update S (n + 1) y0) j = csG N h p D S j := by
        apply b98_G_congr
        intro i hi
        rw [Function.update_of_ne (by omega)]
      rw [hcong]
      rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
      · rw [Function.update_of_ne (by omega)]
        exact hS j (Finset.mem_Icc.2 ⟨hj.1, by omega⟩) y
      · have hj' : j = n + 1 := by omega
        subst hj'
        rw [Function.update_self]
        exact hy0 y
  exact key N le_rfl
