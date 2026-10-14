-- Prove2me | solution 1 for SSDConstraint.Optimality.expectedUtility_ge_of_dominance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:43:07.990763+00:00
-- url     : https://prove2.me/submissions/c36c1f45-5fbb-44f0-845d-4a78d21e3532

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem

set_option autoImplicit false

open MeasureTheory Set

/-! ec24e124: SSD constraint (3.2) on [a,b] implies E u(Y) ≤ E u(X) for u ∈ U1 a b.
Proof: for a < b, piecewise-linear interpolation of u on an n-grid of [a,b] is a nonnegative
combination of hinges (η_i - t)₊ (plus a constant), so its expectation is ordered by (3.2);
the interpolation error lies in [0, c(b-a)/n]; let n → ∞. -/

noncomputable def ec24_grid (a h : ℝ) (i : ℕ) : ℝ := a + (i : ℝ) * h

noncomputable def ec24_slope (u : ℝ → ℝ) (a h c : ℝ) : ℕ → ℝ
  | 0 => c
  | i + 1 => (u (ec24_grid a h (i + 1)) - u (ec24_grid a h i)) / h

noncomputable def ec24_K (u : ℝ → ℝ) (a h c : ℝ) (n : ℕ) : ℝ :=
  u a + ∑ i ∈ Finset.range n,
    ec24_slope u a h c (i + 1) * (ec24_grid a h (i + 1) - ec24_grid a h i)

noncomputable def ec24_I (u : ℝ → ℝ) (a h c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ec24_K u a h c n
    - ∑ i ∈ Finset.range n,
        (ec24_slope u a h c i - ec24_slope u a h c (i + 1)) * max (ec24_grid a h i - t) 0
    - ec24_slope u a h c n * max (ec24_grid a h n - t) 0

lemma ec24_grid_succ (a h : ℝ) (i : ℕ) : ec24_grid a h (i + 1) = ec24_grid a h i + h := by
  simp only [ec24_grid]; push_cast; ring

lemma ec24_grid_zero (a h : ℝ) : ec24_grid a h 0 = a := by simp [ec24_grid]

lemma ec24_grid_mono {a h : ℝ} (hh : 0 ≤ h) : Monotone (ec24_grid a h) :=
  monotone_nat_of_le_succ fun i => by rw [ec24_grid_succ]; linarith

lemma ec24_clamp_hinge {p q : ℝ} (hpq : p ≤ q) (t : ℝ) :
    max p (min t q) - p = (q - p) - max (q - t) 0 + max (p - t) 0 := by
  rcases le_total t p with h | h
  · rw [min_eq_left (h.trans hpq), max_eq_left h, max_eq_left (by linarith : (0:ℝ) ≤ q - t),
      max_eq_left (by linarith : (0:ℝ) ≤ p - t)]; ring
  · rcases le_total t q with h' | h'
    · rw [min_eq_left h', max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ q - t),
        max_eq_right (by linarith : p - t ≤ 0)]; ring
    · rw [min_eq_right h', max_eq_right hpq, max_eq_right (by linarith : q - t ≤ 0),
        max_eq_right (by linarith : p - t ≤ 0)]; ring

lemma ec24_abel (s d : ℕ → ℝ) (n : ℕ) :
    -(s 0 * d 0) + ∑ i ∈ Finset.range n, s (i + 1) * (d i - d (i + 1)) =
      -(∑ i ∈ Finset.range n, (s i - s (i + 1)) * d i) - s n * d n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ]; linear_combination ih

lemma ec24_telescope (g : ℝ → ℝ) (η : ℕ → ℝ) (hη : Monotone η) (t : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (g (max (η i) (min t (η (i + 1)))) - g (η i)) =
      g (max (η 0) (min t (η n))) - g (η 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases le_total t (η n) with h | h
    · have e1 : min t (η n) = t := min_eq_left h
      have e2 : min t (η (n + 1)) = t := min_eq_left (h.trans (hη n.le_succ))
      have e3 : max (η n) t = η n := max_eq_left h
      rw [e1, e2, e3]; ring
    · have e1 : min t (η n) = η n := min_eq_right h
      have e3 : max (η 0) (η n) = η n := max_eq_right (hη (Nat.zero_le n))
      have e4 : max (η n) (min t (η (n + 1))) = min t (η (n + 1)) :=
        max_eq_right (le_min h (hη n.le_succ))
      have e5 : max (η 0) (min t (η (n + 1))) = min t (η (n + 1)) :=
        max_eq_right (le_min ((hη (Nat.zero_le n)).trans h) (hη (Nat.zero_le _)))
      rw [e1, e3, e4, e5]; ring

lemma ec24_sum_le (η : ℕ → ℝ) (hη : Monotone η) (t M : ℝ) (hM : 0 ≤ M) (e : ℕ → ℝ)
    (heM : ∀ i, e i ≤ M) (hlo : ∀ i, t ≤ η i → e i = 0)
    (hhi : ∀ i, η (i + 1) ≤ t → e i = 0) (n : ℕ) : ∑ i ∈ Finset.range n, e i ≤ M := by
  induction n with
  | zero => simpa using hM
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases le_total t (η n) with h | h
    · rw [hlo n h]; linarith
    · have hz : ∑ i ∈ Finset.range n, e i = 0 := Finset.sum_eq_zero fun i hi =>
        hhi i ((hη (Nat.succ_le_of_lt (Finset.mem_range.1 hi))).trans h)
      rw [hz]; linarith [heM n]

lemma ec24_stepA {u : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hzero : ∀ t, b ≤ t → u t = 0)
    (hlin : ∀ t ≤ a, u t = u a + c * (t - a)) (t : ℝ) :
    u t = u (max a (min t b)) - c * max (a - t) 0 := by
  rcases le_total t a with h | h
  · rw [min_eq_left (h.trans hab), max_eq_left h, max_eq_left (by linarith : (0:ℝ) ≤ a - t),
      hlin t h]; ring
  · rw [max_eq_right (by linarith : a - t ≤ 0)]
    rcases le_total t b with h' | h'
    · rw [min_eq_left h', max_eq_right h]; ring
    · rw [min_eq_right h', max_eq_right hab, hzero t h', hzero b le_rfl]; ring

lemma ec24_mid {u : ℝ → ℝ} (hconc : ConcaveOn ℝ univ u) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    u (x - h) + u (x + h) ≤ 2 * u x := by
  have key := hconc.neg.secant_mono_aux1 (mem_univ (x - h)) (mem_univ (x + h))
    (by linarith : x - h < x) (by linarith : x < x + h)
  simp only [Pi.neg_apply] at key
  by_contra hne
  push_neg at hne
  nlinarith [mul_pos hh (sub_pos.2 hne)]

lemma ec24_slope_anti {u : ℝ → ℝ} (hconc : ConcaveOn ℝ univ u) {a h c : ℝ} (hh : 0 < h)
    (hlin : ∀ t ≤ a, u t = u a + c * (t - a)) : Antitone (ec24_slope u a h c) := by
  refine antitone_nat_of_succ_le fun i => ?_
  rcases i with _ | i
  · change (u (ec24_grid a h (0 + 1)) - u (ec24_grid a h 0)) / h ≤ c
    rw [ec24_grid_succ, ec24_grid_zero, div_le_iff₀ hh]
    have h1 := ec24_mid hconc hh a
    have h2 := hlin (a - h) (by linarith)
    linarith
  · change (u (ec24_grid a h (i + 1 + 1)) - u (ec24_grid a h (i + 1))) / h ≤
      (u (ec24_grid a h (i + 1)) - u (ec24_grid a h i)) / h
    rw [ec24_grid_succ a h (i + 1), ec24_grid_succ a h i]
    have h1 := ec24_mid hconc hh (ec24_grid a h i + h)
    rw [add_sub_cancel_right] at h1
    rw [div_le_div_iff_of_pos_right hh]
    linarith

lemma ec24_slope_nonneg {u : ℝ → ℝ} (hmono : Monotone u) {a h c : ℝ} (hc : 0 ≤ c) (hh : 0 < h) :
    ∀ i, 0 ≤ ec24_slope u a h c i
  | 0 => hc
  | i + 1 => by
    change 0 ≤ (u (ec24_grid a h (i + 1)) - u (ec24_grid a h i)) / h
    exact div_nonneg (sub_nonneg.2 (hmono ((ec24_grid_mono hh.le) i.le_succ))) hh.le

lemma ec24_cell {u : ℝ → ℝ} (hconc : ConcaveOn ℝ univ u) (hmono : Monotone u) {p h σ c t : ℝ}
    (hh : 0 < h) (hσ : σ * h = u (p + h) - u p) (hσ0 : 0 ≤ σ) (hσc : σ ≤ c) :
    0 ≤ u (max p (min t (p + h))) - u p - σ * (max p (min t (p + h)) - p) ∧
    u (max p (min t (p + h))) - u p - σ * (max p (min t (p + h)) - p) ≤ c * h ∧
    (t ≤ p → u (max p (min t (p + h))) - u p - σ * (max p (min t (p + h)) - p) = 0) ∧
    (p + h ≤ t → u (max p (min t (p + h))) - u p - σ * (max p (min t (p + h)) - p) = 0) := by
  have hx1 : p ≤ max p (min t (p + h)) := le_max_left _ _
  have hx2 : max p (min t (p + h)) ≤ p + h := max_le (by linarith) (min_le_right _ _)
  refine ⟨?_, ?_, fun ht => ?_, fun ht => ?_⟩
  · rcases eq_or_lt_of_le hx1 with h1 | h1
    · rw [← h1]; simp
    rcases eq_or_lt_of_le hx2 with h2 | h2
    · rw [h2]; linarith
    have key := hconc.neg.secant_mono_aux1 (mem_univ p) (mem_univ (p + h)) h1 h2
    simp only [Pi.neg_apply] at key
    have e1 : σ * h * (max p (min t (p + h)) - p) =
        (u (p + h) - u p) * (max p (min t (p + h)) - p) := by rw [hσ]
    have hkey : 0 ≤ h * (u (max p (min t (p + h))) - u p - σ * (max p (min t (p + h)) - p)) := by
      linarith
    by_contra hne
    push_neg at hne
    have := mul_neg_of_pos_of_neg hh hne
    linarith
  · have h3 : u (max p (min t (p + h))) ≤ u (p + h) := hmono hx2
    have h4 : 0 ≤ σ * (max p (min t (p + h)) - p) := mul_nonneg hσ0 (sub_nonneg.2 hx1)
    have h5 : σ * h ≤ c * h := mul_le_mul_of_nonneg_right hσc hh.le
    linarith
  · have : max p (min t (p + h)) = p := max_eq_left ((min_le_left _ _).trans ht)
    rw [this]; ring
  · have : max p (min t (p + h)) = p + h := by rw [min_eq_right ht, max_eq_right (by linarith)]
    rw [this]; linarith

lemma ec24_pointwise {u : ℝ → ℝ} {a b c h : ℝ} (hconc : ConcaveOn ℝ univ u) (hmono : Monotone u)
    (hzero : ∀ t, b ≤ t → u t = 0) (hc : 0 ≤ c) (hlin : ∀ t ≤ a, u t = u a + c * (t - a))
    (hh : 0 < h) (n : ℕ) (hb : ec24_grid a h n = b) (t : ℝ) :
    0 ≤ u t - ec24_I u a h c n t ∧ u t - ec24_I u a h c n t ≤ c * h := by
  have hmη : Monotone (ec24_grid a h) := ec24_grid_mono hh.le
  have hab : a ≤ b := calc
    a = ec24_grid a h 0 := (ec24_grid_zero a h).symm
    _ ≤ ec24_grid a h n := hmη (Nat.zero_le n)
    _ = b := hb
  have hA := ec24_stepA hab hzero hlin t
  have hB := ec24_telescope u (ec24_grid a h) hmη t n
  rw [ec24_grid_zero, hb] at hB
  have hanti := ec24_slope_anti hconc hh hlin
  have hC : ec24_I u a h c n t = u a - c * max (a - t) 0 + ∑ i ∈ Finset.range n,
      ec24_slope u a h c (i + 1) *
        (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i) := by
    have hcl : ∀ i ∈ Finset.range n, ec24_slope u a h c (i + 1) *
        (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i) =
        ec24_slope u a h c (i + 1) * (ec24_grid a h (i + 1) - ec24_grid a h i) +
        ec24_slope u a h c (i + 1) *
          (max (ec24_grid a h i - t) 0 - max (ec24_grid a h (i + 1) - t) 0) := by
      intro i _; rw [ec24_clamp_hinge (hmη i.le_succ)]; ring
    rw [Finset.sum_congr rfl hcl, Finset.sum_add_distrib]
    have hab' := ec24_abel (ec24_slope u a h c) (fun i => max (ec24_grid a h i - t) 0) n
    beta_reduce at hab'
    rw [ec24_grid_zero] at hab'
    have hs0 : ec24_slope u a h c 0 = c := rfl
    rw [hs0] at hab'
    unfold ec24_I ec24_K
    linarith
  have he : u t - ec24_I u a h c n t = ∑ i ∈ Finset.range n,
      (u (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1)))) - u (ec24_grid a h i) -
        ec24_slope u a h c (i + 1) *
          (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i)) := by
    rw [Finset.sum_sub_distrib, hB, hC]; linarith
  have hcell : ∀ i : ℕ,
      0 ≤ u (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1)))) - u (ec24_grid a h i) -
        ec24_slope u a h c (i + 1) *
          (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i) ∧
      u (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1)))) - u (ec24_grid a h i) -
        ec24_slope u a h c (i + 1) *
          (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i) ≤ c * h ∧
      (t ≤ ec24_grid a h i →
        u (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1)))) - u (ec24_grid a h i) -
        ec24_slope u a h c (i + 1) *
          (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i) = 0) ∧
      (ec24_grid a h (i + 1) ≤ t →
        u (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1)))) - u (ec24_grid a h i) -
        ec24_slope u a h c (i + 1) *
          (max (ec24_grid a h i) (min t (ec24_grid a h (i + 1))) - ec24_grid a h i) = 0) := by
    intro i
    have hσ : ec24_slope u a h c (i + 1) * h = u (ec24_grid a h i + h) - u (ec24_grid a h i) := by
      change (u (ec24_grid a h (i + 1)) - u (ec24_grid a h i)) / h * h = _
      rw [ec24_grid_succ, div_mul_cancel₀ _ hh.ne']
    have hσ0 : 0 ≤ ec24_slope u a h c (i + 1) := ec24_slope_nonneg hmono hc hh (i + 1)
    have hσc : ec24_slope u a h c (i + 1) ≤ c := hanti (Nat.zero_le _)
    rw [ec24_grid_succ]
    exact ec24_cell hconc hmono hh hσ hσ0 hσc
  rw [he]
  refine ⟨Finset.sum_nonneg fun i _ => (hcell i).1, ?_⟩
  exact ec24_sum_le (ec24_grid a h) hmη t (c * h) (mul_nonneg hc hh.le) _
    (fun i => (hcell i).2.1) (fun i => (hcell i).2.2.1) (fun i => (hcell i).2.2.2) n

lemma ec24_integral_I {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℝ → ℝ) (a h c : ℝ) (n : ℕ) (f : Ω → ℝ) (hf : Integrable f P) :
    Integrable (fun ω => ec24_I u a h c n (f ω)) P ∧
    ∫ ω, ec24_I u a h c n (f ω) ∂P = ec24_K u a h c n
      - ∑ i ∈ Finset.range n, (ec24_slope u a h c i - ec24_slope u a h c (i + 1)) *
          ∫ ω, max (ec24_grid a h i - f ω) 0 ∂P
      - ec24_slope u a h c n * ∫ ω, max (ec24_grid a h n - f ω) 0 ∂P := by
  have hH : ∀ η : ℝ, Integrable (fun ω => max (η - f ω) 0) P :=
    fun η => ((integrable_const η).sub hf).pos_part
  have hS : Integrable (fun ω => ∑ i ∈ Finset.range n,
      (ec24_slope u a h c i - ec24_slope u a h c (i + 1)) * max (ec24_grid a h i - f ω) 0) P :=
    integrable_finsetSum _ fun i _ => (hH _).const_mul _
  have hT : Integrable (fun ω => ec24_slope u a h c n * max (ec24_grid a h n - f ω) 0) P :=
    (hH _).const_mul _
  have h1 : Integrable (fun ω => ec24_K u a h c n - ∑ i ∈ Finset.range n,
      (ec24_slope u a h c i - ec24_slope u a h c (i + 1)) * max (ec24_grid a h i - f ω) 0
      - ec24_slope u a h c n * max (ec24_grid a h n - f ω) 0) P :=
    ((integrable_const _).sub hS).sub hT
  have hKS : Integrable (fun ω => ec24_K u a h c n - ∑ i ∈ Finset.range n,
      (ec24_slope u a h c i - ec24_slope u a h c (i + 1)) * max (ec24_grid a h i - f ω) 0) P :=
    (integrable_const _).sub hS
  refine ⟨h1, ?_⟩
  simp only [ec24_I]
  rw [integral_sub hKS hT, integral_sub (integrable_const _) hS,
    integral_finsetSum _ (fun i _ => (hH _).const_mul _), integral_const_mul]
  simp [integral_const_mul]

lemma ec24_int_u {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {u I : ℝ → ℝ} {M : ℝ} (hmono : Monotone u) {f : Ω → ℝ} (hf : Integrable f P)
    (hI : Integrable (fun ω => I (f ω)) P) (hbd : ∀ t, 0 ≤ u t - I t ∧ u t - I t ≤ M) :
    Integrable (fun ω => u (f ω)) P := by
  have hg : Integrable (fun ω => |I (f ω)| + M) P := hI.abs.add (integrable_const M)
  refine Integrable.mono' hg
    ((hmono.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have h1 := hbd (f ω)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (I (f ω))]
  · linarith [le_abs_self (I (f ω))]

lemma ec24_main_n {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {u : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hconc : ConcaveOn ℝ univ u) (hmono : Monotone u)
    (hzero : ∀ t, b ≤ t → u t = 0) (hc : 0 ≤ c) (hlin : ∀ t ≤ a, u t = u a + c * (t - a))
    {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    (hdom : ∀ η ∈ Icc a b, ∫ ω, max (η - X ω) 0 ∂P ≤ ∫ ω, max (η - Y ω) 0 ∂P)
    (n : ℕ) (hn : 0 < n) :
    ∫ ω, u (Y ω) ∂P ≤ ∫ ω, u (X ω) ∂P + c * ((b - a) / n) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.2 hn
  have hh : 0 < (b - a) / n := div_pos (by linarith) hnR
  have hb : ec24_grid a ((b - a) / n) n = b := by
    simp only [ec24_grid]; field_simp; ring
  have hpt := ec24_pointwise hconc hmono hzero hc hlin hh n hb
  obtain ⟨hIX, hEX⟩ := ec24_integral_I P u a ((b - a) / n) c n X hX
  obtain ⟨hIY, hEY⟩ := ec24_integral_I P u a ((b - a) / n) c n Y hY
  have huX := ec24_int_u P hmono hX hIX hpt
  have huY := ec24_int_u P hmono hY hIY hpt
  have hmem : ∀ i, i ≤ n → ec24_grid a ((b - a) / n) i ∈ Icc a b := by
    intro i hi
    constructor
    · simp only [ec24_grid]
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
      linarith
    · exact (ec24_grid_mono hh.le hi).trans_eq hb
  have hanti := ec24_slope_anti (a := a) (c := c) hconc hh hlin
  have h1 : ∫ ω, u (Y ω) ∂P ≤ ∫ ω, ec24_I u a ((b - a) / n) c n (Y ω) ∂P + c * ((b - a) / n) := by
    have hIY' : Integrable (fun ω => ec24_I u a ((b - a) / n) c n (Y ω) + c * ((b - a) / n)) P :=
      hIY.add (integrable_const _)
    have := integral_mono huY hIY' (fun ω => by
      show u (Y ω) ≤ ec24_I u a ((b - a) / n) c n (Y ω) + c * ((b - a) / n)
      linarith [(hpt (Y ω)).2])
    rw [integral_add hIY (integrable_const _)] at this
    simpa using this
  have h2 : ∫ ω, ec24_I u a ((b - a) / n) c n (X ω) ∂P ≤ ∫ ω, u (X ω) ∂P :=
    integral_mono hIX huX (fun ω => by
      show ec24_I u a ((b - a) / n) c n (X ω) ≤ u (X ω)
      linarith [(hpt (X ω)).1])
  have h3 : ∫ ω, ec24_I u a ((b - a) / n) c n (Y ω) ∂P ≤
      ∫ ω, ec24_I u a ((b - a) / n) c n (X ω) ∂P := by
    rw [hEX, hEY]
    have hw := Finset.sum_le_sum (s := Finset.range n) fun i hi =>
      mul_le_mul_of_nonneg_left (hdom _ (hmem i (Finset.mem_range.1 hi).le))
        (sub_nonneg.2 (hanti i.le_succ))
    have hn' := mul_le_mul_of_nonneg_left (hdom _ (hmem n le_rfl))
      (ec24_slope_nonneg (a := a) (h := (b - a) / n) hmono hc hh n)
    linarith
  linarith

lemma ec24_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {u : ℝ → ℝ} {a b c : ℝ} (hconc : ConcaveOn ℝ univ u) (hmono : Monotone u)
    (hzero : ∀ t, b ≤ t → u t = 0) (hc : 0 ≤ c) (hlin : ∀ t ≤ a, u t = u a + c * (t - a))
    {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    (hdom : ∀ η ∈ Icc a b, ∫ ω, max (η - X ω) 0 ∂P ≤ ∫ ω, max (η - Y ω) 0 ∂P) :
    ∫ ω, u (Y ω) ∂P ≤ ∫ ω, u (X ω) ∂P := by
  rcases lt_or_ge a b with hab | hab
  · by_contra hne
    push_neg at hne
    set ε := ∫ ω, u (Y ω) ∂P - ∫ ω, u (X ω) ∂P with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (c * (b - a) / ε)
    have hnR : (0:ℝ) < n :=
      lt_of_le_of_lt (div_nonneg (mul_nonneg hc (by linarith)) hε.le) hn
    have hlt : c * ((b - a) / n) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hnR]; rw [div_lt_iff₀ hε] at hn; linarith
    have := ec24_main_n P hab hconc hmono hzero hc hlin hX hY hdom n (Nat.cast_pos.1 hnR)
    linarith
  · rcases eq_or_lt_of_le hab with hba | hba
    · rw [hba] at hzero hdom
      have hu : ∀ t, u t = -(c * max (a - t) 0) := by
        intro t
        rw [ec24_stepA le_rfl hzero hlin t, hzero (max a (min t a)) (le_max_left _ _)]; ring
      simp only [hu]
      rw [integral_neg, integral_neg, integral_const_mul, integral_const_mul]
      have := hdom a ⟨le_rfl, le_rfl⟩
      nlinarith [mul_le_mul_of_nonneg_left this hc]
    · have hua : u a = 0 := hzero a hba.le
      have hc0 : c = 0 := by
        have h1 := hlin b hba.le
        rw [hzero b le_rfl, hua] at h1
        have h2 : c * (b - a) = 0 := by linarith
        rcases mul_eq_zero.1 h2 with h | h
        · exact h
        · exfalso; linarith
      have hu : ∀ t, u t = 0 := by
        intro t
        rcases le_total b t with h | h
        · exact hzero t h
        · rw [hlin t (h.trans hba.le), hua, hc0]; ring
      simp [hu]

open MeasureTheory SSDConstraint.Optimality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (pr : Problem Ω P) :
    ∀ u ∈ U1 pr.a pr.b, ∀ X : Ω →₁[P] ℝ,
      (∀ η ∈ Set.Icc pr.a pr.b, ∫ ω, max (η - X ω) 0 ∂P ≤ ∫ ω, max (η - pr.Y ω) 0 ∂P) →
      ∫ ω, u (pr.Y ω) ∂P ≤ ∫ ω, u (X ω) ∂P := by
  intro u hu X hdom
  obtain ⟨hconc, hmono, hzero, c, hc, hlin⟩ := hu
  exact ec24_core P hconc hmono hzero hc hlin (L1.integrable_coeFn X) (L1.integrable_coeFn pr.Y)
    hdom
