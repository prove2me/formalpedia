-- Prove2me | solution 1 for OWMR.convex_quantile_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:48:10.396917+00:00
-- url     : https://prove2.me/submissions/094058c9-89d5-4520-b3fa-d923210af6cd

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
Lemma D.1 (Convex-Quantile Contraction). Both sides are computed in quantile form: `Y`, `Y^{[t]}`
have the laws of `Q(V)`, `Q(tV)` for `V` uniform on `(0, 1)`, and `Z` is independent of each, so
every expected loss is an iterated integral against the law of `Z` and the uniform law.
* Since `Q` is convex, the gap `D(u) = t Q(u) - Q(tu)` is nondecreasing on `(0, 1)`. At the target
  `Q(t x*)`, `x* = b/(a+b)`, the loss of `Y^{[t]}` exceeds `t` times that of `Y` at any target by at
  most `a ∫_{(0,x*)} D - b ∫_{(x*,1)} D ≤ (a x* - b(1 - x*)) D(x*) = 0`: the mirror contraction.
* The centered variables `Q(tV) - 𝔼Q(tV)` and `t(Q(V) - 𝔼Q(V))` have equal means and a
  nondecreasing difference, so their lower stop-loss transforms are ordered; as the loss is
  `(a + b)(k - X)⁺ - b(k - X)`, this gives `NV(Z + Y^{[t]}) ≤ NV(Z + tY)` (convex order).
* Convexity of the loss in `(target, value)` gives `NV(Z + tY) ≤ (1 - t) NV(Z) + t NV(Z + Y)`, and
  Jensen's inequality in the uniform variable gives `NV(Z) ≤ NV(Z + Y)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace CQC

/-! ### Integrals over subintervals of `(0, 1)` -/

lemma iInt01 {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo 0 1)) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1) : IntervalIntegrable f volume x y := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hxy]
  exact hf.mono_set (Ioo_subset_Ioo hx hy)

lemma setInt_eq_interval (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≤ y) :
    ∫ u in Ioo x y, f u = ∫ u in x..y, f u := by
  rw [intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo]

lemma split01 {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo 0 1)) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ u in Ioo 0 1, f u = (∫ u in Ioo 0 x, f u) + ∫ u in Ioo x 1, f u := by
  rw [setInt_eq_interval f zero_le_one, setInt_eq_interval f hx0, setInt_eq_interval f hx1]
  exact (intervalIntegral.integral_add_adjacent_intervals (iInt01 hf le_rfl hx0 hx1)
    (iInt01 hf hx0 hx1 le_rfl)).symm

lemma const_int (c x y : ℝ) : IntegrableOn (fun _ : ℝ => c) (Ioo x y) :=
  integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp)

/-- Running averages of a nondecreasing function lie below its full average. -/
lemma running_avg01 {e : ℝ → ℝ} (he : MonotoneOn e (Ioo 0 1)) (hint : IntegrableOn e (Ioo 0 1))
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ u in Ioo 0 x, e u ≤ x * ∫ u in Ioo 0 1, e u := by
  rcases hx0.lt_or_eq with hx0 | rfl
  swap; · simp
  rcases hx1.lt_or_eq with hx1 | rfl
  swap; · simp
  have hA : ∫ u in Ioo 0 x, e u ≤ x * e x := by
    have := setIntegral_mono_on (hint.mono_set (Ioo_subset_Ioo le_rfl hx1.le)) (const_int (e x) 0 x)
      measurableSet_Ioo fun u hu => he ⟨hu.1, hu.2.trans hx1⟩ ⟨hx0, hx1⟩ hu.2.le
    rwa [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx0.le, sub_zero] at this
  have hB : (1 - x) * e x ≤ ∫ u in Ioo x 1, e u := by
    have := setIntegral_mono_on (const_int (e x) x 1) (hint.mono_set (Ioo_subset_Ioo hx0.le le_rfl))
      measurableSet_Ioo fun u hu => he ⟨hx0, hx1⟩ ⟨hx0.trans hu.1, hu.2⟩ hu.1.le
    rwa [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx1.le] at this
  rw [split01 hint hx0.le hx1.le]
  nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 1 - x),
    mul_le_mul_of_nonneg_left hB hx0.le]

/-- Gaps of the shortened quantile function are at most `t` times the original gaps. -/
lemma Q_scale01 {Q : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioo 0 1) Q) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    Q (t * v) - Q (t * u) ≤ t * (Q v - Q u) := by
  rcases huv.lt_or_eq with huv | huv
  swap
  · subst huv; simp
  rcases ht1.lt_or_eq with ht1 | ht1
  swap
  · subst ht1; simp
  have htu : t * u ≤ u := by nlinarith
  have htv : t * v ≤ v := by nlinarith
  have htuv : t * u < t * v := mul_lt_mul_of_pos_left huv ht0
  have m_tu : t * u ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos ht0 hu, by linarith⟩
  have m_tv : t * v ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos ht0 (hu.trans huv), by linarith⟩
  have m_u : u ∈ Ioo (0 : ℝ) 1 := ⟨hu, by linarith⟩
  have m_v : v ∈ Ioo (0 : ℝ) 1 := ⟨hu.trans huv, hv⟩
  have s1 := hconv.secant_mono m_tu m_tv m_v htuv.ne' (by linarith) htv
  have s2 := hconv.secant_mono m_v m_tu m_u (by linarith) (by linarith) htu
  have e1 : (Q v - Q (t * u)) / (v - t * u) = (Q (t * u) - Q v) / (t * u - v) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  have e2 : (Q u - Q v) / (u - v) = (Q v - Q u) / (v - u) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  have key : (Q (t * v) - Q (t * u)) / (t * v - t * u) ≤ (Q v - Q u) / (v - u) := by
    calc (Q (t * v) - Q (t * u)) / (t * v - t * u)
        ≤ (Q v - Q (t * u)) / (v - t * u) := s1
      _ = (Q (t * u) - Q v) / (t * u - v) := e1
      _ ≤ (Q u - Q v) / (u - v) := s2
      _ = (Q v - Q u) / (v - u) := e2
  have hvu : 0 < v - u := by linarith
  rw [show t * v - t * u = t * (v - u) by ring, div_le_div_iff₀ (by positivity) hvu] at key
  nlinarith

/-- Lower stop-loss comparison on `(0, 1)`. -/
lemma stoploss01 {X1 X2 : ℝ → ℝ} (h1 : MonotoneOn X1 (Ioo 0 1))
    (hd : MonotoneOn (fun u => X2 u - X1 u) (Ioo 0 1))
    (hi1 : IntegrableOn X1 (Ioo 0 1)) (hi2 : IntegrableOn X2 (Ioo 0 1))
    (hmean : ∫ u in Ioo 0 1, X1 u = ∫ u in Ioo 0 1, X2 u) (k : ℝ) :
    ∫ u in Ioo 0 1, max (k - X1 u) 0 ≤ ∫ u in Ioo 0 1, max (k - X2 u) 0 := by
  classical
  set A := {u | u ∈ Ioo (0 : ℝ) 1 ∧ X1 u < k} with hA
  set xs : ℝ := if A.Nonempty then sSup A else 0 with hxs
  have hAbdd : BddAbove A := ⟨1, fun u hu => hu.1.2.le⟩
  have hxs0 : 0 ≤ xs := by
    rw [hxs]; split_ifs with hne
    · obtain ⟨a, ha⟩ := hne; exact ha.1.1.le.trans (le_csSup hAbdd ha)
    · exact le_rfl
  have hxs1 : xs ≤ 1 := by
    rw [hxs]; split_ifs with hne
    · exact csSup_le hne fun u hu => hu.1.2.le
    · exact zero_le_one
  have hbelow : ∀ u ∈ Ioo 0 xs, X1 u < k := by
    intro u hu
    have hne : A.Nonempty := by
      by_contra hne; rw [hxs, if_neg hne] at hu; exact absurd hu.2 (not_lt.2 hu.1.le)
    rw [hxs, if_pos hne] at hu
    obtain ⟨a, ha, hua⟩ := exists_lt_of_lt_csSup hne hu.2
    exact lt_of_le_of_lt (h1 ⟨hu.1, hua.trans ha.1.2⟩ ha.1 hua.le) ha.2
  have habove : ∀ u ∈ Ioo xs 1, k ≤ X1 u := by
    intro u hu
    by_contra hlt
    have hmem : u ∈ A := ⟨⟨hxs0.trans_lt hu.1, hu.2⟩, lt_of_not_ge hlt⟩
    have hne : A.Nonempty := ⟨u, hmem⟩
    have := le_csSup hAbdd hmem
    rw [hxs, if_pos hne] at hu
    linarith [hu.1]
  have hint1 : IntegrableOn (fun u => max (k - X1 u) 0) (Ioo 0 1) :=
    ((const_int k 0 1).sub hi1).sup (const_int 0 0 1)
  have hint2 : IntegrableOn (fun u => max (k - X2 u) 0) (Ioo 0 1) :=
    ((const_int k 0 1).sub hi2).sup (const_int 0 0 1)
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → Ioo a b ⊆ Ioo 0 1 := fun ha hb u hu =>
    ⟨ha.trans_lt hu.1, hu.2.trans_le hb⟩
  have hL : ∫ u in Ioo 0 1, max (k - X1 u) 0 = ∫ u in Ioo 0 xs, (k - X1 u) := by
    rw [split01 hint1 hxs0 hxs1]
    have e1 : ∫ u in Ioo 0 xs, max (k - X1 u) 0 = ∫ u in Ioo 0 xs, (k - X1 u) :=
      setIntegral_congr_fun measurableSet_Ioo fun u hu => max_eq_left (by linarith [hbelow u hu])
    have e2 : ∫ u in Ioo xs 1, max (k - X1 u) 0 = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        fun u hu => max_eq_right (by linarith [habove u hu])]
      simp
    rw [e1, e2, add_zero]
  have hdiff : ∫ u in Ioo 0 xs, (X2 u - X1 u) ≤ 0 := by
    have hiD : IntegrableOn (fun u => X2 u - X1 u) (Ioo 0 1) := hi2.sub hi1
    have hra := running_avg01 hd hiD hxs0 hxs1
    have htot : ∫ u in Ioo 0 1, (X2 u - X1 u) = 0 := by
      rw [integral_sub hi2 hi1, hmean, sub_self]
    rw [htot, mul_zero] at hra
    exact hra
  have hsplit : ∫ u in Ioo 0 xs, (k - X1 u)
      = (∫ u in Ioo 0 xs, (k - X2 u)) + ∫ u in Ioo 0 xs, (X2 u - X1 u) := by
    have i1 : IntegrableOn (fun u => k - X2 u) (Ioo 0 xs) :=
      ((const_int k 0 1).sub hi2).mono_set (hsub le_rfl hxs1)
    have i2 : IntegrableOn (fun u => X2 u - X1 u) (Ioo 0 xs) :=
      (hi2.sub hi1).mono_set (hsub le_rfl hxs1)
    rw [← integral_add i1 i2]
    congr 1; ext u; ring
  rw [hL, hsplit]
  calc (∫ u in Ioo 0 xs, (k - X2 u)) + ∫ u in Ioo 0 xs, (X2 u - X1 u)
      ≤ ∫ u in Ioo 0 xs, (k - X2 u) := by linarith
    _ ≤ ∫ u in Ioo 0 xs, max (k - X2 u) 0 :=
        setIntegral_mono_on (((const_int k 0 1).sub hi2).mono_set (hsub le_rfl hxs1))
          (hint2.mono_set (hsub le_rfl hxs1)) measurableSet_Ioo fun u _ => le_max_left _ _
    _ ≤ ∫ u in Ioo 0 1, max (k - X2 u) 0 := by
        rw [split01 hint2 hxs0 hxs1]
        have : 0 ≤ ∫ u in Ioo xs 1, max (k - X2 u) 0 :=
          setIntegral_nonneg measurableSet_Ioo fun u _ => le_max_right _ _
        linarith

/-- Mirror contraction in quantile form: for `Q(t ·)`, the target `Q(t x*)` with `x* = b/(a+b)`
costs at most `t` times the cost of any target for `Q`. -/
lemma mirror01 {Q : ℝ → ℝ} (hmono : MonotoneOn Q (Ioo 0 1)) (hconv : ConvexOn ℝ (Ioo 0 1) Q)
    {t a b : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hint : IntegrableOn Q (Ioo 0 1)) (hintt : IntegrableOn (fun u => Q (t * u)) (Ioo 0 1))
    (c' : ℝ) :
    ∫ u in Ioo 0 1, (a * max (Q (t * (b / (a + b))) - Q (t * u)) 0
        + b * max (Q (t * u) - Q (t * (b / (a + b)))) 0)
      ≤ t * ∫ u in Ioo 0 1, (a * max (c' - Q u) 0 + b * max (Q u - c') 0) := by
  set x := b / (a + b) with hx
  have hab : 0 < a + b := by linarith
  have hx0 : 0 < x := div_pos hb hab
  have hx1 : x < 1 := by rw [hx, div_lt_one hab]; linarith
  have hax : a * x = b * (1 - x) := by rw [hx]; field_simp; ring
  set c := Q (t * x) with hc
  have hmt : ∀ u ∈ Ioo (0 : ℝ) 1, t * u ∈ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨mul_pos ht0 hu.1, by nlinarith [hu.1, hu.2]⟩
  have hLint : ∀ {f : ℝ → ℝ}, IntegrableOn f (Ioo 0 1) → ∀ c0 : ℝ,
      IntegrableOn (fun u => a * max (c0 - f u) 0 + b * max (f u - c0) 0) (Ioo 0 1) :=
    fun hf c0 => ((((const_int c0 0 1).sub hf).sup (const_int 0 0 1)).const_mul a).add
      (((hf.sub (const_int c0 0 1)).sup (const_int 0 0 1)).const_mul b)
  have hs0 : Ioo 0 x ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo le_rfl hx1.le
  have hs1 : Ioo x 1 ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo hx0.le le_rfl
  -- the left side in closed form
  have hL : ∫ u in Ioo 0 1, (a * max (c - Q (t * u)) 0 + b * max (Q (t * u) - c) 0)
      = a * (x * c - ∫ u in Ioo 0 x, Q (t * u)) + b * ((∫ u in Ioo x 1, Q (t * u)) - (1 - x) * c) := by
    rw [split01 (hLint hintt c) hx0.le hx1.le]
    have e1 : ∫ u in Ioo 0 x, (a * max (c - Q (t * u)) 0 + b * max (Q (t * u) - c) 0)
        = ∫ u in Ioo 0 x, a * (c - Q (t * u)) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have : Q (t * u) ≤ c := hmono (hmt u (hs0 hu)) (hmt x ⟨hx0, hx1⟩)
        (mul_le_mul_of_nonneg_left hu.2.le ht0.le)
      show a * max (c - Q (t * u)) 0 + b * max (Q (t * u) - c) 0 = a * (c - Q (t * u))
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have e2 : ∫ u in Ioo x 1, (a * max (c - Q (t * u)) 0 + b * max (Q (t * u) - c) 0)
        = ∫ u in Ioo x 1, b * (Q (t * u) - c) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have : c ≤ Q (t * u) := hmono (hmt x ⟨hx0, hx1⟩) (hmt u (hs1 hu))
        (mul_le_mul_of_nonneg_left hu.1.le ht0.le)
      show a * max (c - Q (t * u)) 0 + b * max (Q (t * u) - c) 0 = b * (Q (t * u) - c)
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    rw [e1, e2, integral_const_mul, integral_const_mul,
      integral_sub (const_int c 0 x) (hintt.mono_set hs0),
      integral_sub (hintt.mono_set hs1) (const_int c x 1), setIntegral_const, setIntegral_const,
      smul_eq_mul, smul_eq_mul, Real.volume_real_Ioo_of_le hx0.le, Real.volume_real_Ioo_of_le hx1.le]
    ring
  -- a lower bound for the right side, valid for every target `c'`
  have hR : a * (x * c' - ∫ u in Ioo 0 x, Q u) + b * ((∫ u in Ioo x 1, Q u) - (1 - x) * c')
      ≤ ∫ u in Ioo 0 1, (a * max (c' - Q u) 0 + b * max (Q u - c') 0) := by
    rw [split01 (hLint hint c') hx0.le hx1.le]
    have e1 : a * (x * c' - ∫ u in Ioo 0 x, Q u)
        ≤ ∫ u in Ioo 0 x, (a * max (c' - Q u) 0 + b * max (Q u - c') 0) := by
      have eq1 : ∫ u in Ioo 0 x, a * (c' - Q u) = a * (x * c' - ∫ u in Ioo 0 x, Q u) := by
        rw [integral_const_mul, integral_sub (const_int c' 0 x) (hint.mono_set hs0),
          setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx0.le, sub_zero]
      rw [← eq1]
      refine setIntegral_mono_on (((const_int c' 0 x).sub (hint.mono_set hs0)).const_mul a)
        ((hLint hint c').mono_set hs0) measurableSet_Ioo fun u _ => ?_
      have h1 : 0 ≤ b * max (Q u - c') 0 := mul_nonneg hb.le (le_max_right _ _)
      have h2 : a * (c' - Q u) ≤ a * max (c' - Q u) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le
      linarith
    have e2 : b * ((∫ u in Ioo x 1, Q u) - (1 - x) * c')
        ≤ ∫ u in Ioo x 1, (a * max (c' - Q u) 0 + b * max (Q u - c') 0) := by
      have eq2 : ∫ u in Ioo x 1, b * (Q u - c') = b * ((∫ u in Ioo x 1, Q u) - (1 - x) * c') := by
        rw [integral_const_mul, integral_sub (hint.mono_set hs1) (const_int c' x 1),
          setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx1.le]
      rw [← eq2]
      refine setIntegral_mono_on (((hint.mono_set hs1).sub (const_int c' x 1)).const_mul b)
        ((hLint hint c').mono_set hs1) measurableSet_Ioo fun u _ => ?_
      have h1 : 0 ≤ a * max (c' - Q u) 0 := mul_nonneg ha.le (le_max_right _ _)
      have h2 : b * (Q u - c') ≤ b * max (Q u - c') 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le
      linarith
    linarith
  -- the gap function `D(u) = t Q(u) - Q(t u)` is nondecreasing
  set D : ℝ → ℝ := fun u => t * Q u - Q (t * u) with hD
  have hDmono : MonotoneOn D (Ioo 0 1) := by
    intro u hu v hv huv
    have := Q_scale01 hconv ht0 ht1 hu.1 huv hv.2
    simp only [hD]; linarith
  have hDint : IntegrableOn D (Ioo 0 1) := (hint.const_mul t).sub hintt
  have hD1 : ∫ u in Ioo 0 x, D u ≤ x * D x := by
    have := setIntegral_mono_on (hDint.mono_set hs0) (const_int (D x) 0 x) measurableSet_Ioo
      fun u hu => hDmono (hs0 hu) ⟨hx0, hx1⟩ hu.2.le
    rwa [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx0.le, sub_zero] at this
  have hD2 : (1 - x) * D x ≤ ∫ u in Ioo x 1, D u := by
    have := setIntegral_mono_on (const_int (D x) x 1) (hDint.mono_set hs1) measurableSet_Ioo
      fun u hu => hDmono ⟨hx0, hx1⟩ (hs1 hu) hu.1.le
    rwa [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx1.le] at this
  have hDs1 : ∫ u in Ioo 0 x, D u = t * (∫ u in Ioo 0 x, Q u) - ∫ u in Ioo 0 x, Q (t * u) := by
    rw [integral_sub (IntegrableOn.mono_set (hint.const_mul t) hs0) (hintt.mono_set hs0),
      integral_const_mul]
  have hDs2 : ∫ u in Ioo x 1, D u = t * (∫ u in Ioo x 1, Q u) - ∫ u in Ioo x 1, Q (t * u) := by
    rw [integral_sub (IntegrableOn.mono_set (hint.const_mul t) hs1) (hintt.mono_set hs1),
      integral_const_mul]
  rw [hL]
  have key : a * ∫ u in Ioo 0 x, D u ≤ b * ∫ u in Ioo x 1, D u := by
    have h1 := mul_le_mul_of_nonneg_left hD1 ha.le
    have h2 := mul_le_mul_of_nonneg_left hD2 hb.le
    have h3 : a * (x * D x) = b * ((1 - x) * D x) := by rw [← mul_assoc, hax, mul_assoc]
    linarith
  rw [hDs1, hDs2] at key
  have hcc : a * (x * c) = b * ((1 - x) * c) := by rw [← mul_assoc, hax, mul_assoc]
  have hcc' : t * (a * (x * c')) = t * (b * ((1 - x) * c')) := by
    rw [← mul_assoc a, hax, mul_assoc]
  have htR := mul_le_mul_of_nonneg_left hR ht0.le
  nlinarith

/-- The loss `a (z - y)⁺ + b (y - z)⁺` integrated against two quantile-form variables with equal
means is ordered by their lower stop-loss transforms. -/
lemma loss_cmp {X1 X2 : ℝ → ℝ} (hi1 : IntegrableOn X1 (Ioo 0 1)) (hi2 : IntegrableOn X2 (Ioo 0 1))
    (hmean : ∫ u in Ioo 0 1, X1 u = ∫ u in Ioo 0 1, X2 u)
    (hsl : ∀ k, ∫ u in Ioo 0 1, max (k - X1 u) 0 ≤ ∫ u in Ioo 0 1, max (k - X2 u) 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z c : ℝ) :
    ∫ u in Ioo 0 1, (a * max (z - (c + X1 u)) 0 + b * max ((c + X1 u) - z) 0)
      ≤ ∫ u in Ioo 0 1, (a * max (z - (c + X2 u)) 0 + b * max ((c + X2 u) - z) 0) := by
  have hvol : (volume (Ioo (0 : ℝ) 1)).toReal = 1 := by simp [Real.volume_Ioo]
  have e : ∀ {X : ℝ → ℝ}, IntegrableOn X (Ioo 0 1) →
      ∫ u in Ioo 0 1, (a * max (z - (c + X u)) 0 + b * max ((c + X u) - z) 0)
        = (a + b) * (∫ u in Ioo 0 1, max (z - c - X u) 0) - b * ((z - c) - ∫ u in Ioo 0 1, X u) := by
    intro X hX
    have hpt : ∀ u, a * max (z - (c + X u)) 0 + b * max ((c + X u) - z) 0
        = (a + b) * max (z - c - X u) 0 - b * ((z - c) - X u) := fun u => by
      rcases le_total (z - c - X u) 0 with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_right h]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_left h]; ring
    simp_rw [hpt]
    have hlin : IntegrableOn (fun u => z - c - X u) (Ioo 0 1) := (const_int (z - c) 0 1).sub hX
    have hi : IntegrableOn (fun u => max (z - c - X u) 0) (Ioo 0 1) :=
      hlin.sup (const_int 0 0 1)
    rw [integral_sub (hi.const_mul (a + b)) (hlin.const_mul b),
      integral_const_mul, integral_const_mul, integral_sub (const_int (z - c) 0 1) hX,
      setIntegral_const, smul_eq_mul, measureReal_def, hvol, one_mul]
  rw [e hi1, e hi2, hmean]
  have := hsl (z - c)
  have hab : 0 ≤ a + b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hab]

/-! ### The loss and the transfer to quantile form -/

lemma loss_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z y : ℝ) :
    0 ≤ a * max (z - y) 0 + b * max (y - z) 0 :=
  add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

lemma loss_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z y : ℝ) :
    a * max (z - y) 0 + b * max (y - z) 0 ≤ (a + b) * (|z| + |y|) := by
  have h1 : max (z - y) 0 ≤ |z| + |y| :=
    max_le (by linarith [le_abs_self z, neg_abs_le y]) (by positivity)
  have h2 : max (y - z) 0 ≤ |z| + |y| :=
    max_le (by linarith [le_abs_self y, neg_abs_le z]) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma loss_cont (a b z : ℝ) : Continuous fun y : ℝ => a * max (z - y) 0 + b * max (y - z) 0 := by
  fun_prop

lemma loss_int {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {X : α → ℝ}
    (hX : Integrable X μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ) :
    Integrable (fun x => a * max (z - X x) 0 + b * max (X x - z) 0) μ := by
  refine Integrable.mono' (g := fun x => (a + b) * (|z| + |X x|))
    (((integrable_const |z|).add hX.abs).const_mul (a + b))
    ((loss_cont a b z).comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (loss_nonneg ha hb z (X x))]
  exact loss_le ha hb z (X x)

lemma loss_prod_int {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : Integrable (fun y : ℝ => y) ν) {X : ℝ → ℝ} (hX : Integrable X μ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ) :
    Integrable (fun p : ℝ × ℝ => a * max (z - (p.1 + X p.2)) 0 + b * max ((p.1 + X p.2) - z) 0)
      (ν.prod μ) := by
  have hm : AEMeasurable (fun p : ℝ × ℝ => p.1 + X p.2) (ν.prod μ) :=
    measurable_fst.aemeasurable.add hX.aemeasurable.comp_snd
  refine Integrable.mono' (g := fun p : ℝ × ℝ => (a + b) * (|z| + (|p.1| + |X p.2|))) ?_
    ((loss_cont a b z).measurable.comp_aemeasurable hm).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  · exact ((integrable_const |z|).add ((hν.abs.comp_fst μ).add (hX.abs.comp_snd ν))).const_mul
      (a + b)
  · rw [Real.norm_eq_abs, abs_of_nonneg (loss_nonneg ha hb z _)]
    refine (loss_le ha hb z _).trans ?_
    have h1 := abs_add_le p.1 (X p.2)
    have hab : 0 ≤ a + b := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hab]

lemma transfer1 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : Ω → ℝ} (hW : Measurable W)
    {μ : Measure ℝ} {R : ℝ → ℝ} (hR : AEMeasurable R μ) (hlaw : P.map W = μ.map R)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    ∫ ω, φ (W ω) ∂P = ∫ u, φ (R u) ∂μ := by
  rw [← integral_map hW.aemeasurable hφ.aestronglyMeasurable, hlaw,
    integral_map hR hφ.aestronglyMeasurable]

lemma transfer2 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z W : Ω → ℝ} (hZ : Measurable Z) (hW : Measurable W) (hZW : IndepFun Z W P)
    (hZi : Integrable Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ] {R : ℝ → ℝ}
    (hR : AEMeasurable R μ) (hRi : Integrable R μ) (hlaw : P.map W = μ.map R)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ) :
    ∫ ω, (a * max (z - (Z ω + W ω)) 0 + b * max ((Z ω + W ω) - z) 0) ∂P
      = ∫ ζ, (∫ u, (a * max (z - (ζ + R u)) 0 + b * max ((ζ + R u) - z) 0) ∂μ) ∂(P.map Z) := by
  have hpair : P.map (fun ω => (Z ω, W ω)) = (P.map Z).prod (μ.map R) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hW.aemeasurable).1 hZW, hlaw]
  have hc : Continuous fun p : ℝ × ℝ =>
      a * max (z - (p.1 + p.2)) 0 + b * max ((p.1 + p.2) - z) 0 := by fun_prop
  have h1 : ∫ ω, (a * max (z - (Z ω + W ω)) 0 + b * max ((Z ω + W ω) - z) 0) ∂P
      = ∫ p, (a * max (z - (p.1 + p.2)) 0 + b * max ((p.1 + p.2) - z) 0)
          ∂(P.map (fun ω => (Z ω, W ω))) :=
    (integral_map (hZ.prodMk hW).aemeasurable hc.aestronglyMeasurable).symm
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ.map R) := Measure.isProbabilityMeasure_map hR
  have hνi : Integrable (fun y : ℝ => y) (P.map Z) :=
    (integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).2 hZi
  have hRi' : Integrable (fun y : ℝ => y) (μ.map R) :=
    (integrable_map_measure aestronglyMeasurable_id hR).2 hRi
  have hint : Integrable (fun p : ℝ × ℝ =>
      a * max (z - (p.1 + p.2)) 0 + b * max ((p.1 + p.2) - z) 0) ((P.map Z).prod (μ.map R)) :=
    loss_prod_int (X := fun y => y) hνi hRi' ha hb z
  rw [h1, hpair, integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  exact integral_map hR (by fun_prop : Continuous fun y : ℝ =>
    a * max (z - (ζ + y)) 0 + b * max ((ζ + y) - z) 0).aestronglyMeasurable

end CQC

open CQC in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℝ → ℝ) (hQm : MonotoneOn Q (Set.Ioo 0 1))
    (hQc : ConvexOn ℝ (Set.Ioo 0 1) Q) (Y Yt Z : Ω → ℝ) (hY : Measurable Y)
    (hYt : Measurable Yt) (hZ : Measurable Z) (hYi : Integrable Y P) (hZi : Integrable Z P)
    (t a b : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hYlaw : P.map Y = (volume.restrict (Set.Ioo 0 1)).map Q)
    (hYtlaw : P.map Yt = (volume.restrict (Set.Ioo 0 1)).map (fun u => Q (t * u)))
    (hZY : IndepFun Z Y P) (hZYt : IndepFun Z Yt P) :
    let NV : (Ω → ℝ) → ℝ := fun X =>
      ⨅ z : ℝ, ∫ ω, (a * max (z - X ω) 0 + b * max (X ω - z) 0) ∂P
    NV Yt ≤ t * NV Y ∧
      NV (fun ω => Z ω + Yt ω) ≤ (1 - t) * NV Z + t * NV (fun ω => Z ω + Y ω) ∧
      (1 - t) * NV Z + t * NV (fun ω => Z ω + Y ω) ≤ NV (fun ω => Z ω + Y ω) := by
  intro NV
  have hNV : ∀ X : Ω → ℝ,
      NV X = ⨅ z : ℝ, ∫ ω, (a * max (z - X ω) 0 + b * max (X ω - z) 0) ∂P := fun X => rfl
  have hbdd : ∀ X : Ω → ℝ, BddBelow (Set.range fun z : ℝ =>
      ∫ ω, (a * max (z - X ω) 0 + b * max (X ω - z) 0) ∂P) := fun X =>
    ⟨0, by rintro _ ⟨z, rfl⟩; exact integral_nonneg fun ω => loss_nonneg ha.le hb.le z (X ω)⟩
  have hV : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]; norm_num⟩
  have h1t : 0 ≤ 1 - t := by linarith
  -- the quantile functions
  have hmt : ∀ u ∈ Ioo (0 : ℝ) 1, t * u ∈ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨mul_pos ht0 hu.1, by nlinarith [hu.1, hu.2]⟩
  have hQtm : MonotoneOn (fun u => Q (t * u)) (Ioo 0 1) := fun u hu v hv huv =>
    hQm (hmt u hu) (hmt v hv) (mul_le_mul_of_nonneg_left huv ht0.le)
  have hQae : AEMeasurable Q (volume.restrict (Ioo 0 1)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQm
  have hQtae : AEMeasurable (fun u => Q (t * u)) (volume.restrict (Ioo 0 1)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQtm
  have hQi : Integrable Q (volume.restrict (Ioo 0 1)) := by
    have h1 : Integrable (fun y : ℝ => y) (P.map Y) :=
      (integrable_map_measure aestronglyMeasurable_id hY.aemeasurable).2 hYi
    rw [hYlaw] at h1
    exact (integrable_map_measure aestronglyMeasurable_id hQae).1 h1
  -- `Q` is bounded below on `(0, 1)`, as it is convex and nondecreasing
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, ∀ u ∈ Ioo (0 : ℝ) 1, B0 ≤ Q u := by
    have m12 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have m34 : (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hq : Q (1 / 2) ≤ Q (3 / 4) := hQm m12 m34 (by norm_num)
    refine ⟨Q (1 / 2) - 2 * (Q (3 / 4) - Q (1 / 2)), fun u hu => ?_⟩
    rcases lt_or_ge u (1 / 2) with hu2 | hu2
    · have hs := hQc.slope_mono_adjacent hu m34 hu2 (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      rw [div_le_div_iff₀ (by linarith) (by norm_num)] at hs
      nlinarith [hu.1]
    · have := hQm m12 hu hu2
      linarith
  have hQti : Integrable (fun u => Q (t * u)) (volume.restrict (Ioo 0 1)) := by
    refine Integrable.mono' (g := fun u => |B0| + |Q u|) ((integrable_const _).add hQi.abs)
      hQtae.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_)
    have h1 : B0 ≤ Q (t * u) := hB0 _ (hmt u hu)
    have h2 : Q (t * u) ≤ Q u := hQm (hmt u hu) hu (by nlinarith [hu.1])
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le B0, abs_nonneg (Q u)]
    · linarith [le_abs_self (Q u), abs_nonneg B0]
  -- transfers to quantile form
  have hA1 : ∀ z, ∫ ω, (a * max (z - Y ω) 0 + b * max (Y ω - z) 0) ∂P
      = ∫ u in Ioo 0 1, (a * max (z - Q u) 0 + b * max (Q u - z) 0) :=
    fun z => transfer1 hY hQae hYlaw _ (loss_cont a b z)
  have hA1t : ∀ z, ∫ ω, (a * max (z - Yt ω) 0 + b * max (Yt ω - z) 0) ∂P
      = ∫ u in Ioo 0 1, (a * max (z - Q (t * u)) 0 + b * max (Q (t * u) - z) 0) :=
    fun z => transfer1 hYt hQtae hYtlaw _ (loss_cont a b z)
  have hνp : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hνi : Integrable (fun y : ℝ => y) (P.map Z) :=
    (integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).2 hZi
  have hAZ : ∀ z, ∫ ω, (a * max (z - Z ω) 0 + b * max (Z ω - z) 0) ∂P
      = ∫ ζ, (a * max (z - ζ) 0 + b * max (ζ - z) 0) ∂(P.map Z) := fun z =>
    (integral_map hZ.aemeasurable (loss_cont a b z).aestronglyMeasurable).symm
  have hA2 : ∀ z, ∫ ω, (a * max (z - (Z ω + Y ω)) 0 + b * max ((Z ω + Y ω) - z) 0) ∂P
      = ∫ ζ, (∫ u in Ioo 0 1, (a * max (z - (ζ + Q u)) 0 + b * max ((ζ + Q u) - z) 0))
          ∂(P.map Z) :=
    fun z => transfer2 hZ hY hZY hZi hQae hQi hYlaw ha.le hb.le z
  have hA2t : ∀ z, ∫ ω, (a * max (z - (Z ω + Yt ω)) 0 + b * max ((Z ω + Yt ω) - z) 0) ∂P
      = ∫ ζ, (∫ u in Ioo 0 1, (a * max (z - (ζ + Q (t * u))) 0
          + b * max ((ζ + Q (t * u)) - z) 0)) ∂(P.map Z) :=
    fun z => transfer2 hZ hYt hZYt hZi hQtae hQti hYtlaw ha.le hb.le z
  have hin : ∀ (R : ℝ → ℝ), Integrable R (volume.restrict (Ioo 0 1)) → ∀ z,
      Integrable (fun ζ => ∫ u in Ioo 0 1, (a * max (z - (ζ + R u)) 0
        + b * max ((ζ + R u) - z) 0)) (P.map Z) :=
    fun R hR z => (loss_prod_int hνi hR ha.le hb.le z).integral_prod_left
  -- the means of the quantile functions
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ u in Ioo 0 1, Q u := ⟨_, rfl⟩
  obtain ⟨mt, hmt'⟩ : ∃ mt : ℝ, mt = ∫ u in Ioo 0 1, Q (t * u) := ⟨_, rfl⟩
  -- Jensen: `NV(Z) ≤ NV(Z + Y)`
  have hNVZ : NV Z ≤ NV (fun ω => Z ω + Y ω) := by
    rw [hNV (fun ω => Z ω + Y ω)]
    refine le_ciInf fun z => ?_
    rw [hA2 z]
    have hJ : ∀ ζ : ℝ, a * max (z - (ζ + m)) 0 + b * max ((ζ + m) - z) 0
        ≤ ∫ u in Ioo 0 1, (a * max (z - (ζ + Q u)) 0 + b * max ((ζ + Q u) - z) 0) := by
      intro ζ
      have iζQ : Integrable (fun u => ζ + Q u) (volume.restrict (Ioo 0 1)) :=
        (integrable_const ζ).add hQi
      have i1 : Integrable (fun u => z - (ζ + Q u)) (volume.restrict (Ioo 0 1)) :=
        (integrable_const z).sub iζQ
      have i2 : Integrable (fun u => (ζ + Q u) - z) (volume.restrict (Ioo 0 1)) :=
        iζQ.sub (integrable_const z)
      have e1 : ∫ u in Ioo 0 1, (z - (ζ + Q u)) = z - (ζ + m) := by
        rw [integral_sub (integrable_const z) iζQ, integral_add (integrable_const ζ) hQi, hm]
        simp
      have e2 : ∫ u in Ioo 0 1, ((ζ + Q u) - z) = (ζ + m) - z := by
        rw [integral_sub iζQ (integrable_const z), integral_add (integrable_const ζ) hQi, hm]
        simp
      have j1 : Integrable (fun u => max (z - (ζ + Q u)) 0) (volume.restrict (Ioo 0 1)) :=
        i1.sup (integrable_const 0)
      have j2 : Integrable (fun u => max ((ζ + Q u) - z) 0) (volume.restrict (Ioo 0 1)) :=
        i2.sup (integrable_const 0)
      have k1 : max (z - (ζ + m)) 0 ≤ ∫ u in Ioo 0 1, max (z - (ζ + Q u)) 0 :=
        max_le (e1 ▸ integral_mono i1 j1 fun u => le_max_left _ _)
          (integral_nonneg fun u => le_max_right _ _)
      have k2 : max ((ζ + m) - z) 0 ≤ ∫ u in Ioo 0 1, max ((ζ + Q u) - z) 0 :=
        max_le (e2 ▸ integral_mono i2 j2 fun u => le_max_left _ _)
          (integral_nonneg fun u => le_max_right _ _)
      rw [integral_add (j1.const_mul a) (j2.const_mul b), integral_const_mul, integral_const_mul]
      nlinarith [mul_le_mul_of_nonneg_left k1 ha.le, mul_le_mul_of_nonneg_left k2 hb.le]
    calc NV Z ≤ ∫ ω, (a * max ((z - m) - Z ω) 0 + b * max (Z ω - (z - m)) 0) ∂P :=
          ciInf_le (hbdd Z) (z - m)
      _ = ∫ ζ, (a * max ((z - m) - ζ) 0 + b * max (ζ - (z - m)) 0) ∂(P.map Z) := hAZ (z - m)
      _ = ∫ ζ, (a * max (z - (ζ + m)) 0 + b * max ((ζ + m) - z) 0) ∂(P.map Z) := by
          congr 1; funext ζ
          rw [show z - m - ζ = z - (ζ + m) by ring, show ζ - (z - m) = ζ + m - z by ring]
      _ ≤ _ := integral_mono (loss_int (X := fun ζ => ζ + m) (hνi.add (integrable_const m))
          ha.le hb.le z) (hin Q hQi z) hJ
  refine ⟨?_, ?_, ?_⟩
  · -- the mirror contraction
    rw [hNV, hNV]
    refine (ciInf_le (hbdd Yt) (Q (t * (b / (a + b))))).trans ?_
    rw [Real.mul_iInf_of_nonneg ht0.le]
    refine le_ciInf fun c' => ?_
    rw [hA1t, hA1]
    exact mirror01 hQm hQc ht0 ht1 ha hb hQi hQti c'
  · -- the holding and backlog contraction
    have hX1i : IntegrableOn (fun u => Q (t * u) - mt) (Ioo 0 1) := hQti.sub (integrable_const mt)
    have hX2i : IntegrableOn (fun u => t * Q u - t * m) (Ioo 0 1) :=
      (hQi.const_mul t).sub (integrable_const (t * m))
    have hX1m : MonotoneOn (fun u => Q (t * u) - mt) (Ioo 0 1) := fun u hu v hv huv => by
      have := hQtm hu hv huv
      simp only at this ⊢
      linarith
    have hdm : MonotoneOn (fun u => (t * Q u - t * m) - (Q (t * u) - mt)) (Ioo 0 1) := by
      intro u hu v hv huv
      have := Q_scale01 hQc ht0 ht1 hu.1 huv hv.2
      simp only
      linarith
    have hmean0 : ∫ u in Ioo 0 1, (Q (t * u) - mt) = ∫ u in Ioo 0 1, (t * Q u - t * m) := by
      rw [integral_sub hQti (integrable_const mt),
        integral_sub (hQi.const_mul t) (integrable_const (t * m)), integral_const_mul, ← hm,
        ← hmt']
      simp
    have hsl := stoploss01 hX1m hdm hX1i hX2i hmean0
    have hcmp : ∀ z ζ : ℝ,
        ∫ u in Ioo 0 1, (a * max ((z + mt - t * m) - (ζ + Q (t * u))) 0
          + b * max ((ζ + Q (t * u)) - (z + mt - t * m)) 0)
        ≤ ∫ u in Ioo 0 1, (a * max (z - (ζ + t * Q u)) 0 + b * max ((ζ + t * Q u) - z) 0) := by
      intro z ζ
      have h := loss_cmp hX1i hX2i hmean0 hsl ha hb z (ζ + t * m)
      have e1 : ∀ u, a * max ((z + mt - t * m) - (ζ + Q (t * u))) 0
            + b * max ((ζ + Q (t * u)) - (z + mt - t * m)) 0
          = a * max (z - ((ζ + t * m) + (Q (t * u) - mt))) 0
            + b * max (((ζ + t * m) + (Q (t * u) - mt)) - z) 0 := fun u => by
        rw [show (z + mt - t * m) - (ζ + Q (t * u)) = z - ((ζ + t * m) + (Q (t * u) - mt)) by ring,
          show (ζ + Q (t * u)) - (z + mt - t * m) = ((ζ + t * m) + (Q (t * u) - mt)) - z by ring]
      have e2 : ∀ u, a * max (z - (ζ + t * Q u)) 0 + b * max ((ζ + t * Q u) - z) 0
          = a * max (z - ((ζ + t * m) + (t * Q u - t * m))) 0
            + b * max (((ζ + t * m) + (t * Q u - t * m)) - z) 0 := fun u => by
        rw [show z - (ζ + t * Q u) = z - ((ζ + t * m) + (t * Q u - t * m)) by ring,
          show (ζ + t * Q u) - z = ((ζ + t * m) + (t * Q u - t * m)) - z by ring]
      simp_rw [e1, e2]
      exact h
    have hmix : ∀ z1 z2 ζ y : ℝ,
        a * max (((1 - t) * z1 + t * z2) - (ζ + t * y)) 0
          + b * max ((ζ + t * y) - ((1 - t) * z1 + t * z2)) 0
        ≤ (1 - t) * (a * max (z1 - ζ) 0 + b * max (ζ - z1) 0)
          + t * (a * max (z2 - (ζ + y)) 0 + b * max ((ζ + y) - z2) 0) := by
      intro z1 z2 ζ y
      have hmx : ∀ p q : ℝ, max ((1 - t) * p + t * q) 0 ≤ (1 - t) * max p 0 + t * max q 0 :=
        fun p q => max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1t)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0.le))
          (add_nonneg (mul_nonneg h1t (le_max_right _ _)) (mul_nonneg ht0.le (le_max_right _ _)))
      have k1 := hmx (z1 - ζ) (z2 - (ζ + y))
      have k2 := hmx (ζ - z1) ((ζ + y) - z2)
      rw [show (1 - t) * (z1 - ζ) + t * (z2 - (ζ + y)) = ((1 - t) * z1 + t * z2) - (ζ + t * y) by
        ring] at k1
      rw [show (1 - t) * (ζ - z1) + t * ((ζ + y) - z2) = (ζ + t * y) - ((1 - t) * z1 + t * z2) by
        ring] at k2
      nlinarith [mul_le_mul_of_nonneg_left k1 ha.le, mul_le_mul_of_nonneg_left k2 hb.le]
    have hmixI : ∀ z1 z2 : ℝ,
        ∫ ζ, (∫ u in Ioo 0 1, (a * max (((1 - t) * z1 + t * z2) - (ζ + t * Q u)) 0
          + b * max ((ζ + t * Q u) - ((1 - t) * z1 + t * z2)) 0)) ∂(P.map Z)
        ≤ (1 - t) * ∫ ζ, (a * max (z1 - ζ) 0 + b * max (ζ - z1) 0) ∂(P.map Z)
          + t * ∫ ζ, (∫ u in Ioo 0 1, (a * max (z2 - (ζ + Q u)) 0
              + b * max ((ζ + Q u) - z2) 0)) ∂(P.map Z) := by
      intro z1 z2
      have hz1i : Integrable (fun ζ => a * max (z1 - ζ) 0 + b * max (ζ - z1) 0) (P.map Z) :=
        loss_int hνi ha.le hb.le z1
      have inner : ∀ ζ : ℝ,
          ∫ u in Ioo 0 1, (a * max (((1 - t) * z1 + t * z2) - (ζ + t * Q u)) 0
            + b * max ((ζ + t * Q u) - ((1 - t) * z1 + t * z2)) 0)
          ≤ (1 - t) * (a * max (z1 - ζ) 0 + b * max (ζ - z1) 0)
            + t * ∫ u in Ioo 0 1, (a * max (z2 - (ζ + Q u)) 0 + b * max ((ζ + Q u) - z2) 0) := by
        intro ζ
        have hi2 : Integrable (fun u => a * max (z2 - (ζ + Q u)) 0 + b * max ((ζ + Q u) - z2) 0)
            (volume.restrict (Ioo 0 1)) :=
          loss_int (X := fun u => ζ + Q u) ((integrable_const ζ).add hQi) ha.le hb.le z2
        have hi1 : Integrable (fun u => a * max (((1 - t) * z1 + t * z2) - (ζ + t * Q u)) 0
            + b * max ((ζ + t * Q u) - ((1 - t) * z1 + t * z2)) 0) (volume.restrict (Ioo 0 1)) :=
          loss_int (X := fun u => ζ + t * Q u) ((integrable_const ζ).add (hQi.const_mul t))
            ha.le hb.le _
        calc _ ≤ ∫ u in Ioo 0 1, ((1 - t) * (a * max (z1 - ζ) 0 + b * max (ζ - z1) 0)
                + t * (a * max (z2 - (ζ + Q u)) 0 + b * max ((ζ + Q u) - z2) 0)) :=
              integral_mono hi1 ((integrable_const _).add (hi2.const_mul t))
                fun u => hmix z1 z2 ζ (Q u)
          _ = _ := by
              rw [integral_add (integrable_const _) (hi2.const_mul t), integral_const,
                integral_const_mul]
              simp
      calc _ ≤ ∫ ζ, ((1 - t) * (a * max (z1 - ζ) 0 + b * max (ζ - z1) 0)
              + t * ∫ u in Ioo 0 1, (a * max (z2 - (ζ + Q u)) 0
                + b * max ((ζ + Q u) - z2) 0)) ∂(P.map Z) :=
            integral_mono (hin (fun u => t * Q u) (hQi.const_mul t) _)
              ((hz1i.const_mul _).add ((hin Q hQi z2).const_mul t)) inner
        _ = _ := by
            rw [integral_add (hz1i.const_mul _) ((hin Q hQi z2).const_mul t), integral_const_mul,
              integral_const_mul]
    have key : ∀ z1 z2 : ℝ, NV (fun ω => Z ω + Yt ω)
        ≤ (1 - t) * ∫ ω, (a * max (z1 - Z ω) 0 + b * max (Z ω - z1) 0) ∂P
          + t * ∫ ω, (a * max (z2 - (Z ω + Y ω)) 0 + b * max ((Z ω + Y ω) - z2) 0) ∂P := by
      intro z1 z2
      rw [hAZ, hA2]
      calc NV (fun ω => Z ω + Yt ω)
          ≤ ∫ ω, (a * max ((((1 - t) * z1 + t * z2) + mt - t * m) - (Z ω + Yt ω)) 0
              + b * max ((Z ω + Yt ω) - (((1 - t) * z1 + t * z2) + mt - t * m)) 0) ∂P :=
            ciInf_le (hbdd _) _
        _ = _ := hA2t _
        _ ≤ ∫ ζ, (∫ u in Ioo 0 1, (a * max (((1 - t) * z1 + t * z2) - (ζ + t * Q u)) 0
              + b * max ((ζ + t * Q u) - ((1 - t) * z1 + t * z2)) 0)) ∂(P.map Z) :=
            integral_mono (hin _ hQti _) (hin (fun u => t * Q u) (hQi.const_mul t) _)
              fun ζ => hcmp _ ζ
        _ ≤ _ := hmixI z1 z2
    obtain ⟨fZ, hfZ⟩ : ∃ f : ℝ → ℝ,
        f = fun z1 => ∫ ω, (a * max (z1 - Z ω) 0 + b * max (Z ω - z1) 0) ∂P := ⟨_, rfl⟩
    obtain ⟨gZ, hgZ⟩ : ∃ g : ℝ → ℝ,
        g = fun z2 => ∫ ω, (a * max (z2 - (Z ω + Y ω)) 0 + b * max ((Z ω + Y ω) - z2) 0) ∂P :=
      ⟨_, rfl⟩
    have eZ : NV Z = ⨅ z1, fZ z1 := by subst hfZ; rfl
    have eZY : NV (fun ω => Z ω + Y ω) = ⨅ z2, gZ z2 := by subst hgZ; rfl
    have key' : ∀ z1 z2 : ℝ, NV (fun ω => Z ω + Yt ω) ≤ (1 - t) * fZ z1 + t * gZ z2 := by
      subst hfZ hgZ; exact key
    have h1 : ∀ z2, NV (fun ω => Z ω + Yt ω) - t * gZ z2 ≤ (1 - t) * ⨅ z1, fZ z1 := by
      intro z2
      rw [Real.mul_iInf_of_nonneg h1t]
      exact le_ciInf fun z1 => by linarith [key' z1 z2]
    have h2 : NV (fun ω => Z ω + Yt ω) - (1 - t) * (⨅ z1, fZ z1) ≤ t * ⨅ z2, gZ z2 := by
      rw [Real.mul_iInf_of_nonneg ht0.le]
      exact le_ciInf fun z2 => by linarith [h1 z2]
    rw [eZ, eZY]
    linarith
  · -- `(1 - t) NV(Z) + t NV(Z + Y) ≤ NV(Z + Y)`
    nlinarith [mul_le_mul_of_nonneg_left hNVZ h1t]
