-- Prove2me | solution 1 for PGDMap20261031.pgd_prefix_to_upper
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T17:30:58.31801+00:00
-- url     : https://prove2.me/submissions/88f873c4-76b1-4af3-a963-4f12a7962e01

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Definitions.Def_PGDMap20261031_PGD

open PGDMap20261031 Set Filter
open scoped Topology RealInnerProductSpace BigOperators
noncomputable section

private lemma line_deriv {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (x v : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (g (x + t • v)) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    convert ((hasDerivAt_id t).smul_const v).const_add x using 1 <;> first | rfl | simp
  convert (hgrad (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl using 1 <;> rfl

private lemma smooth_descent {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (L : ℝ) (hf : SmoothConvex f g L) (x y : Space d) :
    f y ≤ f x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  let v := y - x
  let φ := fun t : ℝ => f (x + t • v) - t * inner ℝ (g x) v -
    (L / 2 * ‖v‖ ^ 2) * t ^ 2
  have hd (t : ℝ) : HasDerivAt φ
      (inner ℝ (g (x + t • v)) v - inner ℝ (g x) v - L * t * ‖v‖ ^ 2) t := by
    convert ((line_deriv f g hf.2.1 x v t).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (g x) v))).sub
        (((hasDerivAt_id t).pow 2).const_mul (L / 2 * ‖v‖ ^ 2)) using 1 <;> try rfl
    simp only [id_eq, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by omega, pow_one, mul_one]
    ring
  have hanti : AntitoneOn φ (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro t _
      exact (hd t).continuousAt.continuousWithinAt
    · intro t _
      exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      have hinner := real_inner_le_norm (g (x + t • v) - g x) v
      have hLip := hf.2.2 (x + t • v) x
      have hnorm : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hnorm] at hLip
      have hmul := mul_le_mul_of_nonneg_right hLip (norm_nonneg v)
      rw [inner_sub_left] at hinner
      nlinarith only [hinner, hmul]
  have hval := hanti (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) (by norm_num)
  have hv : x + v = y := by dsimp [v]; abel
  dsimp [φ] at hval
  simp only [zero_smul, one_smul, add_zero, zero_mul, mul_zero, one_mul,
    zero_pow (by norm_num : 2 ≠ 0), one_pow, mul_one, sub_zero, hv] at hval
  dsimp [v] at hval
  linarith

private lemma proximal_support {d : ℕ} (r : Penalty d) (μ γ : ℝ) (hr : IsPenalty r)
    (hstrong : StrongPenalty r μ) (hγ : 0 < γ) (c y : Space d) (hy : y ∈ r.domain)
    (hmin : ∀ z ∈ r.domain, r.value y + ‖y - c‖ ^ 2 / (2 * γ) ≤
      r.value z + ‖z - c‖ ^ 2 / (2 * γ)) :
    ∀ z ∈ r.domain, r.value y - inner ℝ (y - c) (z - y) / γ +
      μ / 2 * ‖z - y‖ ^ 2 ≤ r.value z := by
  intro z hz
  let A := 2 * γ * (r.value y - r.value z) - 2 * inner ℝ (y - c) (z - y) +
    γ * μ * ‖z - y‖ ^ 2
  let C := (γ * μ + 1) * ‖z - y‖ ^ 2
  have ht_bound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : A - t * C ≤ 0 := by
    let w := t • z + (1 - t) • y
    have hw : w ∈ r.domain := hr.2.2.1 hz hy ht.1.le (by linarith [ht.2]) (by ring)
    have hopt := hmin w hw
    have hconv := hstrong z hz y hy t ⟨ht.1.le, ht.2.le⟩
    have hnorm : ‖w - c‖ ^ 2 = ‖y - c‖ ^ 2 +
        2 * t * inner ℝ (y - c) (z - y) + t ^ 2 * ‖z - y‖ ^ 2 := by
      have hv : w - c = (y - c) + t • (z - y) := by dsimp [w]; module
      rw [hv, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
      ring
    have hopt' := mul_le_mul_of_nonneg_left hopt (show 0 ≤ 2 * γ by positivity)
    have hconv' := mul_le_mul_of_nonneg_left hconv (show 0 ≤ 2 * γ by positivity)
    rw [hnorm] at hopt'
    field_simp [ne_of_gt hγ] at hopt'
    have hprod : t * (A - t * C) ≤ 0 := by
      dsimp [A, C, w]
      nlinarith only [hopt', hconv']
    by_contra hn
    exact (not_lt_of_ge hprod) (mul_pos ht.1 (lt_of_not_ge hn))
  have hlim : Tendsto (fun t : ℝ => A - t * C) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [zero_mul, sub_zero] using (hid.mul_const C).const_sub A
  have hA : A ≤ 0 := by
    apply le_of_tendsto hlim
    have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from Iio_mem_nhds (by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hlt1, self_mem_nhdsWithin] with t ht1 ht0
    exact ht_bound t ⟨ht0, ht1⟩
  have htarget : (r.value y - inner ℝ (y - c) (z - y) / γ +
      μ / 2 * ‖z - y‖ ^ 2 - r.value z) * (2 * γ) = A := by
    dsimp [A]
    field_simp [ne_of_gt hγ]
    <;> ring
  have hprod : (r.value y - inner ℝ (y - c) (z - y) / γ +
      μ / 2 * ‖z - y‖ ^ 2 - r.value z) * (2 * γ) ≤ 0 := by rw [htarget]; exact hA
  apply sub_nonpos.mp
  by_contra hn
  exact (not_lt_of_ge hprod) (mul_pos (lt_of_not_ge hn) (by positivity : 0 < 2 * γ))

private lemma last_descent {d : ℕ} (r : Penalty d) (f : Space d → ℝ) (g : Space d → Space d)
    (L μ γ : ℝ) (hr : IsPenalty r) (hstrong : StrongPenalty r μ) (hf : SmoothConvex f g L)
    (hγ : 0 < γ) (x y : Space d) (hx : x ∈ r.domain) (hy : y ∈ r.domain)
    (hmin : ∀ z ∈ r.domain, r.value y + ‖y - (x - γ • g x)‖ ^ 2 / (2 * γ) ≤
      r.value z + ‖z - (x - γ • g x)‖ ^ 2 / (2 * γ)) :
    (1 / γ - L / 2 + μ / 2) * ‖x - y‖ ^ 2 ≤ totalValue r f x - totalValue r f y := by
  have hprox := proximal_support r μ γ hr hstrong hγ (x - γ • g x) y hy hmin x hx
  have hdesc := smooth_descent f g L hf x y
  have hinner : inner ℝ (y - (x - γ • g x)) (x - y) =
      -‖x - y‖ ^ 2 + γ * inner ℝ (g x) (x - y) := by
    have hv : y - (x - γ • g x) = -(x - y) + γ • g x := by module
    rw [hv, inner_add_left, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hquot : inner ℝ (y - (x - γ • g x)) (x - y) / γ =
      -‖x - y‖ ^ 2 / γ + inner ℝ (g x) (x - y) := by
    rw [hinner]
    field_simp [ne_of_gt hγ]
    <;> ring
  rw [hquot] at hprox
  have hrev : inner ℝ (g x) (y - x) = -inner ℝ (g x) (x - y) := by
    rw [show y - x = -(x - y) by module, inner_neg_right]
  rw [hrev, norm_sub_rev y x] at hdesc
  unfold totalValue
  simp only [div_eq_mul_inv] at hprox ⊢
  nlinarith only [hprox, hdesc]

private lemma geom_polynomial (n : ℕ) (b : ℝ) :
    (b - 1) * (∑ j ∈ Finset.Icc 1 n, b ^ j) = b ^ (n + 1) - b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    rw [pow_succ b (n + 1)]
    ring

private lemma geom_inverse (n : ℕ) (z : ℝ) (hz : z ≠ 0) :
    (1 - z) * (∑ j ∈ Finset.Icc 1 n, (z ^ j)⁻¹) = (z ^ n)⁻¹ - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih, pow_succ, mul_inv_rev]
    field_simp [hz, pow_ne_zero n hz]
    <;> ring

private lemma geometric_first (k : ℕ) (b : ℝ) :
    (b - 1) * geometricSum k (1 / b) = b ^ (2 * k + 1) - b := by
  simpa only [geometricSum, one_div, inv_pow, inv_inv] using geom_polynomial (2 * k) b

private lemma geometric_one (k : ℕ) : geometricSum k 1 = 2 * (k : ℝ) := by
  simp [geometricSum, Nat.card_Icc]

private lemma A_den_positive (N : ℕ) (h q : ℝ) (hN : 1 ≤ N) (hh : validStep h) (hq : 0 < q) :
    0 < base h q ^ (2 * N) - 1 - h ^ 2 * q := by
  have hb : 1 ≤ base h q := by dsimp [base]; nlinarith [hh.1]
  have hpow : base h q ^ 2 ≤ base h q ^ (2 * N) := pow_le_pow_right₀ hb (by omega)
  have hpos : 0 < h * q * (2 - h + h * q) := by
    exact mul_pos (mul_pos hh.1 hq) (by nlinarith [hh.2, hh.1])
  dsimp [base] at hpow ⊢
  nlinarith only [hpow, hpos]

private lemma B_den_positive (N : ℕ) (h q : ℝ) (hN : 1 ≤ N) (hh : validStep h) (hq : 0 ≤ q) :
    0 < base h q ^ (2 * N) - (1 - h) ^ (2 * N) := by
  have hb : 1 ≤ base h q := by dsimp [base]; nlinarith [hh.1]
  have hpow := one_le_pow₀ hb (n := 2 * N)
  have hsq : (1 - h) ^ 2 < 1 := by nlinarith [hh.1, hh.2]
  have ht := pow_lt_one₀ (sq_nonneg (1 - h)) hsq (by omega : N ≠ 0)
  rw [← pow_mul] at ht
  linarith

private lemma first_product (k : ℕ) (h q : ℝ) (hh : validStep h) (hq : 0 ≤ q) :
    h ^ 2 * branchA (k + 1) h q *
      (base h q / (2 * h) * geometricSum k (1 / base h q) + 1 / h - 1 / 2 + q / 2) = 1 := by
  have hh0 : h ≠ 0 := ne_of_gt hh.1
  have hn : 1 ≤ k + 1 := by omega
  unfold branchA
  by_cases hq0 : q = 0
  · rw [if_pos hq0]
    simp only [hq0, base, mul_zero, add_zero, div_one, geometric_one]
    have hd : 0 < 2 * ((k + 1 : ℕ) : ℝ) - h := by
      push_cast
      nlinarith [hh.2, (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    field_simp [hh0, ne_of_gt hd]
    push_cast
    ring
  · rw [if_neg hq0]
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hd := ne_of_gt (A_den_positive (k + 1) h q hn hh hqpos)
    have hg := geometric_first k (base h q)
    have hexp : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [← mul_div_assoc (h ^ 2) (2 * q) (base h q ^ (2 * (k + 1)) - 1 - h ^ 2 * q),
      div_mul_eq_mul_div]
    apply (div_eq_iff hd).2
    rw [hexp, pow_succ]
    field_simp [hh0]
    have hmul := congrArg (fun v : ℝ => base h q * v) hg
    dsimp [base] at hmul ⊢
    rw [pow_succ (1 + h * q) (2 * k + 1)]
    nlinarith only [hmul]

private lemma second_product (k : ℕ) (h q : ℝ) (hh : validStep h) (hq : 0 ≤ q)
    (hh1 : h ≠ 1) :
    h ^ 2 * branchB (k + 1) h q *
      (base h q / (2 * h) * geometricSum k ((1 - h) / base h q) + 1 / h - 1 / 2 + q / 2) = 1 := by
  have hb : 0 < base h q := by dsimp [base]; nlinarith [hh.1]
  have hh0 : h ≠ 0 := ne_of_gt hh.1
  have ht0 : 1 - h ≠ 0 := sub_ne_zero.mpr (Ne.symm hh1)
  have hz0 : (1 - h) / base h q ≠ 0 := div_ne_zero ht0 (ne_of_gt hb)
  have hd := ne_of_gt (B_den_positive (k + 1) h q (by omega) hh hq)
  have hg := geom_inverse (2 * k) ((1 - h) / base h q) hz0
  change (1 - (1 - h) / base h q) * geometricSum k ((1 - h) / base h q) = _ at hg
  rw [div_pow, inv_div] at hg
  field_simp [ne_of_gt hb, pow_ne_zero (2 * k) ht0] at hg
  unfold branchB
  rw [show 2 * (k + 1) - 2 = 2 * k by omega]
  rw [← mul_div_assoc (h ^ 2) (2 * (1 + q) * (1 - h) ^ (2 * k))
    (base h q ^ (2 * (k + 1)) - (1 - h) ^ (2 * (k + 1))), div_mul_eq_mul_div]
  apply (div_eq_iff hd).2
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_add]
  field_simp [hh0]
  have hmul := congrArg (fun v : ℝ => base h q * v) hg
  dsimp [base] at hmul ⊢
  nlinarith only [hmul]

private lemma A_positive (N : ℕ) (h q : ℝ) (hN : 1 ≤ N) (hh : validStep h) (hq : 0 ≤ q) :
    0 < branchA N h q := by
  unfold branchA
  split_ifs with hq0
  · have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact div_pos (by norm_num) (mul_pos hh.1 (by nlinarith [hh.2]))
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    exact div_pos (mul_pos (by norm_num) hqpos) (A_den_positive N h q hN hh hqpos)

private lemma B_positive (k : ℕ) (h q : ℝ) (hh : validStep h) (hq : 0 ≤ q) (hh1 : h ≠ 1) :
    0 < branchB (k + 1) h q := by
  unfold branchB
  rw [show 2 * (k + 1) - 2 = 2 * k by omega]
  have ht : 0 < (1 - h) ^ (2 * k) := (show Even (2 * k) from ⟨k, by omega⟩).pow_pos
    (sub_ne_zero.mpr (Ne.symm hh1))
  exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) ht)
    (B_den_positive (k + 1) h q (by omega) hh hq)

private lemma prefix_scalar (k : ℕ) (h q : ℝ) (hk : 1 ≤ k) (hh : validStep h) (hq : 0 ≤ q) :
    let C := prefixCoefficient k h q + 1 / h - 1 / 2 + q / 2
    0 < C ∧ 0 < curve (k + 1) h q ∧ 1 ≤ h ^ 2 * curve (k + 1) h q * C := by
  dsimp only
  let C := prefixCoefficient k h q + 1 / h - 1 / 2 + q / 2
  change 0 < C ∧ 0 < curve (k + 1) h q ∧ 1 ≤ h ^ 2 * curve (k + 1) h q * C
  have hcurve : curve (k + 1) h q = max (branchA (k + 1) h q) (branchB (k + 1) h q) := by
    rw [curve, if_neg (by omega)]
  have hbound (B D : ℝ) (hB : 0 < B) (hprod : h ^ 2 * B * D = 1)
      (hle : B ≤ curve (k + 1) h q) :
      0 < D ∧ 0 < curve (k + 1) h q ∧ 1 ≤ h ^ 2 * curve (k + 1) h q * D := by
    have hD : 0 < D := by
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg h) hB.le) (le_of_not_gt hn)
      rw [hprod] at hm
      norm_num at hm
    refine ⟨hD, lt_of_lt_of_le hB hle, ?_⟩
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (sq_nonneg h)) hD.le
    rwa [hprod] at hm
  by_cases hh1 : h = 1
  · have heq : C = base h q / (2 * h) * geometricSum k (1 / base h q) + 1 / h - 1 / 2 + q / 2 := by
      dsimp [C, prefixCoefficient]
      rw [if_pos hh1]
    rw [heq]
    exact hbound _ _ (A_positive (k + 1) h q (by omega) hh hq) (first_product k h q hh hq)
      (by rw [hcurve]; exact le_max_left _ _)
  · by_cases hmin : geometricSum k (1 / base h q) ≤ geometricSum k ((1 - h) / base h q)
    · have heq : C = base h q / (2 * h) * geometricSum k (1 / base h q) + 1 / h - 1 / 2 + q / 2 := by
        dsimp [C, prefixCoefficient]
        rw [if_neg hh1, min_eq_left hmin]
      rw [heq]
      exact hbound _ _ (A_positive (k + 1) h q (by omega) hh hq) (first_product k h q hh hq)
        (by rw [hcurve]; exact le_max_left _ _)
    · have heq : C = base h q / (2 * h) * geometricSum k ((1 - h) / base h q) + 1 / h - 1 / 2 + q / 2 := by
        dsimp [C, prefixCoefficient]
        rw [if_neg hh1, min_eq_right (le_of_not_ge hmin)]
      rw [heq]
      exact hbound _ _ (B_positive k h q hh hq hh1) (second_product k h q hh hq hh1)
        (by rw [hcurve]; exact le_max_right _ _)

private lemma one_product (h q : ℝ) (hh : validStep h) (hq : 0 ≤ q) :
    0 < curveOne h q ∧ h ^ 2 * curveOne h q * (1 / h - 1 / 2 + q / 2) = 1 := by
  have hd : 0 < h * (2 - h + h * q) := mul_pos hh.1 (by nlinarith [hh.2, hh.1])
  constructor
  · exact div_pos (by norm_num) hd
  · unfold curveOne
    field_simp [ne_of_gt hd, ne_of_gt hh.1,
      (ne_of_gt (by nlinarith [hh.2, hh.1]) : 2 - h + h * q ≠ 0)]
    <;> ring

private lemma weighted_residual (s D h K C : ℝ) (hs : 0 ≤ s) (hh : 0 < h)
    (hK : 0 ≤ K) (hC : C * s ≤ D) (hprod : 1 ≤ h ^ 2 * K * C) : s / h ^ 2 ≤ K * D := by
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  have h1 := mul_le_mul_of_nonneg_right hprod hs
  have h2 := mul_le_mul_of_nonneg_left hC (mul_nonneg (sq_nonneg h) hK)
  nlinarith only [h1, h2]

private lemma unit_upper (hpref : PrefixCertificateClaim) (d : ℕ) (r : Penalty d)
    (q h : ℝ) (N : ℕ) (f : Space d → ℝ) (g : Space d → Space d) (x : ℕ → Space d)
    (hr : IsPenalty r) (hq : 0 ≤ q) (hs : StrongPenalty r q) (hh : validStep h)
    (hN : 1 ≤ N) (hf : SmoothConvex f g 1) (ht : IsPGDTrajectory r g h N x) :
    residualSquared h x N ≤ curve N h q * decrease r f x N := by
  by_cases hN1 : N = 1
  · subst N
    have hd := last_descent r f g 1 q h hr hs hf hh.1 (x 0) (x 1)
      (ht.1 0 (by omega)) (ht.1 1 le_rfl) (ht.2 0 (by omega))
    have hscalar := one_product h q hh hq
    have hbound := weighted_residual (‖x 0 - x 1‖ ^ 2) (decrease r f x 1) h (curveOne h q)
      (1 / h - 1 / 2 + q / 2) (sq_nonneg _) hh.1 hscalar.1.le hd hscalar.2.ge
    simpa only [residualSquared, Nat.sub_self, curve, if_pos rfl, ite_true] using hbound
  · let k := N - 1
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hNk : k + 1 = N := by dsimp [k]; omega
    have ht' : IsPGDTrajectory r g h (k + 1) x := by simpa only [hNk] using ht
    have hpre := hpref d r q h k f g x hr hq hs hh hk hf ht'
    have hd := last_descent r f g 1 q h hr hs hf hh.1 (x k) (x (k + 1))
      (ht'.1 k (by omega)) (ht'.1 (k + 1) le_rfl) (ht'.2 k (by omega))
    have htotal : (prefixCoefficient k h q + 1 / h - 1 / 2 + q / 2) *
        ‖x k - x (k + 1)‖ ^ 2 ≤ decrease r f x (k + 1) := by
      unfold decrease at hpre ⊢
      nlinarith only [hpre, hd]
    obtain ⟨_, hK, hprod⟩ := prefix_scalar k h q hk hh hq
    have hbound := weighted_residual (‖x k - x (k + 1)‖ ^ 2) (decrease r f x (k + 1)) h
      (curve (k + 1) h q) (prefixCoefficient k h q + 1 / h - 1 / 2 + q / 2)
      (sq_nonneg _) hh.1 hK.le htotal hprod
    change ‖x (N - 1) - x N‖ ^ 2 / h ^ 2 ≤ _
    simpa only [hNk] using hbound

private def scaledPenalty {d : ℕ} (r : Penalty d) (L : ℝ) : Penalty d :=
  ⟨r.domain, fun x => r.value x / L⟩

private lemma convex_div {d : ℕ} (s : Set (Space d)) (f : Space d → ℝ) (hf : ConvexOn ℝ s f)
    (L : ℝ) (hL : 0 < L) : ConvexOn ℝ s (fun x => f x / L) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := mul_le_mul_of_nonneg_right (hf.2 hx hy ha hb hab) (inv_nonneg.mpr hL.le)
  simpa only [smul_eq_mul, div_eq_mul_inv, add_mul, mul_assoc] using h

private lemma scaled_penalty_valid {d : ℕ} (r : Penalty d) (L : ℝ) (hr : IsPenalty r) (hL : 0 < L) :
    IsPenalty (scaledPenalty r L) := by
  refine ⟨hr.1, ?_, convex_div r.domain r.value hr.2.2 L hL⟩
  have hcont : Continuous (fun z : Space d × ℝ => (z.1, L * z.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hclosed := hr.2.1.preimage hcont
  have hset : {z : Space d × ℝ | z.1 ∈ r.domain ∧ r.value z.1 / L ≤ z.2} =
      (fun z : Space d × ℝ => (z.1, L * z.2)) ⁻¹'
        {z : Space d × ℝ | z.1 ∈ r.domain ∧ r.value z.1 ≤ z.2} := by
    ext z
    simp only [mem_setOf_eq, mem_preimage, div_le_iff₀ hL, mul_comm z.2 L]
  exact hset ▸ hclosed

private lemma scaled_strong {d : ℕ} (r : Penalty d) (L μ : ℝ) (hL : 0 < L)
    (hs : StrongPenalty r μ) : StrongPenalty (scaledPenalty r L) (μ / L) := by
  intro x hx y hy t ht
  have h := div_le_div_of_nonneg_right (hs x hx y hy t ht) hL.le
  convert h using 1 <;> try rfl
  dsimp [scaledPenalty]
  ring

private lemma scaled_smooth {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d) (L : ℝ)
    (hL : 0 < L) (hf : SmoothConvex f g L) :
    SmoothConvex (fun x => f x / L) (fun x => L⁻¹ • g x) 1 := by
  refine ⟨convex_div univ f hf.1 L hL, ?_, ?_⟩
  · intro x
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hdual : (InnerProductSpace.toDual ℝ (Space d)) (L⁻¹ • g x) =
        L⁻¹ • (InnerProductSpace.toDual ℝ (Space d)) (g x) := by
      ext v
      change inner ℝ (L⁻¹ • g x) v = L⁻¹ * inner ℝ (g x) v
      rw [real_inner_smul_left]
    have hfun : (fun x => f x / L) = (fun x => L⁻¹ * f x) := by
      funext x
      simp only [div_eq_mul_inv, mul_comm]
    rw [hdual, hfun]
    exact (hf.2.1 x).hasFDerivAt.const_mul L⁻¹
  · intro x y
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), one_mul]
    have hm := mul_le_mul_of_nonneg_left (hf.2.2 x y) (inv_nonneg.mpr hL.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL), one_mul] using hm

private lemma scaled_trajectory {d : ℕ} (r : Penalty d) (g : Space d → Space d) (L h : ℝ)
    (N : ℕ) (x : ℕ → Space d) (hL : 0 < L) (hh : 0 < h)
    (ht : IsPGDTrajectory r g (h / L) N x) :
    IsPGDTrajectory (scaledPenalty r L) (fun x => L⁻¹ • g x) h N x := by
  refine ⟨ht.1, ?_⟩
  intro i hi y hy
  have hc : x i - h • (L⁻¹ • g (x i)) = x i - (h / L) • g (x i) := by
    rw [smul_smul]
    congr 2
  have hobj (z : Space d) : r.value z / L + ‖z - (x i - (h / L) • g (x i))‖ ^ 2 / (2 * h) =
      (r.value z + ‖z - (x i - (h / L) • g (x i))‖ ^ 2 / (2 * (h / L))) / L := by
    field_simp [ne_of_gt hL, ne_of_gt hh]
    <;> ring
  change r.value (x (i + 1)) / L + _ ≤ r.value y / L + _
  rw [hc, hobj, hobj]
  exact div_le_div_of_nonneg_right (ht.2 i hi y hy) hL.le

theorem solution : PrefixCertificateClaim → UniformUpperClaim := by
  intro hpref d r L μ h N f g x hr hL hμ hs hh hN hf ht
  have hunit := unit_upper hpref d (scaledPenalty r L) (μ / L) h N
    (fun x => f x / L) (fun x => L⁻¹ • g x) x (scaled_penalty_valid r L hr hL)
    (div_nonneg hμ hL.le) (scaled_strong r L μ hL hs) hh hN (scaled_smooth f g L hL hf)
    (scaled_trajectory r g L h N x hL hh.1 ht)
  have hdelta : decrease (scaledPenalty r L) (fun x => f x / L) x N = decrease r f x N / L := by
    unfold decrease totalValue scaledPenalty
    ring
  have hres : residualSquared (h / L) x N = L ^ 2 * residualSquared h x N := by
    unfold residualSquared
    field_simp [ne_of_gt hL, ne_of_gt hh.1]
    <;> ring
  rw [hres]
  calc
    _ ≤ L ^ 2 * (curve N h (μ / L) * decrease (scaledPenalty r L) (fun x => f x / L) x N) :=
      mul_le_mul_of_nonneg_left hunit (sq_nonneg L)
    _ = _ := by
      rw [hdelta]
      field_simp [ne_of_gt hL]
      <;> ring
