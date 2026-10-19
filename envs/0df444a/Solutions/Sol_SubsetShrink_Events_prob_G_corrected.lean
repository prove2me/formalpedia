-- Prove2me | solution 1 for SubsetShrink.Events.prob_G_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T11:57:26.25517+00:00
-- url     : https://prove2.me/submissions/8c6e1f20-4828-4b41-b32b-e517a3d499e7

/-
  DS19A submission: `SubsetShrink.Events.prob_G_corrected`
  target ee53bbda-0dac-4c4f-8f65-23414897e20f
  (mission 97e863d6-ac4e-4114-a6d3-d16a481f46a2).

  Theorem 1 of Mazumder–Radchenko–Dedieu, *Subset Selection with Shrinkage*,
  p. 13 / §B.1, with the fast-rate constant corrected to 3 log(1/δ₀):

      G'_s = {ε | εᵀXu ≤ σ√(5s log(ep/s) + 3 log(1/δ₀)) ‖Xu‖  for all ‖u‖₀ ≤ s}

  is measurable and P(G'_s) ≥ 1 - δ₀ for ε ~ N(0,σ²)^{⊗n}.

  Proof outline (self-contained; no platform theorem is imported beyond the shared
  definition file):

  * deterministic geometry: for a support `S`, the supremum of `εᵀXu/‖Xu‖` over
    `supp u ⊆ S` is the norm of the orthogonal projection of `ε` onto the span
    `K_S` of the columns in `S` (Stage A: `BS_eq_norm`);
  * the projection has at most `s` degrees of freedom (`finrank K_S ≤ |S| = s`);
  * its coordinates in an orthonormal basis of `K_S` are i.i.d. `N(0,σ²)`
    (Stage B: `noiseLaw_map_coords_family`), so the failure probability for `S`
    is a chi-square tail with `d ≤ s` degrees of freedom;
  * the Laurent–Massart bound at the `d`-dof optimal exponent, with
    `x = s log(ep/s) + log(1/δ₀)`, gives `P(failure for S) ≤ e^{-x}`
    (`chiSq_tail_dof_le`);
  * a union bound over the `C(p,s) ≤ (ep/s)^s` supports gives
    `P(G'_sᶜ) ≤ e^{s log(ep/s)} e^{-x} = δ₀` (Stage C).

  The DS12 chi-square/MGF helpers and the DS13 `toE`/coordinate-law helpers are
  inlined below with attribution; the DS19A geometry/law/union-bound material is
  inlined as well.  Expected axiom footprint: propext, Classical.choice, Quot.sound.
-/
import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

namespace SubsetShrink.Events

noncomputable section

/-! ## Inlined DS12 helpers: MGF and chi-square tail bounds -/


/-! ## 1. MGF of the square of a centred Gaussian -/

lemma two_mul_var_pos {v : ℝ≥0} (hv : v ≠ 0) : 0 < 2 * (v : ℝ) := by
  have hv' : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  linarith

lemma inv_two_mul_sub_eq {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    1 / (2 * (v : ℝ)) - t = (1 - 2 * (v : ℝ) * t) / (2 * (v : ℝ)) := by
  have hv' : (2 * (v : ℝ)) ≠ 0 := ne_of_gt (two_mul_var_pos hv)
  field_simp

lemma two_mul_mul_inv_sub {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    2 * (v : ℝ) * (1 / (2 * (v : ℝ)) - t) = 1 - 2 * (v : ℝ) * t := by
  have hv' : (2 * (v : ℝ)) ≠ 0 := ne_of_gt (two_mul_var_pos hv)
  field_simp

/-- Pointwise rewriting of the integrand: multiplying the standard Gaussian density by
`exp (t x²)` produces a Gaussian density with variance `v / (1 - 2 v t)`. -/
lemma gaussianPDFReal_mul_exp_sq {v : ℝ≥0} (hv : v ≠ 0) (t x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * x ^ 2) := by
  rw [gaussianPDFReal, sub_zero, mul_assoc]
  congr 1
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- Integrability of `x ↦ exp (t x²)` under `N(0,v)`, for `2 v t < 1`. -/
lemma integrable_exp_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ}
    (ht : 2 * (v : ℝ) * t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 v) := by
  have hb : 0 < 1 / (2 * (v : ℝ)) - t := by
    rw [inv_two_mul_sub_eq hv t]
    exact div_pos (by linarith) (two_mul_var_pos hv)
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff (measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have h2 : Integrable (fun x : ℝ =>
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * x ^ 2)) volume :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  refine h2.congr ?_
  filter_upwards with x
  rw [toReal_gaussianPDF, mul_comm (Real.exp (t * x ^ 2)) (gaussianPDFReal 0 v x)]
  exact (gaussianPDFReal_mul_exp_sq hv t x).symm

/-- Exact integral of `x ↦ exp (t x²)` under `N(0,v)`: `1/√(1 - 2 v t)`. -/
lemma integral_exp_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ}
    (ht : 2 * (v : ℝ) * t < 1) :
    ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal 0 v) = 1 / Real.sqrt (1 - 2 * (v : ℝ) * t) := by
  have hb : 0 < 1 / (2 * (v : ℝ)) - t := by
    rw [inv_two_mul_sub_eq hv t]
    exact div_pos (by linarith) (two_mul_var_pos hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [show (fun x : ℝ => gaussianPDFReal 0 v x * Real.exp (t * x ^ 2)) =
      fun x : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * x ^ 2) from
      funext fun x => gaussianPDFReal_mul_exp_sq hv t x]
  rw [integral_const_mul, _root_.integral_gaussian]
  -- numeric identity
  have h2vb : 2 * (v : ℝ) * (1 / (2 * (v : ℝ)) - t) = 1 - 2 * (v : ℝ) * t :=
    two_mul_mul_inv_sub hv t
  rw [← h2vb]
  have hπ : 0 < Real.pi := Real.pi_pos
  have key : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.sqrt (Real.pi / (1 / (2 * (v : ℝ)) - t)) =
      Real.sqrt ((2 * (v : ℝ) * (1 / (2 * (v : ℝ)) - t))⁻¹) := by
    rw [(Real.sqrt_inv (2 * Real.pi * (v : ℝ))).symm,
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi * (v : ℝ))⁻¹)]
    congr 1
    field_simp
  rw [key]
  conv_rhs => rw [one_div]
  exact Real.sqrt_inv _

/-- **MGF of the square of a centred Gaussian.** For `Z ~ N(0,v)` and `2 v t < 1`,
`E[e^{t Z²}] = 1/√(1 - 2 v t)`. -/
theorem mgf_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 2 * (v : ℝ) * t < 1) :
    mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 v) t = 1 / Real.sqrt (1 - 2 * (v : ℝ) * t) := by
  rw [mgf]
  exact integral_exp_sq_gaussianReal hv ht

/-! ## 2. Finite sums of independent squares on the product Gaussian space -/

lemma integrable_pi_exp_sq {k : ℕ} {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ}
    (ht : 2 * (v : ℝ) * t < 1) :
    Integrable (fun x : Fin k → ℝ => Real.exp (t * ∑ i, x i ^ 2))
      (Measure.pi (fun _ : Fin k => gaussianReal 0 v)) := by
  have hprod : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (t * x i ^ 2))
      (Measure.pi (fun _ : Fin k => gaussianReal 0 v)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_sq_gaussianReal hv ht)
  refine hprod.congr ?_
  filter_upwards with x
  rw [Finset.mul_sum, Real.exp_sum]

/-- **MGF of a finite sum of independent squares.** Under the product law of `k` centred
Gaussians of variance `v`, `E[e^{t ∑ xᵢ²}] = (1/√(1 - 2 v t))^k`. -/
theorem mgf_sum_sq_pi {k : ℕ} {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ}
    (ht : 2 * (v : ℝ) * t < 1) :
    mgf (fun x : Fin k → ℝ => ∑ i, x i ^ 2) (Measure.pi (fun _ : Fin k => gaussianReal 0 v)) t =
      (1 / Real.sqrt (1 - 2 * (v : ℝ) * t)) ^ k := by
  rw [mgf]
  have eq : (fun x : Fin k → ℝ => Real.exp (t * ∑ i, x i ^ 2)) =
      fun x : Fin k → ℝ => ∏ i, Real.exp (t * x i ^ 2) := by
    funext x
    rw [Finset.mul_sum, Real.exp_sum]
  rw [eq, integral_fintype_prod_eq_pow (f := fun x : ℝ => Real.exp (t * x ^ 2))
      (μ := gaussianReal 0 v), Fintype.card_fin, integral_exp_sq_gaussianReal hv ht]

/-- **Chernoff bound for a finite sum of independent squares.** -/
theorem measure_sum_sq_ge_le {k : ℕ} {v : ℝ≥0} (hv : v ≠ 0) {t y : ℝ} (ht0 : 0 ≤ t)
    (ht : 2 * (v : ℝ) * t < 1) :
    (Measure.pi (fun _ : Fin k => gaussianReal 0 v)).real {x : Fin k → ℝ | y ≤ ∑ i, x i ^ 2}
      ≤ Real.exp (-t * y) * (1 / Real.sqrt (1 - 2 * (v : ℝ) * t)) ^ k := by
  calc (Measure.pi (fun _ : Fin k => gaussianReal 0 v)).real {x : Fin k → ℝ | y ≤ ∑ i, x i ^ 2}
      ≤ Real.exp (-t * y) *
          mgf (fun x : Fin k → ℝ => ∑ i, x i ^ 2)
            (Measure.pi (fun _ : Fin k => gaussianReal 0 v)) t :=
        measure_ge_le_exp_mul_mgf y ht0 (integrable_pi_exp_sq hv ht)
    _ = Real.exp (-t * y) * (1 / Real.sqrt (1 - 2 * (v : ℝ) * t)) ^ k := by
        rw [mgf_sum_sq_pi hv ht]

/-! ## 3. Laurent–Massart numerical inequality at the optimal exponent -/

/-- `√(kx) = k · (2√(kx)/k) / 2`. -/
lemma sqrt_mul_eq {k : ℕ} {x : ℝ} (hk : 0 < k) :
    Real.sqrt ((k : ℝ) * x) = (k : ℝ) * (2 * Real.sqrt ((k : ℝ) * x) / k) / 2 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp

/-- **Laurent–Massart numerical inequality (optimal exponent).**

With `Y = k + 2√(kx) + 2x` (`k > 0`, `x ≥ 0`), the chi-square Chernoff bound at the optimal
`t` (where `1 - 2vt = k/Y`, so that `tY = (Y-k)/2`) is at most `e^{-x}`:

`(1/√(1-2vt))^k · e^{-tY} = √(Y/k)^k · e^{-(Y-k)/2} ≤ e^{-x}`. -/
theorem lm_sqrt_bound {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt ((k + 2 * Real.sqrt ((k : ℝ) * x) + 2 * x) / k) ^ k *
        Real.exp (-((k + 2 * Real.sqrt ((k : ℝ) * x) + 2 * x) - k) / 2) ≤ Real.exp (-x) := by
  set Y : ℝ := k + 2 * Real.sqrt ((k : ℝ) * x) + 2 * x with hY
  set w : ℝ := 2 * Real.sqrt ((k : ℝ) * x) / k with hw
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkx : 0 ≤ (k : ℝ) * x := mul_nonneg hk'.le hx
  have hsq : Real.sqrt ((k : ℝ) * x) = (k : ℝ) * w / 2 := sqrt_mul_eq hk
  have hw_nonneg : 0 ≤ w := by rw [hw]; positivity
  -- `Y/k = 1 + w + w²/2`
  have hYk : Y / k = 1 + w + w ^ 2 / 2 := by
    have hs2 : Real.sqrt ((k : ℝ) * x) ^ 2 = (k : ℝ) * x := Real.sq_sqrt hkx
    have h : Y = k * (1 + w + w ^ 2 / 2) := by
      rw [hY, hw]
      field_simp
      nlinarith [hs2]
    rw [h, mul_div_cancel_left₀ _ (by positivity : (k : ℝ) ≠ 0)]
  -- `√(Y/k) ≤ exp (w/2)`
  have hsqrt_le : Real.sqrt (Y / k) ≤ Real.exp (w / 2) := by
    rw [hYk, Real.exp_half w]
    exact Real.sqrt_le_sqrt (Real.quadratic_le_exp_of_nonneg hw_nonneg)
  -- raise to the `k`-th power
  have hpow : Real.sqrt (Y / k) ^ k ≤ (Real.exp (w / 2)) ^ k :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le k
  -- `exp(w/2)^k = exp(√(kx))`
  have hexp : (Real.exp (w / 2)) ^ k = Real.exp (Real.sqrt ((k : ℝ) * x)) := by
    rw [← Real.exp_nat_mul, hsq]
    congr 1
    field_simp
  -- `exp(-(Y-k)/2) = exp(-(√(kx)+x))`
  have hYsub : -(Y - (k : ℝ)) / 2 = -(Real.sqrt ((k : ℝ) * x) + x) := by
    rw [hY]; ring
  rw [hexp] at hpow
  calc Real.sqrt (Y / k) ^ k * Real.exp (-(Y - (k : ℝ)) / 2)
      = Real.sqrt (Y / k) ^ k * Real.exp (-(Real.sqrt ((k : ℝ) * x) + x)) := by rw [hYsub]
    _ ≤ Real.exp (Real.sqrt ((k : ℝ) * x)) *
          Real.exp (-(Real.sqrt ((k : ℝ) * x) + x)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## 4. Union-bound inputs: elementary threshold algebra and support count -/

/-- `2√(ab) ≤ a + b` for `a, b ≥ 0`. -/
lemma two_mul_sqrt_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  rw [Real.sqrt_mul ha b]
  linarith

/-- **Threshold algebra.** For `s ≥ 1`, `L ≥ 1`, `L' ≥ 0`, the corrected threshold `5sL + 3L'`
dominates the Laurent–Massart threshold `s + 2√(s x) + 2x` at `x = sL + L'` (using
`2√(a b) ≤ a + b` and `2s ≤ 2sL`). -/
lemma threshold_alg {s : ℕ} (hs : 1 ≤ s) {L L' : ℝ} (hL : 1 ≤ L) (hL' : 0 ≤ L') :
    (s : ℝ) + 2 * Real.sqrt ((s : ℝ) * ((s : ℝ) * L + L')) + 2 * ((s : ℝ) * L + L')
      ≤ 5 * (s : ℝ) * L + 3 * L' := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hx : 0 ≤ (s : ℝ) * L + L' := by nlinarith
  have h : 2 * Real.sqrt ((s : ℝ) * ((s : ℝ) * L + L')) ≤ (s : ℝ) + ((s : ℝ) * L + L') :=
    two_mul_sqrt_mul_le hs'.le hx
  nlinarith

/-- Stirling lower bound: `(s/e)^s ≤ s!` for `s ≥ 1`. -/
lemma div_exp_pow_le_factorial {s : ℕ} (hs : 1 ≤ s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h := Stirling.le_factorial_stirling s
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three, hs']
  calc ((s : ℝ) / Real.exp 1) ^ s = 1 * ((s : ℝ) / Real.exp 1) ^ s := (one_mul _).symm
    _ ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) * ((s : ℝ) / Real.exp 1) ^ s :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (s.factorial : ℝ) := h

/-- **Support count.** For `1 ≤ s ≤ p`, the number `C(p,s)` of supports of size `s` is at most
`(e p / s)^s`: from `C(p,s) ≤ p^s/s!` and `s! ≥ (s/e)^s`. -/
lemma choose_le_exp_mul_div_pow {p s : ℕ} (hs : 1 ≤ s) :
    (p.choose s : ℝ) ≤ (Real.exp 1 * (p : ℝ) / s) ^ s := by
  have hfac : ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := div_exp_pow_le_factorial hs
  calc (p.choose s : ℝ) ≤ (p : ℝ) ^ s / (s.factorial : ℝ) := Nat.choose_le_pow_div s p
    _ ≤ (p : ℝ) ^ s / ((s : ℝ) / Real.exp 1) ^ s := by
        gcongr
    _ = (Real.exp 1 * (p : ℝ) / s) ^ s := by
        rw [← div_pow]
        congr 1
        field_simp

/-- **End-to-end per-support chi-square tail bound (standard Gaussian case).**

For `s ≥ 1`, `L ≥ 1`, `L' ≥ 0`, with the union-bound threshold `Y = 5sL + 3L'`,

`P(∑_{i<s} xᵢ² ≥ 5sL + 3L') ≤ e^{-(sL + L')}`

under the product of `s` standard Gaussian laws. Composed from the Chernoff bound
`measure_sum_sq_ge_le` (at the optimal `t`), the Laurent–Massart numerical inequality
`lm_sqrt_bound` and the threshold algebra `threshold_alg`. This is exactly the per-support
estimate required by the union bound in Theorem 1: with `δ₀ = e^{-L'}` and `C(p,s) ≤ e^{sL}`
(`choose_le_exp_mul_div_pow`, `L = log(ep/s)`), the total failure probability is at most
`e^{sL} · e^{-sL-L'} = δ₀`. -/
theorem chiSq_tail_bound {s : ℕ} (hs : 1 ≤ s) {L L' : ℝ} (hL : 1 ≤ L) (hL' : 0 ≤ L') :
    (Measure.pi (fun _ : Fin s => gaussianReal 0 (1 : ℝ≥0))).real
      {x : Fin s → ℝ | 5 * (s : ℝ) * L + 3 * L' ≤ ∑ i, x i ^ 2}
    ≤ Real.exp (-((s : ℝ) * L + L')) := by
  set Ylm : ℝ := (s : ℝ) + 2 * Real.sqrt ((s : ℝ) * ((s : ℝ) * L + L')) +
    2 * ((s : ℝ) * L + L') with hYlm
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hx0 : 0 ≤ (s : ℝ) * L + L' := by nlinarith
  have hYlmpos : 0 < Ylm := by
    rw [hYlm]
    have h := Real.sqrt_nonneg ((s : ℝ) * ((s : ℝ) * L + L'))
    linarith
  have hYle : Ylm ≤ 5 * (s : ℝ) * L + 3 * L' := by
    rw [hYlm]
    exact threshold_alg hs hL hL'
  -- monotonicity of the tail in the threshold
  have hmono : (Measure.pi (fun _ : Fin s => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin s → ℝ | 5 * (s : ℝ) * L + 3 * L' ≤ ∑ i, x i ^ 2}
      ≤ (Measure.pi (fun _ : Fin s => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin s → ℝ | Ylm ≤ ∑ i, x i ^ 2} := by
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    exact le_trans hYle hx
  -- Chernoff at the optimal exponent `t = (1 - s/Ylm)/2`
  have ht0 : 0 ≤ (1 - (s : ℝ) / Ylm) / 2 := by
    apply div_nonneg _ (by norm_num)
    rw [sub_nonneg, div_le_one hYlmpos, hYlm]
    have h := Real.sqrt_nonneg ((s : ℝ) * ((s : ℝ) * L + L'))
    linarith
  have ht1 : 2 * (1 : ℝ) * ((1 - (s : ℝ) / Ylm) / 2) < 1 := by
    have hp : 0 < (s : ℝ) / Ylm := div_pos hspos hYlmpos
    linarith
  have hchernoff := measure_sum_sq_ge_le (k := s) (v := 1) (by norm_num)
    (t := (1 - (s : ℝ) / Ylm) / 2) (y := Ylm) ht0 ht1
  have hsqrt_id : 1 / Real.sqrt (1 - 2 * (1 : ℝ) * ((1 - (s : ℝ) / Ylm) / 2)) =
      Real.sqrt (Ylm / (s : ℝ)) := by
    rw [show 1 - 2 * (1 : ℝ) * ((1 - (s : ℝ) / Ylm) / 2) = (s : ℝ) / Ylm by
      field_simp; ring]
    rw [one_div, ← inv_div (s : ℝ) Ylm, ← Real.sqrt_inv]
  have hty : -((1 - (s : ℝ) / Ylm) / 2) * Ylm = -(Ylm - (s : ℝ)) / 2 := by
    field_simp
  calc (Measure.pi (fun _ : Fin s => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin s → ℝ | 5 * (s : ℝ) * L + 3 * L' ≤ ∑ i, x i ^ 2}
      ≤ (Measure.pi (fun _ : Fin s => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin s → ℝ | Ylm ≤ ∑ i, x i ^ 2} := hmono
    _ ≤ Real.exp (-((1 - (s : ℝ) / Ylm) / 2) * Ylm) *
          (1 / Real.sqrt (1 - 2 * (1 : ℝ) * ((1 - (s : ℝ) / Ylm) / 2))) ^ s := hchernoff
    _ = Real.sqrt (Ylm / (s : ℝ)) ^ s * Real.exp (-(Ylm - (s : ℝ)) / 2) := by
        rw [hsqrt_id, hty]
        ring
    _ ≤ Real.exp (-((s : ℝ) * L + L')) := by
        have h := lm_sqrt_bound hs hx0
        rw [hYlm]
        exact h


/-! ## Inlined DS13 helpers: the `toE` embedding and the noise coordinate law -/


/-! ## Stage 1: `Fin n → ℝ` ↪ `EuclideanSpace ℝ (Fin n)` -/

/-- The identity-on-coordinates embedding of `Fin n → ℝ` into `EuclideanSpace ℝ (Fin n)`,
whose norm is the `l2` norm `Real.sqrt (∑ i, v i ^ 2)`. -/
abbrev toE {n : ℕ} (v : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v

@[simp] lemma toE_apply {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : toE v i = v i := rfl

@[simp] lemma toE_add {n : ℕ} (a b : Fin n → ℝ) : toE (a + b) = toE a + toE b := rfl

@[simp] lemma toE_smul {n : ℕ} (c : ℝ) (a : Fin n → ℝ) : toE (c • a) = c • toE a := rfl

/-- The `EuclideanSpace` norm squared is the sum of squares. -/
lemma norm_sq_toE {n : ℕ} (v : Fin n → ℝ) : ‖toE v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ => by rw [toE_apply, Real.norm_eq_abs, sq_abs]

lemma l2_eq_norm_toE {n : ℕ} (v : Fin n → ℝ) : l2 v = ‖toE v‖ := by
  rw [l2, ← Real.sqrt_sq (norm_nonneg (toE v)), norm_sq_toE]

lemma dot_eq_inner_toE {n : ℕ} (a b : Fin n → ℝ) : dot a b = ⟪toE a, toE b⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [dot, toE, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## Stage 2: sup over the support ≤ projection norm -/

/-- The "projection vector" `w = ∑ i, ⟪e i, x⟫ • e i` of `x` onto `span (range e)`. -/
def projVec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (e : Fin d → E) (x : E) : E :=
  ∑ i, ⟪e i, x⟫_ℝ • e i

/-- **Deterministic geometry.**  If `e` is orthonormal and `v ∈ span (range e)`, then
`⟪x, v⟫ ≤ ‖v‖ · ‖projVec e x‖`.  This is the Cauchy–Schwarz step
`⟪x,v⟫ = ⟪projVec e x, v⟫ ≤ ‖projVec e x‖ ‖v‖` used to bound the supremum over a
support by the norm of the projection of the noise. -/
theorem inner_le_norm_mul_norm_projVec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E} (he : Orthonormal ℝ e) (x v : E)
    (hv : v ∈ Submodule.span ℝ (Set.range e)) :
    ⟪x, v⟫_ℝ ≤ ‖v‖ * ‖projVec e x‖ := by
  classical
  have hgen : ∀ j : Fin d, ⟪x, e j⟫_ℝ = ⟪projVec e x, e j⟫_ℝ := by
    intro j
    rw [projVec, Orthonormal.inner_left_fintype he (fun i => ⟪e i, x⟫_ℝ) j,
      RCLike.conj_to_real, real_inner_comm]
  have key : ⟪x, v⟫_ℝ = ⟪projVec e x, v⟫_ℝ := by
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hgen j
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_right, inner_add_right, hu, hw]
    | smul c u _ hu => rw [inner_smul_right, inner_smul_right, hu]
  rw [key]
  calc ⟪projVec e x, v⟫_ℝ ≤ ‖projVec e x‖ * ‖v‖ := real_inner_le_norm _ _
    _ = ‖v‖ * ‖projVec e x‖ := mul_comm _ _

/-- The squared norm of `projVec e x` is the sum of squares of the coordinates. -/
theorem norm_projVec_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    {e : Fin d → E} (he : Orthonormal ℝ e) (x : E) :
    ‖projVec e x‖ ^ 2 = ∑ i, ⟪e i, x⟫_ℝ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, projVec]
  rw [Orthonormal.inner_sum he (fun i => ⟪e i, x⟫_ℝ) (fun i => ⟪e i, x⟫_ℝ) Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_to_real, sq]

/-! ## Stage 3: coordinates of the noise in an orthonormal basis -/

/-- `noiseLaw n σ` is the coordinatewise `σ`-scaling of the standard product Gaussian. -/
lemma noiseLaw_eq_map_scale (n : ℕ) (σ : ℝ) :
    noiseLaw n σ =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))).map (fun x i => σ * x i) := by
  have h : (Measure.pi (fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))).map
      (fun x i => σ * x i) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
    rw [Measure.pi_map_pi (f := fun _ (x : ℝ) => σ * x)]
    · congr 1
      funext i
      rw [gaussianReal_map_const_mul]
      simp only [mul_zero, mul_one]
      exact congrArg (gaussianReal 0) (Subtype.ext (by simp))
    · intro i
      fun_prop
  rw [h]
  rfl

lemma measurable_toE {n : ℕ} : Measurable (toE (n := n)) :=
  WithLp.measurable_toLp 2 (Fin n → ℝ)

/-- The inverse of `toE`: the `WithLp` equivalence back to coordinates. -/
abbrev ofE {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ := WithLp.equiv 2 (Fin n → ℝ) v

lemma measurable_ofE {n : ℕ} : Measurable (ofE (n := n)) :=
  WithLp.measurable_ofLp 2 (Fin n → ℝ)

@[simp] lemma ofE_toE {n : ℕ} (v : Fin n → ℝ) : ofE (toE v) = v := rfl

/-- **Coordinates in an orthonormal basis are distributed as the product Gaussian.**

For an orthonormal basis `b` of `EuclideanSpace ℝ (Fin n)`, the map sending `ε` to its
coordinates `(i ↦ ⟪b i, toE ε⟫)` in the basis `b` is law-preserving for `noiseLaw n σ`. -/
theorem noiseLaw_map_coords {n : ℕ} (σ : ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (noiseLaw n σ).map (fun ε => fun i => ⟪b i, toE ε⟫_ℝ) = noiseLaw n σ := by
  classical
  have hreb : Measurable b.repr := b.repr.continuous.measurable
  have htoE : Measurable (toE (n := n)) := measurable_toE
  have hcoords_meas : Measurable (fun ε : Fin n → ℝ => fun i => ⟪b i, toE ε⟫_ℝ) := by
    have hc : (fun ε : Fin n → ℝ => fun i => ⟪b i, toE ε⟫_ℝ) =
        ofE ∘ (b.repr ∘ toE) := by
      funext ε i; simp [ofE, OrthonormalBasis.repr_apply_apply]
    rw [hc]; exact measurable_ofE.comp (hreb.comp htoE)
  have hscale_meas : Measurable (fun x : Fin n → ℝ => fun i => σ * x i) := by fun_prop
  -- the coordinate map is law-preserving for the standard product Gaussian
  have hA : Measure.map (b.repr ∘ toE)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [← Measure.map_map (hg := hreb) (hf := htoE), map_pi_eq_stdGaussian (ι := Fin n)]
    exact stdGaussian_map b.repr
  have hB : Measure.map (ofE (n := n)) (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0)) := by
    rw [← map_pi_eq_stdGaussian (ι := Fin n),
      Measure.map_map (hg := measurable_ofE) (hf := htoE)]
    have hid : (ofE (n := n)) ∘ (toE (n := n)) = id := by funext x; rfl
    rw [hid, Measure.map_id]
  have hg : Measure.map (fun ε : Fin n → ℝ => fun i => ⟪b i, toE ε⟫_ℝ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0)) := by
    have hc : (fun ε : Fin n → ℝ => fun i => ⟪b i, toE ε⟫_ℝ) =
        ofE ∘ (b.repr ∘ toE) := by
      funext ε i; simp [ofE, OrthonormalBasis.repr_apply_apply]
    rw [hc, ← Measure.map_map (hg := measurable_ofE) (hf := hreb.comp htoE), hA, hB]
  rw [noiseLaw_eq_map_scale n σ, Measure.map_map (hg := hcoords_meas) (hf := hscale_meas)]
  have hcomp : ((fun ε => fun i => ⟪b i, toE ε⟫_ℝ) ∘ (fun x : Fin n → ℝ => fun i => σ * x i)) =
      ((fun y : Fin n → ℝ => fun i => σ * y i) ∘ (fun ε => fun i => ⟪b i, toE ε⟫_ℝ)) := by
    funext x i
    simp only [Function.comp_apply]
    rw [show (fun i => σ * x i) = σ • x from rfl, toE_smul, real_inner_smul_right]
  rw [hcomp, ← Measure.map_map (hg := hscale_meas) (hf := hcoords_meas), hg]


/-! ## Inlined DS19A helpers: projection geometry, law, union bound -/


/-! ## Stage A.1: generic orthogonal-projection geometry -/

/-- The orthogonal projection of `x` onto `span (range e)`, written as an explicit finite sum
(`e` orthonormal). -/
def projF {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    [Fintype ι] (e : ι → E) (x : E) : E :=
  ∑ i, ⟪e i, x⟫_ℝ • e i

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι] {e : ι → E} {x : E} {t : ℝ}

lemma projF_mem_span (e : ι → E) (x : E) :
    projF e x ∈ Submodule.span ℝ (Set.range e) := by
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Coordinates of the projection: for `v` in the span, `⟪projF e x, v⟫ = ⟪x, v⟫`. -/
lemma inner_projF_eq (he : Orthonormal ℝ e) {v : E}
    (hv : v ∈ Submodule.span ℝ (Set.range e)) :
    ⟪projF e x, v⟫_ℝ = ⟪x, v⟫_ℝ := by
  classical
  have hgen : ∀ j : ι, ⟪projF e x, e j⟫_ℝ = ⟪x, e j⟫_ℝ := by
    intro j
    rw [projF, Orthonormal.inner_left_fintype he (fun i => ⟪e i, x⟫_ℝ) j,
      RCLike.conj_to_real, real_inner_comm]
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hgen j
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_right, inner_add_right, hu, hw]
  | smul c u _ hu => rw [inner_smul_right, inner_smul_right, hu]

/-- The squared norm of the projection is the sum of the squared coordinates. -/
lemma norm_projF_sq (he : Orthonormal ℝ e) (x : E) :
    ‖projF e x‖ ^ 2 = ∑ i, (⟪e i, x⟫_ℝ) ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, projF]
  rw [Orthonormal.inner_sum he (fun i => ⟪e i, x⟫_ℝ) (fun i => ⟪e i, x⟫_ℝ) Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_to_real, sq]

/-- **One direction of the sup/projection-norm identification.**  If the inequality
`⟪x, v⟫ ≤ t ‖v‖` holds on the whole span, then `‖projection‖ ≤ t`. -/
lemma norm_projF_le_of_forall_inner_le (he : Orthonormal ℝ e) (ht : 0 ≤ t)
    (h : ∀ v ∈ Submodule.span ℝ (Set.range e), ⟪x, v⟫_ℝ ≤ t * ‖v‖) :
    ‖projF e x‖ ≤ t := by
  have hmem := projF_mem_span e x
  have h1 : ⟪x, projF e x⟫_ℝ ≤ t * ‖projF e x‖ := h _ hmem
  rw [← inner_projF_eq he hmem, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖projF e x‖ * ‖projF e x‖ ≤ t * ‖projF e x‖ := by
    rw [sq] at h1; exact h1
  have hn : 0 ≤ ‖projF e x‖ := norm_nonneg _
  rcases eq_or_lt_of_le hn with h0 | hpos
  · rw [← h0]; exact ht
  · exact le_of_mul_le_mul_right h2 hpos

/-- **The other direction.**  `‖projection‖ ≤ t` implies the inequality on the span. -/
lemma forall_inner_le_of_norm_projF_le (he : Orthonormal ℝ e)
    (h : ‖projF e x‖ ≤ t) :
    ∀ v ∈ Submodule.span ℝ (Set.range e), ⟪x, v⟫_ℝ ≤ t * ‖v‖ := by
  intro v hv
  rw [← inner_projF_eq he hv]
  calc ⟪projF e x, v⟫_ℝ ≤ ‖projF e x‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ t * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-! ## Stage A.2: the column span of a support -/

variable {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)

/-- The subspace of `ℝⁿ` spanned by the columns of `X` indexed by the finset `S`. -/
def KS (S : Finset (Fin p)) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range (fun j : S => toE (X.col (j : Fin p))))

/-- The set of vectors `X u` with `u` supported in `S`, as a submodule. -/
def TS (S : Finset (Fin p)) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {v | ∃ u : Fin p → ℝ, (∀ j, j ∉ S → u j = 0) ∧ toE (X.mulVec u) = v}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro v w ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    refine ⟨u + u', ?_, ?_⟩
    · intro j hj
      simp [hu j hj, hu' j hj]
    · rw [Matrix.mulVec_add, toE_add]
  smul_mem' := by
    rintro c v ⟨u, hu, rfl⟩
    refine ⟨c • u, ?_, ?_⟩
    · intro j hj
      simp [hu j hj]
    · rw [Matrix.mulVec_smul, toE_smul]

lemma toE_sum_univ {ι : Type*} [Fintype ι] (f : ι → Fin n → ℝ) :
    toE (∑ i, f i) = ∑ i, toE (f i) := by
  simp [toE]

lemma toE_mulVec_eq_sum (S : Finset (Fin p)) (u : Fin p → ℝ)
    (hu : ∀ j, j ∉ S → u j = 0) :
    toE (X.mulVec u) = ∑ j ∈ S, u j • toE (X.col j) := by
  have h1 : X.mulVec u = ∑ j, u j • X.col j := by
    funext i
    simp only [Matrix.mulVec, Matrix.col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h1, toE_sum_univ]
  simp only [toE_smul]
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  intro j _ hj
  simp [hu j hj]

lemma KS_le_TS (S : Finset (Fin p)) : KS X S ≤ TS X S := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨j, rfl⟩
  refine ⟨Pi.single (j : Fin p) 1, ?_, ?_⟩
  · intro k hk
    have hjk : (j : Fin p) ≠ k := fun h => hk (h ▸ j.2)
    simp [Pi.single_eq_of_ne' hjk]
  · rw [Matrix.mulVec_single_one]

lemma TS_le_KS (S : Finset (Fin p)) : TS X S ≤ KS X S := by
  rintro v ⟨u, hu, rfl⟩
  rw [toE_mulVec_eq_sum X S u hu]
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

/-- Exact description of the column span: `v ∈ KS X S` iff `v = X u` for some `u`
vanishing off `S`. -/
lemma mem_KS_iff (S : Finset (Fin p)) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ KS X S ↔ ∃ u : Fin p → ℝ, (∀ j, j ∉ S → u j = 0) ∧ toE (X.mulVec u) = v := by
  constructor
  · intro hv
    exact KS_le_TS X S hv
  · intro hv
    exact TS_le_KS X S hv

/-! ## Stage A.3: an orthonormal basis of the column span -/

/-- An orthonormal basis of `KS X S`, pushed into `ℝⁿ`. -/
def eS (S : Finset (Fin p)) : Fin (Module.finrank ℝ (KS X S)) → EuclideanSpace ℝ (Fin n) :=
  fun i => ((stdOrthonormalBasis ℝ (KS X S)) i : EuclideanSpace ℝ (Fin n))

lemma orthonormal_eS (S : Finset (Fin p)) : Orthonormal ℝ (eS X S) := by
  rw [orthonormal_iff_ite]
  intro i j
  show ⟪((stdOrthonormalBasis ℝ (KS X S) i : KS X S) : EuclideanSpace ℝ (Fin n)),
        ((stdOrthonormalBasis ℝ (KS X S) j : KS X S) : EuclideanSpace ℝ (Fin n))⟫_ℝ = _
  rw [← Submodule.coe_inner]
  exact orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (KS X S)).orthonormal i j

lemma span_eS (S : Finset (Fin p)) :
    Submodule.span ℝ (Set.range (eS X S)) = KS X S := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (stdOrthonormalBasis ℝ (KS X S) i).2
  · intro y hy
    let y' : KS X S := ⟨y, hy⟩
    have hrepr := (stdOrthonormalBasis ℝ (KS X S)).sum_repr y'
    have hcoe : ∑ i, (stdOrthonormalBasis ℝ (KS X S)).repr y' i • eS X S i = y := by
      have := congrArg (Subtype.val) hrepr
      simpa [eS] using this
    rw [← hcoe]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ## Stage A.4: the per-support event is a projection-norm sublevel set -/

/-- The per-support event `{ε | ∀ u supported in S, εᵀXu ≤ t ‖Xu‖}`. -/
def BS (t : ℝ) (S : Finset (Fin p)) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ, (∀ j, j ∉ S → u j = 0) →
    dot ε (X.mulVec u) ≤ t * l2 (X.mulVec u)}

/-- The per-support event equals the sublevel set of the projection norm
`{ε | ‖P_{KS} ε‖ ≤ t}`. -/
theorem BS_eq_norm (S : Finset (Fin p)) {t : ℝ} (ht : 0 ≤ t) :
    BS X t S = {ε : Fin n → ℝ | ‖projF (eS X S) (toE ε)‖ ≤ t} := by
  ext ε
  constructor
  · intro h
    refine norm_projF_le_of_forall_inner_le (orthonormal_eS X S) ht ?_
    intro v hv
    rw [span_eS X S] at hv
    obtain ⟨u, hu, rfl⟩ := (mem_KS_iff X S v).mp hv
    have h' := h u hu
    rw [dot_eq_inner_toE, l2_eq_norm_toE] at h'
    exact h'
  · intro h u hu
    rw [dot_eq_inner_toE, l2_eq_norm_toE]
    exact forall_inner_le_of_norm_projF_le (orthonormal_eS X S) h _
      (by rw [span_eS X S]; exact (mem_KS_iff X S _).mpr ⟨u, hu, rfl⟩)

/-! ## Stage A.5: support bookkeeping -/

/-- The intersection, over all supports `S` of cardinality `s`, of the per-support events equals
the corrected event. -/
theorem Gc_eq_set {σ δ0 : ℝ} {s : ℕ} (hσ : 0 < σ) (hsp : s ≤ p) :
    Gc X σ δ0 s = {ε : Fin n → ℝ | ∀ S ∈ Finset.univ.powersetCard s,
      ‖projF (eS X S) (toE ε)‖ ≤ σ * Real.sqrt (5 * (s : ℝ) *
        Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0))} := by
  ext ε
  constructor
  · intro hε S hS
    have hmem : ε ∈ BS X (σ * Real.sqrt (5 * (s : ℝ) *
        Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0))) S := by
      intro u hu
      have hScard : S.card = s := (Finset.mem_powersetCard.mp hS).2
      have hsupp : l0 u ≤ s := by
        rw [l0]
        refine le_trans (Finset.card_le_card ?_) (le_of_eq hScard)
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_contra hjn
        exact hj (hu j hjn)
      exact hε u hsupp
    rw [BS_eq_norm X S (by positivity)] at hmem
    exact hmem
  · intro hε u hu
    have hcard : (Finset.univ.filter (fun j : Fin p => u j ≠ 0)).card ≤ s := by
      rw [← l0]; exact hu
    obtain ⟨S, hsub, -, hScard⟩ :=
      Finset.exists_subsuperset_card_eq (s := Finset.univ.filter (fun j : Fin p => u j ≠ 0))
        (t := (Finset.univ : Finset (Fin p))) (Finset.subset_univ _) hcard
        (by simpa using hsp)
    have hS : S ∈ Finset.univ.powersetCard s :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩
    have hzero : ∀ j, j ∉ S → u j = 0 := by
      intro j hj
      by_contra hne
      exact absurd (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)) hj
    have hmem : ε ∈ BS X (σ * Real.sqrt (5 * (s : ℝ) *
        Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0))) S := by
      rw [BS_eq_norm X S (by positivity)]
      exact hε S hS
    exact hmem u hzero


/-! ## Stage B: measurability and the law of coordinates in an orthonormal family -/

/-- `σ²` packaged as an `ℝ≥0`. -/
def varNN (σ : ℝ) : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩

@[simp] lemma varNN_coe (σ : ℝ) : (varNN σ : ℝ) = σ ^ 2 := rfl

/-- Restriction of a product Gaussian to an injective subfamily of coordinates is again the
product Gaussian. -/
lemma map_pi_restrict {d n : ℕ} (σ : ℝ) (f : Fin d → Fin n) (hf : Function.Injective f) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 (varNN σ))).map
        (fun y : Fin n → ℝ => fun i : Fin d => y (f i))
      = Measure.pi (fun _ : Fin d => gaussianReal 0 (varNN σ)) := by
  classical
  have hg : Measurable (fun y : Fin n → ℝ => fun i : Fin d => y (f i)) := by fun_prop
  refine (Measure.pi_eq (μ := fun _ : Fin d => gaussianReal 0 (varNN σ)) (fun s hs => ?_)).symm
  rw [Measure.map_apply hg (MeasurableSet.univ_pi hs)]
  set t : Fin n → Set ℝ := fun j =>
    if h : ∃ i, f i = j then s (Classical.choose h) else Set.univ with ht
  have hti : ∀ i : Fin d, t (f i) = s i := by
    intro i
    have hex : ∃ i' : Fin d, f i' = f i := ⟨i, rfl⟩
    change (if h : ∃ i' : Fin d, f i' = f i then s (Classical.choose h) else Set.univ) = s i
    rw [dif_pos hex, hf (Classical.choose_spec hex)]
  have hpre : (fun y : Fin n → ℝ => fun i : Fin d => y (f i)) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi t := by
    ext y
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hy j
      by_cases h : ∃ i', f i' = j
      · obtain ⟨i, hi⟩ := h
        have htj : t j = s i := by
          rw [ht]
          change (if h' : ∃ i' : Fin d, f i' = j then s (Classical.choose h') else Set.univ) = s i
          rw [dif_pos (⟨i, hi⟩ : ∃ i' : Fin d, f i' = j)]
          have hch : Classical.choose (⟨i, hi⟩ : ∃ i' : Fin d, f i' = j) = i :=
            hf (by rw [Classical.choose_spec (⟨i, hi⟩ : ∃ i' : Fin d, f i' = j), hi])
          rw [hch]
        rw [htj, ← hi]
        exact hy i
      · have htj : t j = Set.univ := by rw [ht]; exact dif_neg h
        rw [htj]; exact Set.mem_univ _
    · intro hy i
      have hfi := hy (f i)
      rw [hti i] at hfi
      exact hfi
  rw [hpre, Measure.pi_pi]
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ∉ Finset.univ.image f →
      gaussianReal 0 (varNN σ) (t j) = 1 := by
    intro j _ hj
    have hnot : ¬ ∃ i, f i = j := fun h =>
      hj (Finset.mem_image.mpr ⟨Classical.choose h, Finset.mem_univ _, Classical.choose_spec h⟩)
    have htuniv : t j = Set.univ := by rw [ht]; exact dif_neg hnot
    rw [htuniv, measure_univ]
  have h1 : (∏ j : Fin n, gaussianReal 0 (varNN σ) (t j))
      = ∏ j ∈ (Finset.univ.image f), gaussianReal 0 (varNN σ) (t j) :=
    (Finset.prod_subset (Finset.subset_univ _) hzero).symm
  rw [h1]
  rw [Finset.prod_image (s := (Finset.univ : Finset (Fin d))) (g := f)
    (f := fun j => gaussianReal 0 (varNN σ) (t j))
    (fun x _ y _ hxy => hf hxy)]
  exact Finset.prod_congr rfl fun i _ => by rw [hti i]

/-- **Coordinates of the noise in an orthonormal family.**
If `e : Fin d → ℝⁿ` is orthonormal, then the coordinates `ε ↦ (⟪e i, ε⟫)_i` of the noise have
the product Gaussian law `N(0,σ²)^{⊗d}`. -/
theorem noiseLaw_map_coords_family {d n : ℕ} (hdn : d ≤ n) (σ : ℝ)
    (e : Fin d → EuclideanSpace ℝ (Fin n)) (he : Orthonormal ℝ e) :
    (noiseLaw n σ).map (fun ε : Fin n → ℝ => fun i : Fin d => ⟪e i, toE ε⟫_ℝ)
      = Measure.pi (fun _ : Fin d => gaussianReal 0 (varNN σ)) := by
  classical
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  set v : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => if h : (i : ℕ) < d then e ⟨(i : ℕ), h⟩ else 0 with hv
  have horth : Orthonormal ℝ (Set.domRestrict {i : Fin n | (i : ℕ) < d} v) := by
    have hcomp : Set.domRestrict {i : Fin n | (i : ℕ) < d} v =
        (fun i : {i : Fin n // (i : ℕ) < d} => e ⟨((i : Fin n) : ℕ), i.2⟩) := by
      funext i
      simp only [Set.domRestrict, hv]
      split_ifs with h
      · rfl
      · exact absurd i.2 h
    rw [hcomp]
    refine he.comp (fun i : {i : Fin n // (i : ℕ) < d} => ⟨((i : Fin n) : ℕ), i.2⟩) ?_
    intro i j hij
    apply Subtype.ext
    exact Fin.ext (congrArg (fun k : Fin d => (k : ℕ)) hij)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) hcard horth
  have hbapply : ∀ i : Fin d, b (Fin.castLE hdn i) = e i := by
    intro i
    have hmem : Fin.castLE hdn i ∈ {i : Fin n | (i : ℕ) < d} := by simp
    rw [hb _ hmem]
    simp [hv]
  have hfun : (fun ε : Fin n → ℝ => fun i : Fin d => ⟪e i, toE ε⟫_ℝ) =
      (fun y : Fin n → ℝ => fun i : Fin d => y (Fin.castLE hdn i)) ∘
        (fun ε : Fin n → ℝ => fun j : Fin n => ⟪b j, toE ε⟫_ℝ) := by
    funext ε i
    simp only [Function.comp_apply, hbapply i]
  rw [hfun, ← Measure.map_map]
  · rw [noiseLaw_map_coords σ b]
    exact map_pi_restrict σ (Fin.castLE hdn) (Fin.castLE_injective hdn)
  · fun_prop
  · fun_prop

/-- **`d ≤ s` chi-square tail.**  The threshold valid at `s` degrees of freedom also controls a
`d`-degree sum of squares, with the correspondingly smaller exponent. -/
lemma chiSq_tail_dof_le {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) {L L' : ℝ}
    (hL : 1 ≤ L) (hL' : 0 ≤ L') :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).real
      {x : Fin d → ℝ | 5 * (s : ℝ) * L + 3 * L' < ∑ i, x i ^ 2}
    ≤ Real.exp (-((s : ℝ) * L + L')) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hds' : (d : ℝ) ≤ s := by exact_mod_cast hds
  set x0 : ℝ := (s : ℝ) * L + L' with hx0def
  have hx0 : 0 ≤ x0 := by rw [hx0def]; nlinarith
  set Y : ℝ := (d : ℝ) + 2 * Real.sqrt ((d : ℝ) * x0) + 2 * x0 with hY
  have hYpos : 0 < Y := by
    rw [hY]
    have h := Real.sqrt_nonneg ((d : ℝ) * x0)
    linarith
  -- the `d`-dof Laurent–Massart threshold is below the union-bound threshold
  have hYle : Y ≤ 5 * (s : ℝ) * L + 3 * L' := by
    rw [hY, hx0def]
    have h : 2 * Real.sqrt ((d : ℝ) * ((s : ℝ) * L + L')) ≤ (d : ℝ) + ((s : ℝ) * L + L') :=
      two_mul_sqrt_mul_le hd'.le hx0
    have hdL : (d : ℝ) ≤ (s : ℝ) * L := by nlinarith
    nlinarith
  have hmono : (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin d → ℝ | 5 * (s : ℝ) * L + 3 * L' < ∑ i, x i ^ 2}
      ≤ (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin d → ℝ | Y ≤ ∑ i, x i ^ 2} := by
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    exact le_of_lt (lt_of_le_of_lt hYle hx)
  -- Chernoff at the optimal exponent `t = (1 - d/Y)/2`
  have ht0 : 0 ≤ (1 - (d : ℝ) / Y) / 2 := by
    apply div_nonneg _ (by norm_num)
    rw [sub_nonneg, div_le_one hYpos]
    rw [hY]
    have h := Real.sqrt_nonneg ((d : ℝ) * x0)
    linarith
  have ht1 : 2 * (1 : ℝ) * ((1 - (d : ℝ) / Y) / 2) < 1 := by
    have hp : 0 < (d : ℝ) / Y := div_pos hd' hYpos
    linarith
  have hchernoff := measure_sum_sq_ge_le (k := d) (v := 1) (by norm_num)
    (t := (1 - (d : ℝ) / Y) / 2) (y := Y) ht0 ht1
  have hsqrt_id : 1 / Real.sqrt (1 - 2 * (1 : ℝ) * ((1 - (d : ℝ) / Y) / 2)) =
      Real.sqrt (Y / (d : ℝ)) := by
    rw [show 1 - 2 * (1 : ℝ) * ((1 - (d : ℝ) / Y) / 2) = (d : ℝ) / Y by
      field_simp; ring]
    rw [one_div, ← inv_div (d : ℝ) Y, ← Real.sqrt_inv]
  have hty : -((1 - (d : ℝ) / Y) / 2) * Y = -(Y - (d : ℝ)) / 2 := by
    field_simp
  calc (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin d → ℝ | 5 * (s : ℝ) * L + 3 * L' < ∑ i, x i ^ 2}
      ≤ (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).real
        {x : Fin d → ℝ | Y ≤ ∑ i, x i ^ 2} := hmono
    _ ≤ Real.exp (-((1 - (d : ℝ) / Y) / 2) * Y) *
          (1 / Real.sqrt (1 - 2 * (1 : ℝ) * ((1 - (d : ℝ) / Y) / 2))) ^ d := hchernoff
    _ = Real.sqrt (Y / (d : ℝ)) ^ d * Real.exp (-(Y - (d : ℝ)) / 2) := by
        rw [hsqrt_id, hty]
        ring
    _ ≤ Real.exp (-x0) := by
        simpa [hY] using lm_sqrt_bound (k := d) hd hx0
    _ = Real.exp (-((s : ℝ) * L + L')) := by rw [hx0def]

/-- **Per-support failure probability.**

For a support `S` of cardinality `s`, the complement of the projection event
`{ε | ‖P_{KS} ε‖ ≤ σ √(5 s L + 3 L')}` has noise probability at most `e^{-(sL+L')}`,
where `L = log (e p / s)` and `L' = log (1/δ₀)`.

This is the per-support estimate of §B.1: the projection of the noise on `K_S` is a
`σ χ` variable with `d = finrank K_S ≤ s` degrees of freedom, and the Laurent–Massart
tail bound (at the `d`-dof optimal exponent) gives `e^{-(sL+L')}`. -/
theorem measureReal_compl_BS_le {σ δ0 : ℝ} {s : ℕ} (hX : UnitCols X) (hσ : 0 < σ)
    (hs : 1 ≤ s) (hsp : s ≤ p) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) {S : Finset (Fin p)}
    (hScard : S.card = s) :
    (noiseLaw n σ).real {ε : Fin n → ℝ | ¬ ‖projF (eS X S) (toE ε)‖ ≤
        σ * Real.sqrt (5 * (s : ℝ) * Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0))}
      ≤ Real.exp (-((s : ℝ) * Real.log (Real.exp 1 * p / s) + Real.log (1 / δ0))) := by
  classical
  set L : ℝ := Real.log (Real.exp 1 * (p : ℝ) / s) with hLdef
  set L' : ℝ := Real.log (1 / δ0) with hL'def
  have hspos : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hs
  have hL : 1 ≤ L := by
    rw [hLdef]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) / s := by
      rw [le_div_iff₀ hspos]
      simpa using (show ((s : ℝ) ≤ (p : ℝ)) from by exact_mod_cast hsp)
    have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]; norm_num
    have h2 : Real.exp 1 ≤ Real.exp 1 * (p : ℝ) / s := by
      calc Real.exp 1 = Real.exp 1 * 1 := (mul_one _).symm
        _ ≤ Real.exp 1 * ((p : ℝ) / s) := by gcongr
        _ = Real.exp 1 * (p : ℝ) / s := by ring
    have hlog := Real.log_le_log (Real.exp_pos 1) h2
    simpa [Real.log_exp] using hlog
  have hL' : 0 ≤ L' := by
    rw [hL'def]
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ0]
    linarith
  set d : ℕ := Module.finrank ℝ (KS X S) with hddef
  set f : (Fin n → ℝ) → (Fin d → ℝ) := fun ε i => ⟪eS X S i, toE ε⟫_ℝ with hfdef
  -- `d ≤ n`, `d ≤ s`, `1 ≤ d`
  have hdn : d ≤ n := by
    rw [hddef]
    have h := Submodule.finrank_le (R := ℝ) (M := EuclideanSpace ℝ (Fin n)) (KS X S)
    simpa using h
  have hds : d ≤ s := by
    have h1 : Module.finrank ℝ (KS X S) ≤ Fintype.card S :=
      finrank_range_le_card (R := ℝ) (M := EuclideanSpace ℝ (Fin n))
        (b := fun j : S => toE (X.col (j : Fin p)))
    rw [hddef, ← hScard]
    simpa using h1
  have hdpos : 1 ≤ d := by
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hjS⟩ := hSne
    have hmem : toE (X.col j) ∈ KS X S := by
      rw [KS]
      exact Submodule.subset_span ⟨⟨j, hjS⟩, rfl⟩
    have hne : toE (X.col j) ≠ 0 := by
      intro hzero
      have h1 : ‖toE (X.col j)‖ = 1 := by
        rw [← l2_eq_norm_toE, l2, show (∑ i, X.col j i ^ 2) = 1 by
          simpa [Matrix.col] using hX j, Real.sqrt_one]
      rw [hzero, norm_zero] at h1
      exact zero_ne_one h1
    have hpos : 0 < Module.finrank ℝ (KS X S) := by
      refine (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := KS X S)).mpr
        ⟨⟨toE (X.col j), hmem⟩, ?_⟩
      intro h
      exact hne (congrArg Subtype.val h)
    rw [hddef]; omega
  -- law of the coordinates, and measurability
  have hlaw : (noiseLaw n σ).map f = Measure.pi (fun _ : Fin d => gaussianReal 0 (varNN σ)) := by
    have h := noiseLaw_map_coords_family (d := Module.finrank ℝ (KS X S))
      (by simpa [hddef] using hdn) σ (eS X S) (orthonormal_eS X S)
    simpa [hddef, hfdef] using h
  have hf_meas : Measurable f := by
    rw [hfdef]
    exact measurable_pi_iff.mpr fun i => measurable_const.inner measurable_toE
  -- the complement event is a coordinate tail event
  have hset : {ε : Fin n → ℝ | ¬ ‖projF (eS X S) (toE ε)‖ ≤
        σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')}
      = f ⁻¹' {y : Fin d → ℝ |
          (σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')) ^ 2 < ∑ i, y i ^ 2} := by
    ext ε
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have hT0 : 0 ≤ σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L') := by positivity
    rw [← norm_projF_sq (orthonormal_eS X S) (toE ε)]
    constructor
    · intro h
      rw [not_le] at h
      rwa [sq_lt_sq, abs_of_nonneg hT0, abs_of_nonneg (norm_nonneg _)]
    · intro h
      rw [not_le]
      rwa [sq_lt_sq, abs_of_nonneg hT0, abs_of_nonneg (norm_nonneg _)] at h
  have hB : MeasurableSet {y : Fin d → ℝ |
      (σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')) ^ 2 < ∑ i, y i ^ 2} := by
    measurability
  rw [hset]
  have hLHS : (noiseLaw n σ).real (f ⁻¹' {y : Fin d → ℝ |
        (σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')) ^ 2 < ∑ i, y i ^ 2})
      = (Measure.pi (fun _ : Fin d => gaussianReal 0 (varNN σ))).real
        {y : Fin d → ℝ | (σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')) ^ 2 < ∑ i, y i ^ 2} := by
    rw [← map_measureReal_apply hf_meas hB, hlaw]
  rw [hLHS]
  -- push the `σ`-scaling into the product Gaussian
  have hscale : Measure.pi (fun _ : Fin d => gaussianReal 0 (varNN σ)) =
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).map
        (fun z : Fin d → ℝ => fun i => σ * z i) := by
    have h : (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 : ℝ≥0))).map
        (fun z : Fin d → ℝ => fun i => σ * z i) =
        Measure.pi (fun _ : Fin d => gaussianReal 0 (varNN σ)) := by
      rw [Measure.pi_map_pi (f := fun _ (x : ℝ) => σ * x)]
      · congr 1
        funext i
        rw [gaussianReal_map_const_mul]
        simp only [mul_zero, mul_one]
        exact congrArg (gaussianReal 0) (Subtype.ext (by simp [varNN]))
      · intro i
        fun_prop
    exact h.symm
  rw [hscale]
  have hg_meas : Measurable (fun z : Fin d → ℝ => fun i => σ * z i) := by fun_prop
  rw [map_measureReal_apply hg_meas hB]
  have hT2 : (σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')) ^ 2 =
      σ ^ 2 * (5 * (s : ℝ) * L + 3 * L') := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hset2 : (fun z : Fin d → ℝ => fun i => σ * z i) ⁻¹'
      {y : Fin d → ℝ | (σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')) ^ 2 < ∑ i, y i ^ 2}
      = {z : Fin d → ℝ | 5 * (s : ℝ) * L + 3 * L' < ∑ i, z i ^ 2} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hT2]
    rw [show (∑ i : Fin d, (σ * z i) ^ 2) = σ ^ 2 * ∑ i, z i ^ 2 by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    constructor
    · intro h
      exact (mul_lt_mul_iff_right₀ (by positivity : (0 : ℝ) < σ ^ 2)).mp h
    · intro h
      exact (mul_lt_mul_iff_right₀ (by positivity : (0 : ℝ) < σ ^ 2)).mpr h
  rw [hset2]
  exact chiSq_tail_dof_le hdpos hds hL hL'

/-- Measurability of the corrected event. -/
theorem measurableSet_Gc {σ δ0 : ℝ} {s : ℕ} (hσ : 0 < σ) (hsp : s ≤ p) :
    MeasurableSet (Gc X σ δ0 s) := by
  rw [Gc_eq_set X hσ hsp]
  have hset : {ε : Fin n → ℝ | ∀ S ∈ Finset.univ.powersetCard s,
      ‖projF (eS X S) (toE ε)‖ ≤ σ * Real.sqrt (5 * (s : ℝ) *
        Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0))}
      = ⋂ S ∈ Finset.univ.powersetCard s,
        {ε : Fin n → ℝ | ‖projF (eS X S) (toE ε)‖ ≤ σ * Real.sqrt (5 * (s : ℝ) *
          Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0))} := by
    ext ε
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  refine Finset.measurableSet_biInter _ (fun S _ => ?_)
  have hcont : Continuous fun ε : Fin n → ℝ => projF (eS X S) (toE ε) := by
    unfold projF
    fun_prop
  exact measurableSet_le hcont.norm.measurable measurable_const

/-! ## Stage C: union bound and the corrected event -/

/-- **Union bound.** The failure probability of the corrected event is at most `δ₀`. -/
theorem measureReal_compl_Gc_le {σ δ0 : ℝ} {s : ℕ} (hX : UnitCols X) (hσ : 0 < σ)
    (hs : 1 ≤ s) (hsp : s ≤ p) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    (noiseLaw n σ).real (Gc X σ δ0 s)ᶜ ≤ δ0 := by
  classical
  haveI : IsProbabilityMeasure (noiseLaw n σ) := by
    unfold noiseLaw
    haveI : ∀ i : Fin n, IsProbabilityMeasure (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
      fun _ => instIsProbabilityMeasureGaussianReal 0 _
    infer_instance
  set L : ℝ := Real.log (Real.exp 1 * (p : ℝ) / s) with hLdef
  set L' : ℝ := Real.log (1 / δ0) with hL'def
  set A : Finset (Fin p) → Set (Fin n → ℝ) := fun S =>
    {ε : Fin n → ℝ | ‖projF (eS X S) (toE ε)‖ ≤
      σ * Real.sqrt (5 * (s : ℝ) * L + 3 * L')} with hA
  have hsub : (Gc X σ δ0 s)ᶜ ⊆ ⋃ S ∈ Finset.univ.powersetCard s, (A S)ᶜ := by
    intro ε hε
    rw [Gc_eq_set X hσ hsp] at hε
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hε
    push_neg at hε
    obtain ⟨S, hS, hSε⟩ := hε
    refine Set.mem_biUnion hS ?_
    simpa only [hA, hLdef, hL'def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hSε
  have hUnion : (noiseLaw n σ).real (Gc X σ δ0 s)ᶜ
      ≤ (noiseLaw n σ).real (⋃ S ∈ Finset.univ.powersetCard s, (A S)ᶜ) :=
    measureReal_mono hsub (measure_ne_top (noiseLaw n σ) _)
  refine hUnion.trans ?_
  refine (measureReal_biUnion_finset_le (Finset.univ.powersetCard s) (fun S => (A S)ᶜ)).trans ?_
  have hper : ∀ S ∈ Finset.univ.powersetCard s,
      (noiseLaw n σ).real ((A S)ᶜ) ≤ Real.exp (-((s : ℝ) * L + L')) := by
    intro S hS
    simpa only [hA, hLdef, hL'def, Set.compl_setOf] using
      measureReal_compl_BS_le X hX hσ hs hsp hδ0 hδ1 (Finset.mem_powersetCard.mp hS).2
  refine (Finset.sum_le_sum hper).trans ?_
  have hcard : ((Finset.univ : Finset (Fin p)).powersetCard s).card = p.choose s := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hppos : (0 : ℝ) < p := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans hs hsp)
  have hxpos : 0 < Real.exp 1 * (p : ℝ) / s := by positivity
  have hpow : (Real.exp 1 * (p : ℝ) / s) ^ s = Real.exp ((s : ℝ) * L) := by
    rw [← Real.exp_log hxpos, ← Real.exp_nat_mul]
  calc ∑ S ∈ (Finset.univ : Finset (Fin p)).powersetCard s, Real.exp (-((s : ℝ) * L + L'))
      = (((Finset.univ : Finset (Fin p)).powersetCard s).card : ℝ) *
          Real.exp (-((s : ℝ) * L + L')) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (p.choose s : ℝ) * Real.exp (-((s : ℝ) * L + L')) := by rw [hcard]
    _ ≤ (Real.exp 1 * (p : ℝ) / s) ^ s * Real.exp (-((s : ℝ) * L + L')) := by
        gcongr
        exact choose_le_exp_mul_div_pow hs
    _ = Real.exp ((s : ℝ) * L) * Real.exp (-((s : ℝ) * L + L')) := by rw [hpow]
    _ = Real.exp (-L') := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ = δ0 := by
        rw [hL'def, Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ0), inv_div,
          div_one]

/-- **Corrected event: measurability and probability at least `1 - δ₀`.** -/
theorem prob_G_corrected_aux {σ δ0 : ℝ} {s : ℕ} (hX : UnitCols X) (hσ : 0 < σ)
    (hs : 1 ≤ s) (hsp : s ≤ p) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    MeasurableSet (Gc X σ δ0 s) ∧ 1 - δ0 ≤ (noiseLaw n σ (Gc X σ δ0 s)).toReal := by
  haveI : IsProbabilityMeasure (noiseLaw n σ) := by
    unfold noiseLaw
    haveI : ∀ i : Fin n, IsProbabilityMeasure (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
      fun _ => instIsProbabilityMeasureGaussianReal 0 _
    infer_instance
  have hmeas : MeasurableSet (Gc X σ δ0 s) := measurableSet_Gc X hσ hsp
  have hcompl_bound : (noiseLaw n σ).real (Gc X σ δ0 s)ᶜ ≤ δ0 :=
    measureReal_compl_Gc_le X hX hσ hs hsp hδ0 hδ1
  have huniv : (noiseLaw n σ).real Set.univ = 1 := by simp [measureReal_def]
  have hcompl_eq := measureReal_compl (μ := noiseLaw n σ) hmeas
  rw [huniv] at hcompl_eq
  have hmain : 1 - δ0 ≤ (noiseLaw n σ).real (Gc X σ δ0 s) := by linarith
  exact ⟨hmeas, hmain⟩


end

end SubsetShrink.Events

open SubsetShrink.Events

/-- **Theorem 1 (§B.1, corrected):** the fast-rate event `G'_s` is measurable and has
probability at least `1 - δ₀` under independent `N(0,σ²)` noise. -/
theorem solution {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (hs : 1 ≤ s) (hsp : s ≤ p) (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hδ1 : δ0 ≤ 1) :
    MeasurableSet (Gc X σ δ0 s) ∧ 1 - δ0 ≤ (noiseLaw n σ (Gc X σ δ0 s)).toReal :=
  prob_G_corrected_aux X hX hσ hs hsp hδ0 hδ1

#check @solution
