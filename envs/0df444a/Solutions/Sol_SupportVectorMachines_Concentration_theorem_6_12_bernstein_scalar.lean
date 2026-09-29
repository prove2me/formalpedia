-- Prove2me | solution 1 for SupportVectorMachines.Concentration.theorem_6_12_bernstein_scalar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:52:23.271998+00:00
-- url     : https://prove2.me/submissions/bb9cc511-f103-4f18-8f54-719c75182c17

import Mathlib

open MeasureTheory ProbabilityTheory


namespace SupportVectorMachines.Concentration

lemma two_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

lemma exp_le_quad_pos {u : ℝ} (h0 : 0 ≤ u) (h3 : u < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3)) := by
  have hs := Real.summable_pow_div_factorial u
  have hexp : Real.exp u = ∑' k, u ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hr : 0 ≤ u / 3 := by positivity
  have hr1 : u / 3 < 1 := by linarith
  have hgs : Summable fun k : ℕ => u ^ 2 / 2 * (u / 3) ^ k :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ u ^ 2 / 2 * (u / 3) ^ k := by
    intro k
    have hf : (2 * 3 ^ k : ℝ) ≤ ((k + 2).factorial : ℝ) := by
      exact_mod_cast two_three_pow_le_factorial k
    have hpos : (0 : ℝ) < 2 * 3 ^ k := by positivity
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((k + 2).factorial : ℝ))]
    calc u ^ (k + 2) = u ^ 2 / 2 * (u / 3) ^ k * (2 * 3 ^ k) := by
          rw [div_pow]; field_simp; ring
      _ ≤ u ^ 2 / 2 * (u / 3) ^ k * ((k + 2).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
  have hle := (hs.comp_injective (add_left_injective 2)).tsum_le_tsum hterm hgs
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1] at hle
  rw [hexp, ← hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one]
  have e : u ^ 2 / 2 * (1 - u / 3)⁻¹ = u ^ 2 / (2 * (1 - u / 3)) := by
    field_simp
  have : ∑' k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ u ^ 2 / (2 * (1 - u / 3)) := by
    rw [← e]; exact hle
  linarith

lemma exp_le_quad_neg {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  have hanti : AntitoneOn (fun y => 1 + y + y ^ 2 / 2 - Real.exp y) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact (by fun_prop : Continuous fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y).continuousOn
    · exact (by fun_prop : Differentiable ℝ fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
        |>.differentiableOn
    · intro y hy
      rw [interior_Iic] at hy
      have hd : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
          (1 + y - Real.exp y) y := by
        have := ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub (Real.hasDerivAt_exp y))
        refine this.congr_deriv ?_
        simp only [Nat.cast_ofNat, id]
        ring
      rw [hd.deriv]
      linarith [Real.add_one_le_exp y]
  have := hanti hx (Set.mem_Iic.mpr le_rfl) hx
  simp at this
  linarith

lemma exp_le_quad {x c : ℝ} (hc0 : 0 ≤ c) (hc3 : c < 3) (hx : x ≤ c) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3)) := by
  have hden : 0 < 2 * (1 - c / 3) := by linarith
  rcases le_or_gt x 0 with hneg | hpos
  · have h1 := exp_le_quad_neg hneg
    have h2 : x ^ 2 / 2 ≤ x ^ 2 / (2 * (1 - c / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) hden
      linarith
    linarith
  · have h1 := exp_le_quad_pos hpos.le (by linarith)
    have h2 : x ^ 2 / (2 * (1 - x / 3)) ≤ x ^ 2 / (2 * (1 - c / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) hden
      linarith
    linarith


lemma mgf_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B σ : ℝ) (X : Ω → ℝ) (hm : Measurable X) (hmean : ∫ ω, X ω ∂P = 0)
    (hbound : ∀ᵐ ω ∂P, |X ω| ≤ B) (hvar : ∫ ω, (X ω) ^ 2 ∂P ≤ σ ^ 2)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl3 : lam * B < 3) :
    mgf X P lam ≤ Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) := by
  have hB0 : 0 ≤ B := by
    obtain ⟨ω, hω⟩ := hbound.exists
    exact (abs_nonneg _).trans hω
  have hc0 : 0 ≤ lam * B := mul_nonneg hl0 hB0
  have hden : 0 < 2 * (1 - lam * B / 3) := by linarith
  have hXint : Integrable X P :=
    Integrable.of_bound hm.aestronglyMeasurable B (by
      filter_upwards [hbound] with ω hω; rwa [Real.norm_eq_abs])
  have hX2int : Integrable (fun ω => (X ω) ^ 2) P :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (B ^ 2) (by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
  have hEint : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    Integrable.of_bound (by fun_prop) (Real.exp (lam * B)) (by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) hl0)
  set K := 1 / (2 * (1 - lam * B / 3)) with hK
  have hpt : ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤ 1 + lam * X ω + K * lam ^ 2 * (X ω) ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hx : lam * X ω ≤ lam * B := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) hl0
    have := exp_le_quad hc0 hl3 hx
    rw [hK]
    calc Real.exp (lam * X ω) ≤ 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - lam * B / 3)) := this
      _ = _ := by field_simp
  have hA : Integrable (fun ω => 1 + lam * X ω) P := (integrable_const 1).add (hXint.const_mul lam)
  have hB2 : Integrable (fun ω => K * lam ^ 2 * (X ω) ^ 2) P := hX2int.const_mul (K * lam ^ 2)
  have hint2 : Integrable (fun ω => 1 + lam * X ω + K * lam ^ 2 * (X ω) ^ 2) P := hA.add hB2
  have hmono := integral_mono_ae hEint hint2 hpt
  have hL : Integrable (fun ω => lam * X ω) P := hXint.const_mul lam
  rw [integral_add hA hB2, integral_add (integrable_const 1) hL, integral_const_mul,
    integral_const_mul, hmean] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at hmono
  have hK0 : 0 ≤ K * lam ^ 2 := by rw [hK]; positivity
  have h2 : 1 + K * lam ^ 2 * ∫ ω, (X ω) ^ 2 ∂P ≤ 1 + lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) := by
    have := mul_le_mul_of_nonneg_left hvar hK0
    rw [hK] at this ⊢
    have e : 1 / (2 * (1 - lam * B / 3)) * lam ^ 2 * σ ^ 2 =
        lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) := by field_simp
    linarith
  unfold mgf
  calc ∫ ω, Real.exp (lam * X ω) ∂P ≤ 1 + K * lam ^ 2 * ∫ ω, (X ω) ^ 2 ∂P := hmono
    _ ≤ 1 + lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) := h2
    _ ≤ Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) := by
        linarith [Real.add_one_le_exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)))]

theorem bern_main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (ξ : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ B)
    (hvar : ∀ i, ∫ ω, (ξ i ω) ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n) ≤
        (1 / (n : ℝ)) * ∑ i, ξ i ω} ≤ Real.exp (-τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set a := (n : ℝ) * Real.sqrt (2 * σ ^ 2 * τ / n) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = 2 * n * σ ^ 2 * τ := by
    rw [ha, mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  set b := 2 * B * τ / 3 with hb
  have hb0 : 0 < b := by positivity
  set T := a + b with hT
  set D := n * σ ^ 2 + B * T / 3 with hD
  have hDpos : 0 < D := by positivity
  set lam := T / D with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl3 : lam * B < 3 := by
    rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hDpos, hD]
    nlinarith [mul_pos hnR (pow_pos hσ 2)]
  -- rewrite the event
  have hset : {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n) ≤
      (1 / (n : ℝ)) * ∑ i, ξ i ω} = {ω | T ≤ (∑ i, ξ i) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_apply]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hnR]
    constructor <;> intro h
    · calc T = (Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n)) * n := by
            rw [hT, ha, hb]; field_simp
        _ ≤ _ := h
    · calc (Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n)) * n = T := by
            rw [hT, ha, hb]; field_simp
        _ ≤ _ := h
  rw [hset]
  -- integrability of the exponential of the sum
  have hSm : Measurable (∑ i, ξ i) := by
    rw [Finset.sum_fn]; exact Finset.measurable_sum _ fun i _ => hmeas i
  have hSint : Integrable (fun ω => Real.exp (lam * (∑ i, ξ i) ω)) P := by
    refine Integrable.of_bound (by fun_prop) (Real.exp (lam * (n * B))) ?_
    have hall : ∀ᵐ ω ∂P, ∀ i, |ξ i ω| ≤ B := ae_all_iff.mpr hbound
    filter_upwards [hall] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_left _ hl0
    simp only [Finset.sum_apply]
    calc ∑ i, ξ i ω ≤ ∑ _i : Fin n, B :=
          Finset.sum_le_sum fun i _ => le_trans (le_abs_self _) (hω i)
      _ = n * B := by simp
  have hch := measure_ge_le_exp_mul_mgf (X := ∑ i, ξ i) (μ := P) T hl0 hSint
  rw [hindep.mgf_sum hmeas Finset.univ] at hch
  have hprod : ∏ i ∈ Finset.univ, mgf (ξ i) P lam ≤
      Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) ^ n := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => mgf (ξ i) P lam)
      (g := fun _ => Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))))
      (fun i _ => mgf_nonneg) fun i _ =>
      mgf_bound P B σ (ξ i) (hmeas i) (hmean i) (hbound i) (hvar i) lam hl0 hl3
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  refine hch.trans ((mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  -- the exponent
  have hD0 : D ≠ 0 := hDpos.ne'
  have h1 : 1 - lam * B / 3 = n * σ ^ 2 / D := by
    rw [hlam, eq_div_iff hD0]
    field_simp
    rw [hD]; ring
  rw [h1]
  have hkey : -lam * T + n * (lam ^ 2 * σ ^ 2 / (2 * (n * σ ^ 2 / D))) = -(T ^ 2 / (2 * D)) := by
    rw [hlam]
    have : (n : ℝ) * σ ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hkey, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  have hab : 0 ≤ a * b := mul_nonneg ha0 hb0.le
  rw [hD, hT]
  nlinarith [ha2]

end SupportVectorMachines.Concentration

open SupportVectorMachines.Concentration

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (ξ : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ B)
    (hvar : ∀ i, ∫ ω, (ξ i ω) ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n) ≤
        (1 / (n : ℝ)) * ∑ i, ξ i ω} ≤ Real.exp (-τ) := by
  exact bern_main P B σ hB hσ n hn ξ hmeas hindep hmean hbound hvar τ hτ
