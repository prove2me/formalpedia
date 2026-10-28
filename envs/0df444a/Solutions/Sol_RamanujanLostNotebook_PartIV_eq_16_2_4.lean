-- Prove2me | solution 1 for RamanujanLostNotebook.PartIV.eq_16_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:28:37.774989+00:00
-- url     : https://prove2.me/submissions/77fef12b-54ec-4b40-8f39-d1040c108906

import Mathlib

open Filter Topology Finset

namespace S100R1624

noncomputable def ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2
noncomputable def ω₂ : ℂ := -1 - ω

lemma sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma ω_sq : ω ^ 2 + ω + 1 = 0 := by
  unfold ω
  linear_combination (Complex.I ^ 2 / 4) * sqrt3_sq + (3 / 4 : ℂ) * Complex.I_sq

noncomputable def F (c : ℂ) (N : ℕ) : ℂ := ∏ j ∈ range (N + 1), (c + j)
noncomputable def E (c : ℂ) (N : ℕ) : ℂ := F c N / ((N : ℂ) ^ c * (N.factorial : ℂ))

lemma E_eq (c : ℂ) (N : ℕ) : E c N = (Complex.GammaSeq c N)⁻¹ := by
  rw [E, F, Complex.GammaSeq, inv_div]

lemma E_tendsto (c : ℂ) : Tendsto (E c) atTop (𝓝 (Complex.Gamma c)⁻¹) := by
  by_cases hc : ∀ m : ℕ, c ≠ -m
  · have := (Complex.GammaSeq_tendsto_Gamma c).inv₀ (Complex.Gamma_ne_zero hc)
    have e : E c = fun N => (Complex.GammaSeq c N)⁻¹ := funext (E_eq c)
    rw [e]; exact this
  · push_neg at hc
    obtain ⟨m, rfl⟩ := hc
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m] with N hN
    rw [E, F, Finset.prod_eq_zero (i := m) (by simp; omega) (by ring), zero_div]

lemma alg (F0 F1 F2 F3 X Y1 Y2 Y3 M : ℂ) (hX : X ≠ 0) (hM : M ≠ 0) (hF : F0 ≠ 0)
    (hY1 : Y1 ≠ 0) (hY2 : Y2 ≠ 0) (hY3 : Y3 ≠ 0) (hY : Y1 * Y2 * Y3 = X * X * X) :
    F1 * F2 * F3 / F0 ^ 3
      = (F1 / (Y1 * M)) * (F2 / (Y2 * M)) * (F3 / (Y3 * M)) / (F0 / (X * M)) ^ 3 := by
  field_simp
  linear_combination (F1 * F2 * F3) * hY

lemma cpow_ne (N : ℕ) (hN : (N : ℂ) ≠ 0) (c : ℂ) : (N : ℂ) ^ c ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hN]; exact Complex.exp_ne_zero _

lemma term_eq (a s x : ℂ) (h : x + a ≠ 0) :
    1 + (s / (x + a)) ^ 3 = ((x + a) + s) * ((x + a) + ω * s) * ((x + a) + ω₂ * s) / (x + a) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 h), div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 3 h)]
  unfold ω₂
  linear_combination ((x + a) * s ^ 2 + s ^ 3) * ω_sq

lemma partial_eq (a s : ℂ) (ha : ∀ n : ℕ, a ≠ -((n : ℂ) + 1)) (N : ℕ) (hN : N ≠ 0) :
    ∏ n ∈ range (N + 1), (1 + (s / (((n : ℂ) + 1) + a)) ^ 3)
      = E (1 + a + s) N * E (1 + a + ω * s) N * E (1 + a + ω₂ * s) N / E (1 + a) N ^ 3 := by
  have hterm : ∀ n ∈ range (N + 1), (1 + (s / (((n : ℂ) + 1) + a)) ^ 3) =
      ((1 + a + s) + n) * ((1 + a + ω * s) + n) * ((1 + a + ω₂ * s) + n) / ((1 + a) + n) ^ 3 := by
    intro n _
    have h : ((n : ℂ) + 1) + a ≠ 0 := fun h0 => ha n (by linear_combination h0)
    rw [term_eq a s _ h]
    ring
  rw [prod_congr rfl hterm, prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_pow]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [E, F]
  apply alg
  · exact cpow_ne N hN' _
  · exact_mod_cast (Nat.factorial_ne_zero N)
  · rw [prod_ne_zero_iff]
    intro n _ h0
    exact ha n (by linear_combination h0)
  · exact cpow_ne N hN' _
  · exact cpow_ne N hN' _
  · exact cpow_ne N hN' _
  · rw [← Complex.cpow_add _ _ hN', ← Complex.cpow_add _ _ hN', ← Complex.cpow_add _ _ hN',
      ← Complex.cpow_add _ _ hN']
    congr 1
    unfold ω₂; ring

noncomputable def P0 (a s : ℂ) : ℂ :=
  (Complex.Gamma (1 + a + s))⁻¹ * (Complex.Gamma (1 + a + ω * s))⁻¹
    * (Complex.Gamma (1 + a + ω₂ * s))⁻¹ / ((Complex.Gamma (1 + a))⁻¹) ^ 3

lemma tendsto_partial (a s : ℂ) (ha : ∀ n : ℕ, a ≠ -((n : ℂ) + 1)) :
    Tendsto (fun N => ∏ n ∈ range N, (1 + (s / (((n : ℂ) + 1) + a)) ^ 3)) atTop
      (𝓝 (P0 a s)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hG : Complex.Gamma (1 + a) ≠ 0 :=
    Complex.Gamma_ne_zero (fun m hm => ha m (by linear_combination hm))
  have hlim := (((E_tendsto (1 + a + s)).mul (E_tendsto (1 + a + ω * s))).mul
    (E_tendsto (1 + a + ω₂ * s))).div ((E_tendsto (1 + a)).pow 3) (by simpa using hG)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (partial_eq a s ha N (by omega)).symm

lemma summable_aux (a s : ℂ) : Summable (fun n : ℕ => (s / (((n : ℂ) + 1) + a)) ^ 3) := by
  have hs : Summable (fun n : ℕ => (8 * ‖s‖ ^ 3) * (1 / ((↑(n + 1) : ℝ)) ^ 3)) := by
    apply Summable.mul_left
    exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply Summable.of_norm_bounded_eventually hs
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop ⌈2 * ‖a‖⌉₊] with n hn
  have hn' : 2 * ‖a‖ ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have h1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have h2 : ‖((n : ℂ) + 1)‖ ≤ ‖((n : ℂ) + 1) + a‖ + ‖a‖ := by
    simpa using norm_sub_le (((n : ℂ) + 1) + a) a
  have hx : ((n : ℝ) + 1) / 2 ≤ ‖((n : ℂ) + 1) + a‖ := by
    have := norm_nonneg a
    linarith
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
  rw [norm_pow, norm_div, div_pow]
  calc ‖s‖ ^ 3 / ‖((n : ℂ) + 1) + a‖ ^ 3 ≤ ‖s‖ ^ 3 / (((n : ℝ) + 1) / 2) ^ 3 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hpos.le hx 3
    _ = (8 * ‖s‖ ^ 3) * (1 / ((↑(n + 1) : ℝ)) ^ 3) := by
        push_cast
        field_simp
        ring

lemma hasProd_main (a s : ℂ) (ha : ∀ n : ℕ, a ≠ -((n : ℂ) + 1)) :
    HasProd (fun n : ℕ => 1 + (s / (((n : ℂ) + 1) + a)) ^ 3) (P0 a s) := by
  have hm : Multipliable (fun n : ℕ => 1 + (s / (((n : ℂ) + 1) + a)) ^ 3) :=
    Complex.multipliable_one_add_of_summable (summable_aux a s)
  have h1 := hm.hasProd
  have h2 := h1.tendsto_prod_nat
  rwa [tendsto_nhds_unique h2 (tendsto_partial a s ha)] at h1

lemma refl_inv (z : ℂ) (hz : z ≠ 0) :
    (Complex.Gamma (1 + z))⁻¹ * (Complex.Gamma (1 - z))⁻¹
      = Complex.sin ((Real.pi : ℂ) * z) / ((Real.pi : ℂ) * z) := by
  rw [← mul_inv, add_comm 1 z, Complex.Gamma_add_one z hz, mul_assoc,
    Complex.Gamma_mul_Gamma_one_sub, mul_inv, inv_div]
  ring

lemma final_eq (α β : ℂ) (h : α ^ 2 + α * β + β ^ 2 ≠ 0) :
    P0 α (α + β) * P0 β (α + β) =
        (Complex.Gamma (1 + α) * Complex.Gamma (1 + β)) ^ 3
            / (Complex.Gamma (1 + α + 2 * β) * Complex.Gamma (1 + β + 2 * α))
          * ((Complex.cosh ((Real.pi : ℂ) * (α + β) * (Real.sqrt 3 : ℂ))
                - Complex.cos ((Real.pi : ℂ) * (α - β)))
              / (2 * (Real.pi : ℂ) ^ 2 * (α ^ 2 + α * β + β ^ 2))) := by
  set z := α + ω * (α + β) with hz_def
  set w := α + ω₂ * (α + β) with hw_def
  have hzw : z * w = α ^ 2 + α * β + β ^ 2 := by
    rw [hz_def, hw_def]; unfold ω₂
    linear_combination (-(α + β) ^ 2) * ω_sq
  have hz : z ≠ 0 := left_ne_zero_of_mul (hzw ▸ h)
  have hw : w ≠ 0 := right_ne_zero_of_mul (hzw ▸ h)
  have e1 : 1 + α + (α + β) = 1 + β + 2 * α := by ring
  have e2 : 1 + β + (α + β) = 1 + α + 2 * β := by ring
  have e3 : 1 + α + ω * (α + β) = 1 + z := by rw [hz_def]; ring
  have e4 : 1 + α + ω₂ * (α + β) = 1 + w := by rw [hw_def]; ring
  have e5 : 1 + β + ω * (α + β) = 1 - w := by rw [hw_def]; unfold ω₂; ring
  have e6 : 1 + β + ω₂ * (α + β) = 1 - z := by rw [hz_def]; unfold ω₂; ring
  have hdiff : z - w = (Real.sqrt 3 : ℂ) * Complex.I * (α + β) := by
    rw [hz_def, hw_def]; unfold ω₂ ω; ring
  have hsum : z + w = α - β := by rw [hz_def, hw_def]; unfold ω₂; ring
  have htrig : Complex.sin ((Real.pi : ℂ) * z) * Complex.sin ((Real.pi : ℂ) * w)
      = (Complex.cosh ((Real.pi : ℂ) * (α + β) * (Real.sqrt 3 : ℂ))
          - Complex.cos ((Real.pi : ℂ) * (α - β))) / 2 := by
    have c1 : Complex.cosh ((Real.pi : ℂ) * (α + β) * (Real.sqrt 3 : ℂ))
        = Complex.cos ((Real.pi : ℂ) * z - (Real.pi : ℂ) * w) := by
      rw [← Complex.cos_mul_I]; congr 1; linear_combination (-(Real.pi : ℂ)) * hdiff
    have c2 : Complex.cos ((Real.pi : ℂ) * (α - β))
        = Complex.cos ((Real.pi : ℂ) * z + (Real.pi : ℂ) * w) := by
      congr 1; linear_combination (-(Real.pi : ℂ)) * hsum
    rw [c1, c2, Complex.cos_sub, Complex.cos_add]; ring
  have rz := refl_inv z hz
  have rw' := refl_inv w hw
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold P0
  rw [e1, e2, e3, e4, e5, e6]
  have key : (Complex.Gamma (1 + z))⁻¹ * (Complex.Gamma (1 - z))⁻¹ *
      ((Complex.Gamma (1 + w))⁻¹ * (Complex.Gamma (1 - w))⁻¹)
      = (Complex.cosh ((Real.pi : ℂ) * (α + β) * (Real.sqrt 3 : ℂ))
                - Complex.cos ((Real.pi : ℂ) * (α - β)))
              / (2 * (Real.pi : ℂ) ^ 2 * (α ^ 2 + α * β + β ^ 2)) := by
    rw [rz, rw', div_mul_div_comm, ← hzw]
    rw [show (Real.pi : ℂ) * z * ((Real.pi : ℂ) * w) = (Real.pi : ℂ) ^ 2 * (z * w) by ring,
      htrig]
    field_simp
  rw [← key]
  simp only [inv_pow, div_inv_eq_mul]
  ring

end S100R1624

open S100R1624 in
theorem solution (α β : ℂ)
    (hα : ∀ n : ℕ, α ≠ -((n : ℂ) + 1)) (hβ : ∀ n : ℕ, β ≠ -((n : ℂ) + 1))
    (hαβ : ∀ n : ℕ, α + 2 * β ≠ -((n : ℂ) + 1))
    (hβα : ∀ n : ℕ, β + 2 * α ≠ -((n : ℂ) + 1))
    (h : α ^ 2 + α * β + β ^ 2 ≠ 0) :
    ∃ P Q : ℂ,
      HasProd (fun n : ℕ => 1 + ((α + β) / (((n : ℂ) + 1) + α)) ^ 3) P ∧
      HasProd (fun n : ℕ => 1 + ((α + β) / (((n : ℂ) + 1) + β)) ^ 3) Q ∧
      P * Q =
        (Complex.Gamma (1 + α) * Complex.Gamma (1 + β)) ^ 3
            / (Complex.Gamma (1 + α + 2 * β) * Complex.Gamma (1 + β + 2 * α))
          * ((Complex.cosh ((Real.pi : ℂ) * (α + β) * (Real.sqrt 3 : ℂ))
                - Complex.cos ((Real.pi : ℂ) * (α - β)))
              / (2 * (Real.pi : ℂ) ^ 2 * (α ^ 2 + α * β + β ^ 2))) :=
  ⟨S100R1624.P0 α (α + β), S100R1624.P0 β (α + β), S100R1624.hasProd_main α (α + β) hα,
    S100R1624.hasProd_main β (α + β) hβ, S100R1624.final_eq α β h⟩
