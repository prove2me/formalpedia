-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P42.precisionGaussianMixture_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:36:11.936481+00:00
-- url     : https://prove2.me/submissions/8bbca130-a579-4e63-8fed-35097dee254c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P42

open MeasureTheory

open scoped BigOperators

lemma X7GM_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    0 ≤ precisionGaussianDensity B b x := by
  unfold precisionGaussianDensity
  have : 0 ≤ Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  positivity

lemma X7GM_expand {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (v b : Fin n → ℝ) (t : ℝ) :
    dotProduct (t • v - b) (B.mulVec (t • v - b)) =
      t ^ 2 * dotProduct v (B.mulVec v) - t * dotProduct v (B.mulVec b) -
        t * dotProduct b (B.mulVec v) + dotProduct b (B.mulVec b) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- the good bounded pieces of the bad set -/
def X7GM_S {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) :
    Set (PrecisionParameters n) :=
  {p | 1 / ((k:ℝ)+1) < dotProduct v ((A - p.val.1).mulVec v) ∧
    1 / ((k:ℝ)+1) < p.val.1.det ∧
    |dotProduct v (p.val.1.mulVec p.val.2)| ≤ (k:ℝ)+1 ∧
    |dotProduct p.val.2 (p.val.1.mulVec v)| ≤ (k:ℝ)+1 ∧
    dotProduct p.val.2 (p.val.1.mulVec p.val.2) ≤ (k:ℝ)+1}

lemma X7GM_null {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (mu : Measure (PrecisionParameters n)) [IsProbabilityMeasure mu]
    (hmixture : IsPrecisionGaussianMixture A mu) (v : Fin n → ℝ) (k : ℕ) :
    mu (X7GM_S A v k) = 0 := by
  by_contra h0
  set K : ℝ := (k:ℝ) + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
  have hKpos : 0 < K := by linarith
  set m := mu.real (X7GM_S A v k) with hm
  have hmpos : 0 < m := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  set c := Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  set a := dotProduct v (A.mulVec v) with ha
  set s := Real.sqrt (1 / K) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  set dA := Real.sqrt A.det with hdA
  -- main inequality for each t ≥ 0
  have key : ∀ t : ℝ, 0 ≤ t →
      s * m * Real.exp (t ^ 2 / (2 * K) - t * K - K / 2) ≤ dA := by
    intro t ht
    obtain ⟨f, hf⟩ : ∃ f : PrecisionParameters n → ℝ,
        f = fun p => precisionGaussianDensity p.val.1 p.val.2 (t • v) := ⟨_, rfl⟩
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ,
        ε = s * c * Real.exp (-(t ^ 2 * (a - 1 / K) + 2 * t * K + K) / 2) := ⟨_, rfl⟩
    have hsub : X7GM_S A v k ⊆ {p | ε ≤ f p} := by
      intro p hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := hp
      simp only [Set.mem_setOf_eq, hf, precisionGaussianDensity]
      have hvB : dotProduct v (p.val.1.mulVec v) < a - 1 / K := by
        rw [Matrix.sub_mulVec, dotProduct_sub] at h1
        rw [ha]; linarith
      have hQ : dotProduct (t • v - p.val.2) (p.val.1.mulVec (t • v - p.val.2)) ≤
          t ^ 2 * (a - 1 / K) + 2 * t * K + K := by
        rw [X7GM_expand]
        have e1 : t ^ 2 * dotProduct v (p.val.1.mulVec v) ≤ t ^ 2 * (a - 1 / K) :=
          mul_le_mul_of_nonneg_left hvB.le (by positivity)
        have e2 : -(t * dotProduct v (p.val.1.mulVec p.val.2)) ≤ t * K := by
          have := neg_abs_le (dotProduct v (p.val.1.mulVec p.val.2))
          nlinarith
        have e3 : -(t * dotProduct p.val.2 (p.val.1.mulVec v)) ≤ t * K := by
          have := neg_abs_le (dotProduct p.val.2 (p.val.1.mulVec v))
          nlinarith
        linarith
      have hsq : s ≤ Real.sqrt p.val.1.det := Real.sqrt_le_sqrt h2.le
      have hexp : Real.exp (-(t ^ 2 * (a - 1 / K) + 2 * t * K + K) / 2) ≤
          Real.exp (-dotProduct (t • v - p.val.2) (p.val.1.mulVec (t • v - p.val.2)) / 2) := by
        apply Real.exp_le_exp.2; linarith
      rw [hε]
      calc s * c * Real.exp (-(t ^ 2 * (a - 1 / K) + 2 * t * K + K) / 2)
          ≤ Real.sqrt p.val.1.det * c *
            Real.exp (-dotProduct (t • v - p.val.2) (p.val.1.mulVec (t • v - p.val.2)) / 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hsq hcpos.le) hexp (Real.exp_pos _).le
            positivity
        _ = _ := rfl
    obtain ⟨_, hint, heq⟩ := hmixture (t • v)
    rw [← hf] at hint heq
    have hle : ε * mu.real {p | ε ≤ f p} ≤ ∫ p, f p ∂mu :=
      mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall
        (fun p => by rw [hf]; exact X7GM_nonneg p.val.1 p.val.2 (t • v))) hint ε
    have hmono : m ≤ mu.real {p | ε ≤ f p} := measureReal_mono hsub
    have hεpos : 0 ≤ ε := by rw [hε]; positivity
    have h1 : ε * m ≤ precisionGaussianDensity A 0 (t • v) := by
      rw [heq]; exact le_trans (mul_le_mul_of_nonneg_left hmono hεpos) hle
    have hA0 : precisionGaussianDensity A 0 (t • v) =
        dA * c * Real.exp (-(t ^ 2 * a) / 2) := by
      unfold precisionGaussianDensity
      rw [sub_zero, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        smul_eq_mul]
      congr 3; rw [ha]; ring
    rw [hA0, hε] at h1
    have hE : Real.exp (-(t ^ 2 * (a - 1 / K) + 2 * t * K + K) / 2) =
        Real.exp (-(t ^ 2 * a) / 2) * Real.exp (t ^ 2 / (2 * K) - t * K - K / 2) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hE] at h1
    have hE2 := Real.exp_pos (-(t ^ 2 * a) / 2)
    have : (s * m * Real.exp (t ^ 2 / (2 * K) - t * K - K / 2)) * (c * Real.exp (-(t ^ 2 * a) / 2))
        ≤ dA * (c * Real.exp (-(t ^ 2 * a) / 2)) := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  set T := dA / (s * m) + K with hT
  have hdA0 : 0 ≤ dA := Real.sqrt_nonneg _
  have hTnn : 0 ≤ T := by positivity
  have hk := key (2 * K ^ 2 + T) (by positivity)
  have hg : (2 * K ^ 2 + T) ^ 2 / (2 * K) - (2 * K ^ 2 + T) * K - K / 2 =
      K * T + T ^ 2 / (2 * K) - K / 2 := by field_simp; ring
  rw [hg] at hk
  have hexp := Real.add_one_le_exp (K * T + T ^ 2 / (2 * K) - K / 2)
  have hT2 : 0 ≤ T ^ 2 / (2 * K) := by positivity
  have hKT : T ≤ K * T := by nlinarith
  have hsm : 0 < s * m := mul_pos hspos hmpos
  have : s * m * T = dA + s * m * K := by
    rw [hT, mul_add, mul_div_cancel₀ _ hsm.ne']
  have : s * m * (T - K / 2 + 1) ≤ s * m * Real.exp (K * T + T ^ 2 / (2 * K) - K / 2) := by
    apply mul_le_mul_of_nonneg_left _ hsm.le; linarith
  nlinarith

end QAlgorithms.Papers.Independent.Claimed50.P42

end

noncomputable section

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P42 in
theorem solution (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (mu : Measure (PrecisionParameters n)) [IsProbabilityMeasure mu]
    (hmixture : IsPrecisionGaussianMixture A mu) :
    mu {p : PrecisionParameters n | ∃ x : Fin n → ℝ,
      0 < dotProduct x ((A - p.val.1).mulVec x)} = 0 := by
  let castv : (Fin n → ℚ) → (Fin n → ℝ) := Pi.map (fun _ (q : ℚ) => (q : ℝ))
  have hdense : DenseRange castv := DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcover : {p : PrecisionParameters n | ∃ x : Fin n → ℝ,
      0 < dotProduct x ((A - p.val.1).mulVec x)} ⊆
      ⋃ q : Fin n → ℚ, ⋃ k : ℕ, X7GM_S A (castv q) k := by
    rintro p ⟨x, hx⟩
    have hopen : IsOpen {y : Fin n → ℝ | 0 < dotProduct y ((A - p.val.1).mulVec y)} := by
      apply isOpen_lt continuous_const
      exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)
    obtain ⟨q, hq⟩ := hdense.exists_mem_open hopen ⟨x, hx⟩
    set v := castv q
    have hq' : 0 < dotProduct v ((A - p.val.1).mulVec v) := hq
    have hdet : 0 < p.val.1.det := p.property.det_pos
    obtain ⟨k, hk⟩ := exists_nat_gt (max (max (1 / dotProduct v ((A - p.val.1).mulVec v))
      (1 / p.val.1.det)) (max (max |dotProduct v (p.val.1.mulVec p.val.2)|
        |dotProduct p.val.2 (p.val.1.mulVec v)|) (dotProduct p.val.2 (p.val.1.mulVec p.val.2))))
    simp only [max_lt_iff] at hk
    obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩, k5⟩ := hk
    simp only [Set.mem_iUnion]
    refine ⟨q, k, ?_, ?_, ?_, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hq'] at k1; nlinarith
    · rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hdet] at k2; nlinarith
    · linarith
    · linarith
    · linarith
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro q
  apply measure_iUnion_null
  intro k
  exact X7GM_null A hA mu hmixture _ k

end
