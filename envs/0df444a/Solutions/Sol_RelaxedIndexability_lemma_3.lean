-- Prove2me | solution 1 for RelaxedIndexability.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T22:54:26.519532+00:00
-- url     : https://prove2.me/submissions/190bd32f-6978-49e9-97bd-53f58ea7a0be

import Definitions.Def_RelaxedIndexability_thresholdValue
import Definitions.Def_RelaxedIndexability_RenewalSystem
import Definitions.Def_RelaxedIndexability_approxWhittle
import Theorems.Thm_RelaxedIndexability_renewal_equations

open Matrix

namespace _M6Lemma3Helper

open RelaxedIndexability

lemma row_mem_simplex {K : ℕ} {P : Matrix (Fin K) (Fin K) ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (k : Fin K) :
    P k ∈ stdSimplex ℝ (Fin K) :=
  ⟨fun _ => Matrix.nonneg_of_mem_rowStochastic hP,
    Matrix.sum_row_of_mem_rowStochastic hP k⟩

lemma vecMul_pow_mem_simplex {K : ℕ} {P : Matrix (Fin K) (Fin K) ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) {x : Fin K → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin K)) (n : ℕ) :
    x ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) := by
  have hPn : P ^ n ∈ Matrix.rowStochastic ℝ (Fin K) := Submonoid.pow_mem _ hP n
  refine ⟨Matrix.nonneg_vecMul_of_mem_rowStochastic hPn hx.1, ?_⟩
  have h1 : x ⬝ᵥ (1 : Fin K → ℝ) = 1 := by simpa [dotProduct] using hx.2
  have h2 := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hPn h1
  simpa [dotProduct] using h2

lemma crossTime_top_or_nat {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (B ω z : Fin K → ℝ) :
    crossTime P B ω z = ⊤ ∨ ∃ n : ℕ, crossTime P B ω z = n := by
  unfold crossTime
  classical
  split_ifs with h
  · exact Or.inr ⟨Nat.find h, rfl⟩
  · exact Or.inl rfl

lemma discPow_nonneg {β : ℝ} (hβ0 : 0 < β) (L : ℕ∞) : 0 ≤ discPow β L :=
  ENat.recTopCoe le_rfl (fun n => pow_nonneg hβ0.le n) L

lemma discPow_le_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (L : ℕ∞) : discPow β L ≤ 1 :=
  ENat.recTopCoe zero_le_one (fun _ => pow_le_one₀ hβ0.le hβ1.le) L

lemma GMat_entry_nonneg {K : ℕ} {β : ℝ} (hβ0 : 0 < β)
    {P : Matrix (Fin K) (Fin K) ℝ} (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) (k j : Fin K) :
    0 ≤ GMat β P B ω k j := by
  simp only [GMat, Matrix.of_apply, gVec, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (discPow_nonneg hβ0 _)
    ((vecMul_pow_mem_simplex hP (row_mem_simplex hP k) _).1 j)

lemma GMat_row_sum_le_one {K : ℕ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {P : Matrix (Fin K) (Fin K) ℝ} (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) (k : Fin K) :
    ∑ j : Fin K, GMat β P B ω k j ≤ 1 := by
  simp only [GMat, Matrix.of_apply, gVec, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [(vecMul_pow_mem_simplex hP (row_mem_simplex hP k) _).2, mul_one]
  exact discPow_le_one hβ0 hβ1 _

lemma mulVec_one_sub_beta_G_injective {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) :
    Function.Injective (1 - β • GMat β P B ω).mulVec := by
  intro u v huv
  have hw0 : (1 - β • GMat β P B ω) *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  suffices hzero : u - v = 0 by exact sub_eq_zero.mp hzero
  by_cases hK : Nonempty (Fin K)
  · obtain ⟨k₀, -, hk₀_max⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (Fin K)) (fun j => |(u - v) j|)
        Finset.univ_nonempty
    have hrow0 : ((1 - β • GMat β P B ω) *ᵥ (u - v)) k₀ = 0 := by rw [hw0]; rfl
    have hwk₀ : (u - v) k₀ = β * ∑ j : Fin K, GMat β P B ω k₀ j * (u - v) j := by
      have hexp : ((1 - β • GMat β P B ω) *ᵥ (u - v)) k₀ =
          (u - v) k₀ - β * ∑ j : Fin K, GMat β P B ω k₀ j * (u - v) j := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      linarith
    have habs_le : |(u - v) k₀| ≤ β * |(u - v) k₀| := by
      calc |(u - v) k₀|
          = |β * ∑ j : Fin K, GMat β P B ω k₀ j * (u - v) j| := by rw [hwk₀]
        _ = β * |∑ j : Fin K, GMat β P B ω k₀ j * (u - v) j| := by
            rw [abs_mul, abs_of_pos hβ0]
        _ ≤ β * ∑ j : Fin K, |GMat β P B ω k₀ j * (u - v) j| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hβ0.le
        _ = β * ∑ j : Fin K, GMat β P B ω k₀ j * |(u - v) j| := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (GMat_entry_nonneg hβ0 hP B ω k₀ j)]
        _ ≤ β * ∑ j : Fin K, GMat β P B ω k₀ j * |(u - v) k₀| := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hβ0.le
            exact mul_le_mul_of_nonneg_left (hk₀_max j (Finset.mem_univ j))
              (GMat_entry_nonneg hβ0 hP B ω k₀ j)
        _ = β * ((∑ j : Fin K, GMat β P B ω k₀ j) * |(u - v) k₀|) := by
            rw [← Finset.sum_mul]
        _ ≤ β * (1 * |(u - v) k₀|) := by
            refine mul_le_mul_of_nonneg_left ?_ hβ0.le
            exact mul_le_mul_of_nonneg_right (GMat_row_sum_le_one hβ0 hβ1 hP B ω k₀)
              (abs_nonneg _)
        _ = β * |(u - v) k₀| := by ring
    have hmax0 : |(u - v) k₀| ≤ 0 := by nlinarith [abs_nonneg ((u - v) k₀)]
    ext j
    have hj_le : |(u - v) j| ≤ 0 := (hk₀_max j (Finset.mem_univ j)).trans hmax0
    exact abs_eq_zero.mp (le_antisymm hj_le (abs_nonneg _))
  · ext j
    exact False.elim (hK ⟨j⟩)

lemma GMat_mulVec_apply {K : ℕ} (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω v : Fin K → ℝ)
    (k : Fin K) :
    (GMat β P B ω *ᵥ v) k = gVec β P B ω (P k) ⬝ᵥ v := by
  simp only [GMat, Matrix.mulVec, dotProduct, Matrix.of_apply]

lemma renewalSystem_linear_eq {K : ℕ} (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (B ω : Fin K → ℝ) (m : ℝ) {x y : Fin K → ℝ}
    (hsys : RenewalSystem β P B ω m x y) :
    (1 - β • GMat β P B ω) *ᵥ x = m • FVec β P B ω + GMat β P B ω *ᵥ B := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  ext k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, FVec]
  rw [GMat_mulVec_apply, GMat_mulVec_apply]
  have hk := hsys k
  rcases crossTime_top_or_nat P B ω (P k) with htop | ⟨n, hn⟩
  · have hx_top : x k = m / (1 - β) := hk.2 htop
    rw [hx_top]
    simp [fCoef, gVec, htop, discPow, ENat.recTopCoe_top]
    ring
  · obtain ⟨hx_eq, hy_eq⟩ := hk.1 n hn
    rw [hx_eq, hy_eq]
    simp only [fCoef, gVec, hn, discPow, ENat.recTopCoe_natCast, ENat.toNat_natCast,
      smul_dotProduct, smul_eq_mul]
    ring

end _M6Lemma3Helper

open RelaxedIndexability

theorem solution {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) (m : ℝ) :
    (∃ x y : Fin K → ℝ, RenewalSystem β P B ω m x y) ∧
    (∀ x y : Fin K → ℝ, RenewalSystem β P B ω m x y →
      x = fun k => thresholdValue β P B ω m (P k)) ∧
    IsUnit (1 - β • GMat β P B ω) := by
  let xStar : Fin K → ℝ := fun k => thresholdValue β P B ω m (P k)
  let yStar : Fin K → ℝ := fun k =>
    thresholdActionValue β P B ω m true (P k ᵥ* P ^ (crossTime P B ω (P k)).toNat)
  have hexist_star : RenewalSystem β P B ω m xStar yStar := by
    intro k
    have hren := renewal_equations β hβ0 hβ1 P hP B ω hω m k
    refine ⟨fun n hn => ?_, fun htop => hren.2 htop⟩
    obtain ⟨h1, h2⟩ := hren.1 n hn
    have htoNat : (crossTime P B ω (P k)).toNat = n := by simp [hn]
    refine ⟨?_, ?_⟩
    · simpa only [xStar, yStar, htoNat] using h1
    · simpa only [xStar, yStar, htoNat] using h2
  have hinj := _M6Lemma3Helper.mulVec_one_sub_beta_G_injective β hβ0 hβ1 P hP B ω
  have hunit : IsUnit (1 - β • GMat β P B ω) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨⟨xStar, yStar, hexist_star⟩, fun x y hsys => ?_, hunit⟩
  have heq1 := _M6Lemma3Helper.renewalSystem_linear_eq β P B ω m hsys
  have heq2 := _M6Lemma3Helper.renewalSystem_linear_eq β P B ω m hexist_star
  exact hinj (heq1.trans heq2.symm)
