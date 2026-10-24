-- Prove2me | solution 1 for OnlineConvexOpt.GamesDuality.eg_regret_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:28:20.238825+00:00
-- url     : https://prove2.me/submissions/73eb1738-dfb7-4212-afb6-a496c138a296

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2

namespace EG88
open MeasureTheory ProbabilityTheory


theorem hoeff {n : ℕ} (x ℓ : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1)
    (hl : ∀ i, |ℓ i| ≤ 1) (t : ℝ) :
    ∑ i, x i * Real.exp (t * ℓ i) ≤ Real.exp (t * ∑ i, x i * ℓ i + t ^ 2 / 2) := by
  let μ : Measure (Fin n) := ∑ i, (ENNReal.ofReal (x i)) • Measure.dirac i
  have hint : ∀ g : Fin n → ℝ, ∫ ω, g ω ∂μ = ∑ i, x i * g i := by
    intro g
    simp only [μ]
    rw [integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hx i), smul_eq_mul]
    · intro i _
      exact Integrable.smul_measure (integrable_dirac (by simp)) (by simp)
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hx i), hs, ENNReal.ofReal_one]
  have hb : ∀ᵐ ω ∂μ, ℓ ω ∈ Set.Icc (-1 : ℝ) 1 :=
    ae_of_all _ fun ω => abs_le.mp (hl ω)
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (measurable_of_finite _).aemeasurable hb).mgf_le t
  have hc : ((‖(1:ℝ) - -1‖₊ / 2) ^ 2 : NNReal) = 1 := by
    have : ‖(1:ℝ) - -1‖₊ = 2 := by
      rw [show (1:ℝ) - -1 = 2 by norm_num]; ext; simp
    rw [this]; norm_num
  rw [hc] at h
  simp only [mgf, hint] at h
  have e : ∀ i, Real.exp (t * (ℓ i - ∑ j, x j * ℓ j)) =
      Real.exp (t * ℓ i) * Real.exp (-(t * ∑ j, x j * ℓ j)) := by
    intro i; rw [← Real.exp_add]; ring_nf
  simp only [e] at h
  simp only [← mul_assoc] at h
  rw [← Finset.sum_mul] at h
  have hpos := Real.exp_pos (-(t * ∑ j, x j * ℓ j))
  have : ∑ i, x i * Real.exp (t * ℓ i) ≤ Real.exp (1 * t ^ 2 / 2) / Real.exp (-(t * ∑ j, x j * ℓ j)) := by
    rw [le_div_iff₀ hpos]; simpa using h
  calc _ ≤ _ := this
    _ = _ := by rw [← Real.exp_sub]; ring_nf


open OnlineConvexOpt.GamesDuality


theorem main {n m T : ℕ} (hn : 0 < n) (_hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ) (η : ℝ) (_hη : 0 ≤ η)
    (hrun : IsSimpleLPRun η A x y) (k : Fin n) :
    η * ∑ t ∈ Finset.range T, rowValue A (x t) (y t) ≤
      η * ∑ t ∈ Finset.range T, A.mulVec (y t) k + Real.log n + T * η ^ 2 / 2 := by
  set ℓ : ℕ → Fin n → ℝ := fun t i => A.mulVec (y t) i with hℓ
  have hlb : ∀ t i, |ℓ t i| ≤ 1 := by
    intro t i
    obtain ⟨hy0, hy1⟩ := (hrun.best_response t).1
    simp only [hℓ, Matrix.mulVec, dotProduct]
    calc |∑ j, A i j * y t j| ≤ ∑ j, |A i j * y t j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, y t j := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (hy0 j)]
          exact mul_le_of_le_one_left (hy0 j) (hA i j)
      _ = 1 := hy1
  set L : ℕ → Fin n → ℝ := fun t i => ∑ s ∈ Finset.range t, ℓ s i with hL
  set w : ℕ → Fin n → ℝ := fun t i => Real.exp (-η * L t i) with hw
  set W : ℕ → ℝ := fun t => ∑ i, w t i with hW
  have hwpos : ∀ t i, 0 < w t i := fun t i => Real.exp_pos _
  have hWpos : ∀ t, 0 < W t := fun t =>
    Finset.sum_pos (fun i _ => hwpos t i) ⟨k, Finset.mem_univ _⟩
  have hw1 : ∀ t j, w (t+1) j = w t j * Real.exp (-η * ℓ t j) := by
    intro t j; simp only [hw, hL, Finset.sum_range_succ, ← Real.exp_add]; ring_nf
  have hW1 : ∀ t, W (t+1) = ∑ j, w t j * Real.exp (-η * ℓ t j) := by
    intro t; simp only [hW, hw1]
  have hxw : ∀ t i, x t i = w t i / W t := by
    intro t
    induction t with
    | zero =>
      intro i
      simp [hw, hW, hL, hrun.init i]
    | succ t ih =>
      intro i
      rw [hrun.update t i]
      simp only [ih]
      rw [hw1, hW1]
      have hWne : W t ≠ 0 := (hWpos t).ne'
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div, div_div_div_cancel_right₀ hWne]
  have hrv : ∀ t, rowValue A (x t) (y t) = ∑ i, x t i * ℓ t i := by
    intro t; simp [rowValue, dotProduct, hℓ]
  have hstep : ∀ t, W (t+1) ≤ W t * Real.exp (-η * rowValue A (x t) (y t) + η ^ 2 / 2) := by
    intro t
    have hx0 : ∀ i, 0 ≤ x t i := fun i => by rw [hxw]; exact (div_pos (hwpos t i) (hWpos t)).le
    have hx1 : ∑ i, x t i = 1 := by
      simp only [hxw, ← Finset.sum_div]; exact div_self (hWpos t).ne'
    have h := hoeff (x t) (ℓ t) hx0 hx1 (hlb t) (-η)
    rw [neg_sq] at h
    have e : W (t+1) = W t * ∑ i, x t i * Real.exp (-η * ℓ t i) := by
      rw [hW1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hxw]; field_simp [(hWpos t).ne']
    rw [e, hrv]
    exact mul_le_mul_of_nonneg_left h (hWpos t).le
  have hprod : ∀ T', W T' ≤ W 0 * Real.exp (∑ t ∈ Finset.range T',
      (-η * rowValue A (x t) (y t) + η ^ 2 / 2)) := by
    intro T'
    induction T' with
    | zero => simp
    | succ T' ih =>
      rw [Finset.sum_range_succ, Real.exp_add, ← mul_assoc]
      exact (hstep T').trans (mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le)
  have hW0 : W 0 = n := by simp [hW, hw, hL]
  have hk : w T k ≤ W T := Finset.single_le_sum (f := w T) (fun i _ => (hwpos T i).le) (Finset.mem_univ k)
  have h2 := hk.trans (hprod T)
  rw [hW0] at h2
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h3 := Real.log_le_log (hwpos T k) h2
  rw [Real.log_mul hnpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
  simp only [Real.log_exp, hL, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum] at h3
  simp only [hℓ] at h3
  linarith

end EG88

open OnlineConvexOpt.GamesDuality in
theorem solution {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y) :
    ∑ t ∈ Finset.range T, rowValue A (x t) (y t) ≤
      sInf ((fun x' => ∑ t ∈ Finset.range T, rowValue A x' (y t)) '' stdSimplex ℝ (Fin n)) +
        Real.sqrt (2 * (T : ℝ) * Real.log (n : ℝ)) := by
  set η := Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ)) with hη
  set S := ∑ t ∈ Finset.range T, rowValue A (x t) (y t) with hS
  set c := Real.sqrt (2 * (T : ℝ) * Real.log (n : ℝ)) with hc
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  -- per-arm bound
  have hk : ∀ k : Fin n, S - c ≤ ∑ t ∈ Finset.range T, A.mulVec (y t) k := by
    intro k
    have h := EG88.main hn hT A hA x y η (Real.sqrt_nonneg _) hrun k
    have hη2 : η ^ 2 = 2 * Real.log n / T := Real.sq_sqrt (by positivity)
    have hηc : η * c = 2 * Real.log n := by
      rw [hη, hc, ← Real.sqrt_mul (by positivity)]
      rw [show 2 * Real.log ↑n / ↑T * (2 * ↑T * Real.log ↑n) = (2 * Real.log n) ^ 2 by
        field_simp]
      exact Real.sqrt_sq (by positivity)
    rw [hη2] at h
    have h' : η * S ≤ η * (∑ t ∈ Finset.range T, A.mulVec (y t) k) + η * c := by
      rw [hηc]
      have : (T:ℝ) * (2 * Real.log n / T) / 2 = Real.log n := by field_simp
      linarith
    rcases (Real.sqrt_nonneg (2 * Real.log (n : ℝ) / (T : ℝ))).lt_or_eq with hpos | hzero
    · have := le_of_mul_le_mul_left (by linarith : η * S ≤ η * (∑ t ∈ Finset.range T, A.mulVec (y t) k + c)) hpos
      linarith
    · -- η = 0 forces n = 1
      have h0 : Real.log (n : ℝ) = 0 := by
        have := hzero.symm
        rw [Real.sqrt_eq_zero (by positivity)] at this
        have := (div_eq_zero_iff.mp this).resolve_right hTr.ne'
        linarith
      have hn1 : n = 1 := by
        rcases Real.log_eq_zero.mp h0 with h | h | h
        · exact absurd h (by exact_mod_cast hn.ne')
        · exact_mod_cast h
        · have : (0:ℝ) ≤ n := Nat.cast_nonneg n
          linarith
      subst hn1
      have hc0 : c = 0 := by rw [hc, h0, mul_zero, Real.sqrt_zero]
      have hx : ∀ t, x t = fun _ => 1 := by
        intro t
        induction t with
        | zero => funext i; simp [hrun.init i]
        | succ t ih =>
          funext i
          rw [hrun.update t i, ih]
          simp only [Fin.sum_univ_one, one_mul]
          have : Fin.mk 0 (by norm_num) = i := Subsingleton.elim _ _
          rw [show (0 : Fin 1) = i from Subsingleton.elim _ _]
          exact div_self (Real.exp_pos _).ne'
      have : S = ∑ t ∈ Finset.range T, A.mulVec (y t) k := by
        rw [hS]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hx t]
        simp [rowValue, dotProduct, Subsingleton.elim (0 : Fin 1) k]
      linarith
  have hne : ((fun x' => ∑ t ∈ Finset.range T, rowValue A x' (y t)) '' stdSimplex ℝ (Fin n)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (single_mem_stdSimplex ℝ (⟨0, hn⟩ : Fin n))⟩
  have : S - c ≤ sInf ((fun x' => ∑ t ∈ Finset.range T, rowValue A x' (y t)) '' stdSimplex ℝ (Fin n)) := by
    refine le_csInf hne ?_
    rintro v ⟨x', ⟨hx0, hx1⟩, rfl⟩
    have e : ∑ t ∈ Finset.range T, rowValue A x' (y t) =
        ∑ i, x' i * ∑ t ∈ Finset.range T, A.mulVec (y t) i := by
      simp only [rowValue, dotProduct, Finset.mul_sum]
      exact Finset.sum_comm
    show S - c ≤ ∑ t ∈ Finset.range T, rowValue A x' (y t)
    rw [e]
    calc S - c = ∑ i, x' i * (S - c) := by rw [← Finset.sum_mul, hx1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hk i) (hx0 i)
  linarith
