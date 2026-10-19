-- Prove2me | solution 1 for QAlgorithms.Nannicini.amplitudeEstimation_complexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:50:37.547899+00:00
-- url     : https://prove2.me/submissions/1a7d8020-8c42-4f53-8062-4a41ee67d419

import Theorems.Thm_QAlgorithms_Nannicini_amplitudeEstimation_error
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
set_option autoImplicit false
open QAlgorithms

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, (m : ℝ) ≤ C * (Real.logb 2 (1 / ε) + 1) ∧
        ((3 * (2 ^ m - 1) + 1 : ℕ) : ℝ) ≤ C / ε ∧
        ∀ (n : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ)
          (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ),
          S ∈ Matrix.unitaryGroup (Qubits n) ℂ → R ∈ Matrix.unitaryGroup (Qubits n) ℂ →
          IsState psiG → IsState psiB → inner ℂ psiG psiB = 0 →
          0 ≤ θ → θ ≤ Real.pi / 2 →
          act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB →
          act R psiG = -psiG → act R psiB = psiB →
          8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) fun z =>
            |Real.sin θ ^ 2 - Real.sin (aeAngle z.1) ^ 2| ≤ ε := by
  classical
  refine ⟨192, by norm_num, ?_⟩
  intro ε hε hε1
  let L : ℝ := Real.logb 2 (1 / ε)
  have hrec : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hL : 0 ≤ L := by
    exact Real.logb_nonneg (by norm_num) hrec
  let k : ℕ := ⌈L⌉₊
  let m : ℕ := k + 5
  have hklo : L ≤ (k : ℝ) := Nat.le_ceil L
  have hkhi : (k : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL).le
  have hpowlo : 1 / ε ≤ (2 : ℝ) ^ k := by
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < 1 / ε)).mp hklo
    simpa only [Real.rpow_natCast] using h
  have hpowhi : (2 : ℝ) ^ k ≤ 2 / ε := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hkhi
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) (by positivity : 0 < 1 / ε), Real.rpow_one] at h
    simpa only [Real.rpow_natCast, mul_comm_div, one_mul] using h
  have hp : (2 : ℝ) ^ m = 32 * (2 : ℝ) ^ k := by
    dsimp [m]
    rw [pow_add]
    norm_num
    ring
  have hplo : 32 / ε ≤ (2 : ℝ) ^ m := by
    rw [hp]
    simp only [div_eq_mul_inv] at *
    linarith
  have hphi : (2 : ℝ) ^ m ≤ 64 / ε := by
    rw [hp]
    simp only [div_eq_mul_inv] at *
    linarith
  have hppos : 0 < (2 : ℝ) ^ m := by positivity
  refine ⟨m, ?_, ?_, ?_⟩
  · have hm : (m : ℝ) = (k : ℝ) + 5 := by simp [m]
    change (m : ℝ) ≤ 192 * (L + 1)
    linarith only [hkhi, hm, hL]
  · have hnat : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_pow m 2 (by norm_num)
    push_cast [Nat.cast_sub hnat]
    calc
      3 * ((2 : ℝ) ^ m - 1) + 1 ≤ 3 * (2 : ℝ) ^ m := by linarith
      _ ≤ 192 / ε := by
        simp only [div_eq_mul_inv] at hphi ⊢
        linarith only [hphi]
  · intro n S R psiG psiB θ hS hR hG hB horth hθ0 hθ1 hprep hRG hRB
    have hsqrt : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) ≤ 1 / 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · nlinarith only [sq_nonneg (Real.sin θ ^ 2 - 1 / 2)]
    have herr : 2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) /
        (2 : ℝ) ^ m + Real.pi ^ 2 / (2 : ℝ) ^ (2 * m) ≤ ε := by
      have hπ : Real.pi < 4 := Real.pi_lt_four
      have hlinear : 2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) ≤ 4 := by
        nlinarith only [Real.pi_pos, hπ, hsqrt, Real.sqrt_nonneg (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2))]
      have hfirst : 2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) /
          (2 : ℝ) ^ m ≤ ε / 8 := by
        apply (div_le_iff₀ hppos).mpr
        have hsize : 32 ≤ ε * (2 : ℝ) ^ m := by
          simpa only [mul_comm] using (div_le_iff₀ hε).mp hplo
        nlinarith only [hsize, hlinear]
      have hsecond : Real.pi ^ 2 / (2 : ℝ) ^ (2 * m) ≤ ε / 64 := by
        rw [mul_comm 2 m, pow_mul]
        apply (div_le_iff₀ (sq_pos_of_pos hppos)).mpr
        have hsize : 32 ≤ ε * (2 : ℝ) ^ m := by
          simpa only [mul_comm] using (div_le_iff₀ hε).mp hplo
        have hsize2 : 1024 ≤ ε ^ 2 * ((2 : ℝ) ^ m) ^ 2 := by
          nlinarith only [hsize, sq_nonneg (ε * (2 : ℝ) ^ m - 32)]
        have hepssq : ε ^ 2 * ((2 : ℝ) ^ m) ^ 2 ≤ ε * ((2 : ℝ) ^ m) ^ 2 := by
          nlinarith only [mul_nonneg (show 0 ≤ ε * (1 - ε) by positivity)
            (sq_nonneg ((2 : ℝ) ^ m))]
        nlinarith only [hπ, Real.pi_pos, hsize2, hepssq]
      linarith only [hfirst, hsecond, hε]
    have hprob := QAlgorithms.Nannicini.amplitudeEstimation_error m S R psiG psiB θ
      hS hR hG hB horth hθ0 hθ1 hprep hRG hRB
    refine hprob.trans ?_
    unfold probEvent
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.trans herr
    · intro z _ _
      exact sq_nonneg _
