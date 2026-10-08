-- Prove2me | solution 1 for RossQC.AlwaysProduce.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:03:27.160873+00:00
-- url     : https://prove2.me/submissions/00933ff9-a09e-4f98-a172-92c72883e7ee

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model
open RossQC.AlwaysProduce

private theorem t_mem (M : Model) (hp0 : 0 ≤ M.π) (hp1 : M.π ≤ 1)
    {P : ℝ} (hP : P ∈ Set.Icc (0 : ℝ) 1) : M.T P ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> dsimp [Model.T]
  · nlinarith [hP.1, mul_nonneg hp0 (sub_nonneg.mpr hP.2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hP.2)]

private theorem min_bound (a b c x y z d : ℝ)
    (ha : |a-x| ≤ d) (hb : |b-y| ≤ d) (hc : |c-z| ≤ d) :
    |min a (min b c) - min x (min y z)| ≤ d :=
  (abs_min_sub_min_le_max _ _ _ _).trans (max_le ha
    ((abs_min_sub_min_le_max _ _ _ _).trans (max_le hb hc)))

private noncomputable def K (M : Model) (n : ℕ) : ℝ :=
  M.C * (1 - (M.β*(1-M.π))^n) / (1-M.β*(1-M.π))

private theorem finite_bound (M : Model) (hb0 : 0 < M.β) (hb1 : M.β < 1)
    (hp0 : 0 ≤ M.π) (hp1 : M.π ≤ 1) (hc : 0 < M.C) :
    ∀ n P Q, P ∈ Set.Icc (0 : ℝ) 1 → Q ∈ Set.Icc (0 : ℝ) 1 →
    |M.valueIter n P - M.valueIter n Q| ≤ K M n * |P-Q| := by
  have hq0 : 0 ≤ M.β*(1-M.π) := mul_nonneg hb0.le (sub_nonneg.mpr hp1)
  have hq1 : M.β*(1-M.π) < 1 := by nlinarith [mul_nonneg hb0.le hp0]
  have hd : 0 < 1-M.β*(1-M.π) := sub_pos.mpr hq1
  have hk (n : ℕ) : 0 ≤ K M n := by
    exact div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr (pow_le_one₀ hq0 hq1.le))) hd.le
  have hrec (n : ℕ) : K M (n+1) = M.C + M.β*(1-M.π)*K M n := by
    unfold K
    rw [pow_succ]
    field_simp
    <;> ring
  intro n
  induction n with
  | zero => intro P Q hP hQ; simp [Model.valueIter, K]
  | succ n ih =>
    intro P Q hP hQ
    have hT : |M.T P - M.T Q| = (1-M.π)*|P-Q| := by
      have he : M.T P - M.T Q = (1-M.π)*(P-Q) := by dsimp [Model.T]; ring
      rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp1)]
    have hp := ih _ _ (t_mem M hp0 hp1 hP) (t_mem M hp0 hp1 hQ)
    rw [hT] at hp
    have hi := ih 1 M.π (by constructor <;> norm_num) ⟨hp0,hp1⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hp1)] at hi
    have ha : |M.rhs3 (M.valueIter n) P .produce - M.rhs3 (M.valueIter n) Q .produce| ≤ K M (n+1)*|P-Q| := by
      have he : M.rhs3 (M.valueIter n) P .produce - M.rhs3 (M.valueIter n) Q .produce =
          M.C*(P-Q) + M.β*(M.valueIter n (M.T P)-M.valueIter n (M.T Q)) := by
        dsimp [Model.rhs3]; ring
      rw [he, hrec]
      calc
        _ ≤ |M.C*(P-Q)| + |M.β*(M.valueIter n (M.T P)-M.valueIter n (M.T Q))| := abs_add_le _ _
        _ ≤ M.C*|P-Q| + M.β*(K M n*((1-M.π)*|P-Q|)) := by
          rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_pos hb0]
          exact add_le_add_right (mul_le_mul_of_nonneg_left hp hb0.le) _
        _ = _ := by ring
    have hb : |M.rhs3 (M.valueIter n) P .inspect - M.rhs3 (M.valueIter n) Q .inspect| ≤ K M (n+1)*|P-Q| := by
      have he : M.rhs3 (M.valueIter n) P .inspect - M.rhs3 (M.valueIter n) Q .inspect =
          M.β*(P-Q)*(M.valueIter n 1-M.valueIter n M.π) := by
        dsimp [Model.rhs3]; ring
      rw [he, abs_mul, abs_mul, abs_of_pos hb0, hrec]
      calc
        _ ≤ M.β * |P-Q| * (K M n*(1-M.π)) :=
          mul_le_mul_of_nonneg_left hi (mul_nonneg hb0.le (abs_nonneg _))
        _ ≤ _ := by nlinarith [mul_nonneg hc.le (abs_nonneg (P-Q))]
    have hr : |M.rhs3 (M.valueIter n) P .revise - M.rhs3 (M.valueIter n) Q .revise| ≤ K M (n+1)*|P-Q| := by
      simp only [Model.rhs3, sub_self, abs_zero]
      exact mul_nonneg (hk _) (abs_nonneg _)
    exact min_bound _ _ _ _ _ _ _ ha hb hr

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ (n : ℕ) (P₁ P₂ : ℝ),
      P₁ ∈ Set.Icc (0 : ℝ) 1 → P₂ ∈ Set.Icc (0 : ℝ) 1 →
      |M.valueIter n P₁ - M.valueIter n P₂| ≤
        M.C * |P₁ - P₂| * (1 - (M.β * (1 - M.π)) ^ n) /
          (1 - M.β * (1 - M.π)) := by
  intro n P Q hP hQ
  have h := finite_bound M hβ0 hβ1 hπ0 hπ1 hC0 n P Q hP hQ
  convert h using 1 <;> dsimp [K] <;> ring

#print axioms solution
