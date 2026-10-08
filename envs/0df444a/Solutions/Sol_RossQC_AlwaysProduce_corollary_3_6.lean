-- Prove2me | solution 1 for RossQC.AlwaysProduce.corollary_3_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:05:00.067533+00:00
-- url     : https://prove2.me/submissions/ef61c687-f3ae-4316-a82e-2f1d016cbf17

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


open Filter Topology
private theorem convergence (M : Model) (hb0 : 0 < M.β) (hb1 : M.β < 1)
    (hp0 : 0 ≤ M.π) (hp1 : M.π ≤ 1) (hc : 0 < M.C)
    (hi : M.C < M.I) (hr : M.I < M.R) (P : ℝ) (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => M.valueIter n P) atTop (𝓝 (M.value P)) := by
  have hπ : M.π ∈ Set.Icc (0 : ℝ) 1 := ⟨hp0,hp1⟩
  have hOne : (1:ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have nonneg : ∀ n Q, Q ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ M.valueIter n Q := by
    intro n
    induction n with
    | zero => intro Q hQ; simp [Model.valueIter]
    | succ n ih =>
      intro Q hQ
      simp only [Model.valueIter, Model.rhs3, le_min_iff]
      have ht := ih _ (t_mem M hp0 hp1 hQ)
      have ho := ih _ hOne
      have hp := ih _ hπ
      constructor
      · have hq := hQ.1
        positivity
      constructor
      · have hq := hQ.1
        have hq' : 0 ≤ 1-Q := sub_nonneg.mpr hQ.2
        have hI : 0 ≤ M.I := by linarith
        positivity
      · have hR : 0 ≤ M.R := by linarith
        positivity
  have mono_step : ∀ n Q, Q ∈ Set.Icc (0 : ℝ) 1 →
      M.valueIter n Q ≤ M.valueIter (n+1) Q := by
    intro n
    induction n with
    | zero => intro Q hQ; simpa [Model.valueIter] using nonneg 1 Q hQ
    | succ n ih =>
      intro Q hQ
      change min (M.rhs3 (M.valueIter n) Q .produce)
        (min (M.rhs3 (M.valueIter n) Q .inspect) (M.rhs3 (M.valueIter n) Q .revise)) ≤
        min (M.rhs3 (M.valueIter (n+1)) Q .produce)
        (min (M.rhs3 (M.valueIter (n+1)) Q .inspect) (M.rhs3 (M.valueIter (n+1)) Q .revise))
      apply min_le_min
      · simp only [Model.rhs3]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (ih _ (t_mem M hp0 hp1 hQ)) hb0.le) _
      · apply min_le_min
        · simp only [Model.rhs3]
          have hq := hQ.1
          have hq' := sub_nonneg.mpr hQ.2
          have ho := ih _ hOne
          have hp := ih _ hπ
          nlinarith [mul_le_mul_of_nonneg_left ho (mul_nonneg hb0.le hq),
            mul_le_mul_of_nonneg_left hp (mul_nonneg hb0.le hq')]
        · simp only [Model.rhs3]
          exact add_le_add_right (mul_le_mul_of_nonneg_left (ih _ hπ) hb0.le) _
  have bound : ∀ n Q, Q ∈ Set.Icc (0 : ℝ) 1 → M.valueIter n Q ≤ M.C/(1-M.β) := by
    have hd : 0 < 1-M.β := sub_pos.mpr hb1
    have he : M.C + M.β*(M.C/(1-M.β)) = M.C/(1-M.β) := by field_simp; ring
    intro n
    induction n with
    | zero => intro Q hQ; simp only [Model.valueIter]; positivity
    | succ n ih =>
      intro Q hQ
      calc
        M.valueIter (n+1) Q ≤ M.C*Q + M.β*M.valueIter n (M.T Q) := min_le_left _ _
        _ ≤ M.C + M.β*(M.C/(1-M.β)) :=
          add_le_add (mul_le_of_le_one_right hc.le hQ.2)
            (mul_le_mul_of_nonneg_left (ih _ (t_mem M hp0 hp1 hQ)) hb0.le)
        _ = _ := he
  have hm : Monotone (fun n => M.valueIter n P) := monotone_nat_of_le_succ (fun n => mono_step n P hP)
  have hbd : BddAbove (Set.range (fun n => M.valueIter n P)) := ⟨M.C/(1-M.β), by
    rintro x ⟨n,rfl⟩; exact bound n P hP⟩
  exact tendsto_nhds_limUnder ⟨_, tendsto_atTop_ciSup hm hbd⟩

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ (P₁ P₂ : ℝ), P₁ ∈ Set.Icc (0 : ℝ) 1 → P₂ ∈ Set.Icc (0 : ℝ) 1 →
      |M.value P₁ - M.value P₂| ≤
        M.C * |P₁ - P₂| / (1 - M.β * (1 - M.π)) ∧
      (0 < M.π →
        M.C * |P₁ - P₂| / (1 - M.β * (1 - M.π)) ≤
          M.C * |P₁ - P₂| / M.π) := by
  intro P Q hP hQ
  have hq0 : 0 ≤ M.β*(1-M.π) := mul_nonneg hβ0.le (sub_nonneg.mpr hπ1)
  have hq1 : M.β*(1-M.π) < 1 := by nlinarith [mul_nonneg hβ0.le hπ0]
  have hd : 0 < 1-M.β*(1-M.π) := sub_pos.mpr hq1
  have hlimP := convergence M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR P hP
  have hlimQ := convergence M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR Q hQ
  have hbound : ∀ n, |M.valueIter n P-M.valueIter n Q| ≤ M.C*|P-Q|/(1-M.β*(1-M.π)) := by
    intro n
    have h := finite_bound M hβ0 hβ1 hπ0 hπ1 hC0 n P Q hP hQ
    have hk : K M n ≤ M.C/(1-M.β*(1-M.π)) := by
      unfold K
      apply div_le_div_of_nonneg_right _ hd.le
      nlinarith [pow_nonneg hq0 n]
    have hh := h.trans (mul_le_mul_of_nonneg_right hk (abs_nonneg (P-Q)))
    calc
      _ ≤ (M.C/(1-M.β*(1-M.π))) * |P-Q| := hh
      _ = _ := by ring
  constructor
  · exact le_of_tendsto (hlimP.sub hlimQ).abs (Filter.Eventually.of_forall hbound)
  · intro hp
    apply div_le_div_of_nonneg_left (mul_nonneg hC0.le (abs_nonneg _)) hp
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ1.le) (sub_nonneg.mpr hπ1)]

#print axioms solution
