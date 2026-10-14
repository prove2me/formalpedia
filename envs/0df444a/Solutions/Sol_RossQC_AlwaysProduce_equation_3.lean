-- Prove2me | solution 1 for RossQC.AlwaysProduce.equation_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:39:27.495446+00:00
-- url     : https://prove2.me/submissions/92bb1f59-4cbe-48de-b37a-264adbaa7b3a

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model
open Filter


namespace RossQC.AlwaysProduce

open RossQC.Regions

structure Good (M : Model) : Prop where
  hβ0 : 0 < M.β
  hβ1 : M.β < 1
  hπ0 : 0 ≤ M.π
  hπ1 : M.π ≤ 1
  hC0 : 0 < M.C
  hCI : M.C < M.I
  hIR : M.I < M.R

noncomputable def Fop (M : Model) (V : ℝ → ℝ) (P : ℝ) : ℝ :=
  min (M.rhs3 V P .produce) (min (M.rhs3 V P .inspect) (M.rhs3 V P .revise))

lemma valueIter_succ (M : Model) (n : ℕ) (P : ℝ) :
    M.valueIter (n+1) P = Fop M (M.valueIter n) P := rfl

lemma T_mem {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.T P ∈ Set.Icc (0:ℝ) 1 ∧ P ≤ M.T P := by
  obtain ⟨h0, h1⟩ := hP
  have := h.hπ0; have := h.hπ1
  unfold Model.T
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith

lemma π_mem {M : Model} (h : Good M) : M.π ∈ Set.Icc (0:ℝ) 1 := ⟨h.hπ0, h.hπ1⟩

lemma one_mem' : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩

lemma iter_bounds {M : Model} (h : Good M) : ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1,
    0 ≤ M.valueIter n P ∧ M.valueIter n P ≤ M.R / (1 - M.β) := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  have hB0 : 0 ≤ M.R / (1 - M.β) := div_nonneg hR.le (by linarith)
  have hB : M.R / (1 - M.β) = M.R + M.β * (M.R / (1 - M.β)) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp; ring
  intro n
  induction n with
  | zero => intro P _; simp [Model.valueIter, hB0]
  | succ n ih =>
    intro P hP
    rw [valueIter_succ]
    unfold Fop
    obtain ⟨hT, _⟩ := T_mem h hP
    have i1 := ih _ hT
    have i2 := ih 1 one_mem'
    have i3 := ih _ (π_mem h)
    have hC := h.hC0; have hCI := h.hCI; have hIR := h.hIR
    obtain ⟨hP0, hP1⟩ := hP
    constructor
    · refine le_min ?_ (le_min ?_ ?_)
      · simp only [Model.rhs3]
        have := mul_nonneg hβ0.le i1.1
        have := mul_nonneg hC.le hP0
        linarith
      · simp only [Model.rhs3]
        have := mul_nonneg (mul_nonneg hβ0.le hP0) i2.1
        have := mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hP1)) i3.1
        linarith
      · simp only [Model.rhs3]
        have := mul_nonneg hβ0.le i3.1
        linarith
    · refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      simp only [Model.rhs3]
      have := mul_le_mul_of_nonneg_left i3.2 hβ0.le
      linarith

lemma F_lip {M : Model} (h : Good M) (U W : ℝ → ℝ) (δ : ℝ)
    (hU : ∀ x ∈ Set.Icc (0:ℝ) 1, |U x - W x| ≤ δ) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    |Fop M U P - Fop M W P| ≤ M.β * δ := by
  have hβ0 := h.hβ0
  obtain ⟨hT, _⟩ := T_mem h hP
  have u1 := hU _ hT
  have u2 := hU 1 one_mem'
  have u3 := hU _ (π_mem h)
  obtain ⟨hP0, hP1⟩ := hP
  have d1 : |M.rhs3 U P .produce - M.rhs3 W P .produce| ≤ M.β * δ := by
    simp only [Model.rhs3]
    have : M.C * P + M.β * U (M.T P) - (M.C * P + M.β * W (M.T P)) = M.β * (U (M.T P) - W (M.T P)) := by ring
    rw [this, abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left u1 hβ0.le
  have d3 : |M.rhs3 U P .revise - M.rhs3 W P .revise| ≤ M.β * δ := by
    simp only [Model.rhs3]
    have : M.R + M.β * U M.π - (M.R + M.β * W M.π) = M.β * (U M.π - W M.π) := by ring
    rw [this, abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left u3 hβ0.le
  have d2 : |M.rhs3 U P .inspect - M.rhs3 W P .inspect| ≤ M.β * δ := by
    simp only [Model.rhs3]
    have : M.I + M.β * P * U 1 + M.β * (1 - P) * U M.π - (M.I + M.β * P * W 1 + M.β * (1 - P) * W M.π)
        = (M.β * P) * (U 1 - W 1) + (M.β * (1 - P)) * (U M.π - W M.π) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (M.β * P), abs_mul (M.β * (1 - P)), abs_of_nonneg (mul_nonneg hβ0.le hP0), abs_of_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hP1))]
    have e1 := mul_le_mul_of_nonneg_left u2 (mul_nonneg hβ0.le hP0)
    have e2 := mul_le_mul_of_nonneg_left u3 (mul_nonneg hβ0.le (sub_nonneg.2 hP1))
    nlinarith
  unfold Fop
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le d1 ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le d2 d3)

lemma iter_diff {M : Model} (h : Good M) : ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1,
    |M.valueIter (n+1) P - M.valueIter n P| ≤ M.R * M.β ^ n := by
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  intro n
  induction n with
  | zero =>
    intro P hP
    obtain ⟨hP0, hP1⟩ := hP
    have hb := (iter_bounds h 1 P ⟨hP0, hP1⟩).1
    have hu : M.valueIter 1 P ≤ M.R := by
      rw [valueIter_succ]
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      simp [Model.rhs3, Model.valueIter]
    simp only [Model.valueIter, pow_zero, mul_one, sub_zero]
    rw [abs_of_nonneg (by simpa [Model.valueIter] using hb)]
    simpa [Model.valueIter] using hu
  | succ n ih =>
    intro P hP
    rw [valueIter_succ, valueIter_succ]
    have := F_lip h (M.valueIter (n+1)) (M.valueIter n) (M.R * M.β ^ n) ih hP
    calc _ ≤ M.β * (M.R * M.β ^ n) := this
      _ = M.R * M.β ^ (n+1) := by ring

lemma iter_tendsto {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P)) := by
  have hc : CauchySeq (fun n : ℕ => M.valueIter n P) := by
    refine cauchySeq_of_le_geometric M.β M.R h.hβ1 (fun n => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact iter_diff h n P hP
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have : M.value P = a := ha.limUnder_eq
  rw [this]; exact ha

lemma value_bounds {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ M.value P ∧ M.value P ≤ M.R / (1 - M.β) :=
  ⟨ge_of_tendsto' (iter_tendsto h hP) (fun n => (iter_bounds h n P hP).1),
   le_of_tendsto' (iter_tendsto h hP) (fun n => (iter_bounds h n P hP).2)⟩

lemma rhs3_tendsto {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) (a : Action) :
    Tendsto (fun n : ℕ => M.rhs3 (M.valueIter n) P a) atTop (nhds (M.rhs3 M.value P a)) := by
  obtain ⟨hT, _⟩ := T_mem h hP
  have t1 := iter_tendsto h hT
  have t2 := iter_tendsto h one_mem'
  have t3 := iter_tendsto h (π_mem h)
  cases a <;> simp only [Model.rhs3]
  · exact tendsto_const_nhds.add (t1.const_mul _)
  · exact (tendsto_const_nhds.add (t2.const_mul _)).add (t3.const_mul _)
  · exact tendsto_const_nhds.add (t3.const_mul _)

lemma value_fixed {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise)) := by
  have t := (rhs3_tendsto h hP .produce).min ((rhs3_tendsto h hP .inspect).min (rhs3_tendsto h hP .revise))
  have t' : Tendsto (fun n : ℕ => M.valueIter (n+1) P) atTop (nhds (M.value P)) :=
    (tendsto_add_atTop_iff_nat 1).2 (iter_tendsto h hP)
  exact tendsto_nhds_unique t' t

lemma uniq_aux {M : Model} (h : Good M) (W : ℝ → ℝ) (B : ℝ)
    (hB : ∀ P ∈ Set.Icc (0 : ℝ) 1, |W P| ≤ B)
    (hW : ∀ P ∈ Set.Icc (0 : ℝ) 1, W P = Fop M W P) :
    ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1, |W P - M.valueIter n P| ≤ M.β ^ n * B := by
  intro n
  induction n with
  | zero => intro P hP; simpa [Model.valueIter] using hB P hP
  | succ n ih =>
    intro P hP
    rw [hW P hP, valueIter_succ]
    have := F_lip h W (M.valueIter n) (M.β ^ n * B) ih hP
    calc _ ≤ M.β * (M.β ^ n * B) := this
      _ = M.β ^ (n+1) * B := by ring

theorem eq_3_core (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P))) ∧
    (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |M.value P| ≤ B) ∧
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise))) ∧
    (∀ W : ℝ → ℝ,
      (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |W P| ≤ B) →
      (∀ P ∈ Set.Icc (0 : ℝ) 1,
        W P = min (M.rhs3 W P .produce)
          (min (M.rhs3 W P .inspect) (M.rhs3 W P .revise))) →
      ∀ P ∈ Set.Icc (0 : ℝ) 1, W P = M.value P) := by
  have h : Good M := ⟨hβ0, hβ1, hπ0, hπ1, hC0, hCI, hIR⟩
  refine ⟨fun P hP => iter_tendsto h hP, ⟨M.R / (1 - M.β), fun P hP => ?_⟩, fun P hP => value_fixed h hP, ?_⟩
  · obtain ⟨a, b⟩ := value_bounds h hP
    rw [abs_of_nonneg a]; exact b
  · rintro W ⟨B, hB⟩ hW P hP
    have key := uniq_aux h W B hB hW
    have t1 : Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (W P)) := by
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB P hP)
      have g : Tendsto (fun n : ℕ => M.β ^ n * B) atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const B
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) g
      rw [Real.dist_eq, abs_sub_comm]
      exact key n P hP
    exact tendsto_nhds_unique t1 (iter_tendsto h hP)

end RossQC.AlwaysProduce

open RossQC.AlwaysProduce
open Filter RossQC.AlwaysProduce

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P))) ∧
    (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |M.value P| ≤ B) ∧
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise))) ∧
    (∀ W : ℝ → ℝ,
      (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |W P| ≤ B) →
      (∀ P ∈ Set.Icc (0 : ℝ) 1,
        W P = min (M.rhs3 W P .produce)
          (min (M.rhs3 W P .inspect) (M.rhs3 W P .revise))) →
      ∀ P ∈ Set.Icc (0 : ℝ) 1, W P = M.value P) := by
  exact eq_3_core M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR
