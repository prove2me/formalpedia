-- Prove2me | solution 1 for RossQC.AlwaysProduce.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:41:52.686997+00:00
-- url     : https://prove2.me/submissions/db01d3bf-3de8-4d07-941b-bfa58d38328c

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


lemma T_one {M : Model} : M.T 1 = 1 := by unfold Model.T; ring

lemma kappa_pos {M : Model} (h : Good M) : 0 < 1 - M.β * (1 - M.π) := by
  have := h.hβ0; have := h.hβ1; have := h.hπ0; have := h.hπ1
  nlinarith

lemma Titer (M : Model) (P : ℝ) (n : ℕ) : (M.T^[n]) P = 1 - (1 - P) * (1 - M.π) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold Model.T
    ring

lemma psi_eq {M : Model} (h : Good M) (P : ℝ) :
    M.psi P = M.C / (1 - M.β) - M.C * (1 - P) / (1 - M.β * (1 - M.π)) := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hπ0 := h.hπ0; have hπ1 := h.hπ1
  have hq0 : 0 ≤ M.β * (1 - M.π) := mul_nonneg hβ0.le (by linarith)
  have hq1 : M.β * (1 - M.π) < 1 := by nlinarith
  have h1 := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left M.C
  have h2 := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M.C * (1 - P))
  have h3 := h1.sub h2
  have hf : (fun n : ℕ => M.β ^ n * (M.C * (M.T^[n]) P)) =
      fun n : ℕ => M.C * M.β ^ n - M.C * (1 - P) * (M.β * (1 - M.π)) ^ n := by
    funext n
    rw [Titer, mul_pow]
    ring
  unfold Model.psi
  rw [hf, h3.tsum_eq]
  simp only [div_eq_mul_inv]

lemma psi_nonneg {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) : 0 ≤ M.psi P := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hC := h.hC0
  have hk := kappa_pos h
  obtain ⟨hP0, hP1⟩ := hP
  rw [psi_eq h]
  have hk1 : 1 - M.β ≤ 1 - M.β * (1 - M.π) := by nlinarith [h.hπ0]
  have : M.C * (1 - P) / (1 - M.β * (1 - M.π)) ≤ M.C / (1 - M.β) := by
    rw [div_le_div_iff₀ hk (by linarith)]
    nlinarith [mul_nonneg hC.le hP0, mul_nonneg hC.le (sub_nonneg.2 hk1)]
  linarith

lemma psi_produce {M : Model} (h : Good M) (P : ℝ) :
    M.rhs3 M.psi P .produce = M.psi P := by
  have hk := kappa_pos h
  have hb : (1 - M.β) ≠ 0 := by linarith [h.hβ1]
  simp only [Model.rhs3]
  rw [psi_eq h, psi_eq h]
  unfold Model.T
  field_simp
  ring

lemma psi_inspect {M : Model} (h : Good M) (P : ℝ) :
    M.rhs3 M.psi P .inspect = M.psi P + (M.I - M.C * P) := by
  have hk := kappa_pos h
  have hb : (1 - M.β) ≠ 0 := by linarith [h.hβ1]
  have := psi_produce h P
  simp only [Model.rhs3] at this ⊢
  rw [psi_eq h, psi_eq h, psi_eq h] at *
  unfold Model.T at *
  field_simp at *
  linarith

lemma psi_revise {M : Model} (h : Good M) (P : ℝ) :
    M.rhs3 M.psi P .revise = M.R - M.C / (1 - M.β * (1 - M.π)) + M.C / (1 - M.β) := by
  have hk := kappa_pos h
  have hb : (1 - M.β) ≠ 0 := by linarith [h.hβ1]
  simp only [Model.rhs3]
  rw [psi_eq h]
  field_simp
  ring

lemma psi_le_top {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.psi P ≤ M.C / (1 - M.β) := by
  have hk := kappa_pos h
  rw [psi_eq h]
  have : 0 ≤ M.C * (1 - P) / (1 - M.β * (1 - M.π)) :=
    div_nonneg (mul_nonneg h.hC0.le (by linarith [hP.2])) hk.le
  linarith

lemma contOn_min {u v : ℝ → ℝ} {s : Set ℝ} (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun P => min (u P) (v P)) s :=
  continuous_min.comp_continuousOn (hu.prodMk hv)

lemma iter_cont {M : Model} (h : Good M) : ∀ n : ℕ, ContinuousOn (M.valueIter n) (Set.Icc (0:ℝ) 1) := by
  intro n
  induction n with
  | zero => simp only [Model.valueIter]; exact continuousOn_const
  | succ n ih =>
    have hT : ContinuousOn M.T (Set.Icc (0:ℝ) 1) := by
      unfold Model.T; fun_prop
    have hmap : Set.MapsTo M.T (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := fun P hP => (T_mem h hP).1
    have hfun : M.valueIter (n+1) = fun P => min (M.rhs3 (M.valueIter n) P .produce)
        (min (M.rhs3 (M.valueIter n) P .inspect) (M.rhs3 (M.valueIter n) P .revise)) := rfl
    rw [hfun]
    simp only [Model.rhs3]
    refine contOn_min ?_ (contOn_min ?_ ?_)
    · exact (continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul (ih.comp hT hmap))
    · fun_prop
    · exact continuousOn_const

lemma value_cont {M : Model} (h : Good M) : ContinuousOn M.value (Set.Icc (0:ℝ) 1) := by
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  have hs : Summable (fun k : ℕ => M.R * M.β ^ k) :=
    (summable_geometric_of_lt_one h.hβ0.le h.hβ1).mul_left _
  have hc := continuousOn_tsum (f := fun (k : ℕ) (P : ℝ) => M.valueIter (k+1) P - M.valueIter k P)
    (s := Set.Icc (0:ℝ) 1) (fun k => (iter_cont h (k+1)).sub (iter_cont h k)) hs
    (fun k P hP => by rw [Real.norm_eq_abs]; exact iter_diff h k P hP)
  refine hc.congr (fun P hP => ?_)
  have hsum : Summable (fun k : ℕ => ‖M.valueIter (k+1) P - M.valueIter k P‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact iter_diff h k P hP) hs
  have hHS : HasSum (fun k : ℕ => M.valueIter (k+1) P - M.valueIter k P) (M.value P) := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    have : ∀ n : ℕ, ∑ i ∈ Finset.range n, (M.valueIter (i+1) P - M.valueIter i P) = M.valueIter n P := by
      intro n
      rw [Finset.sum_range_sub (fun i => M.valueIter i P)]
      simp [Model.valueIter]
    simp only [this]
    exact iter_tendsto h hP
  exact hHS.tsum_eq.symm



lemma value_le_psi {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.value P ≤ M.psi P := by
  have key : ∀ n : ℕ, ∀ Q ∈ Set.Icc (0:ℝ) 1, M.valueIter n Q ≤ M.psi Q := by
    intro n
    induction n with
    | zero => intro Q hQ; simpa [Model.valueIter] using psi_nonneg h hQ
    | succ n ih =>
      intro Q hQ
      rw [valueIter_succ]
      unfold Fop
      refine (min_le_left _ _).trans ?_
      rw [← psi_produce h Q]
      simp only [Model.rhs3]
      have := ih _ (T_mem h hQ).1
      have := h.hβ0
      nlinarith
  exact le_of_tendsto' (iter_tendsto h hP) (fun n => key n P hP)

lemma part_b {M : Model} (h : Good M) (hlt : M.R < M.C / (1 - M.β * (1 - M.π))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P ∈ Set.Icc (0 : ℝ) 1, 1 - ε < P →
      M.rhs3 M.value P .revise < M.rhs3 M.value P .produce ∧
      M.rhs3 M.value P .revise < M.rhs3 M.value P .inspect := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hC := h.hC0; have hCI := h.hCI
  have hk := kappa_pos h
  have hb : (1 - M.β) ≠ 0 := by linarith
  have hvc := value_cont h
  -- strict inequality at P = 1
  have h1 : M.R + M.β * M.value M.π < M.C + M.β * M.value 1 := by
    by_contra hcon
    push_neg at hcon
    have hfix := value_fixed h one_mem'
    simp only [Model.rhs3, T_one] at hfix
    have hv1 : M.value 1 = M.C + M.β * M.value 1 := by
      have e1 : M.C * 1 + M.β * M.value 1 ≤ M.I + M.β * 1 * M.value 1 + M.β * (1 - 1) * M.value M.π := by
        nlinarith
      have e2 : M.C * 1 + M.β * M.value 1 ≤ M.R + M.β * M.value M.π := by linarith
      refine hfix.trans ?_
      rw [min_eq_left (le_min e1 e2)]; ring
    have hv1' : M.value 1 = M.C / (1 - M.β) := by
      field_simp; linarith
    have hpi := value_le_psi h (π_mem h)
    rw [psi_eq h] at hpi
    have hq : M.R + M.β * M.value M.π ≥ M.C / (1 - M.β) := by
      have : M.C + M.β * M.value 1 = M.C / (1 - M.β) := by
        rw [← hv1', ← hv1]
      linarith
    have : M.R + M.β * (M.C / (1 - M.β) - M.C * (1 - M.π) / (1 - M.β * (1 - M.π))) < M.C / (1 - M.β) := by
      have e : M.R + M.β * (M.C / (1 - M.β) - M.C * (1 - M.π) / (1 - M.β * (1 - M.π))) - M.C / (1 - M.β)
          = M.R - M.C / (1 - M.β * (1 - M.π)) := by
        field_simp; ring
      linarith
    nlinarith
  -- continuity
  have hT : ContinuousOn M.T (Set.Icc (0:ℝ) 1) := by unfold Model.T; fun_prop
  have hmap : Set.MapsTo M.T (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := fun P hP => (T_mem h hP).1
  have cprod : ContinuousOn (fun P => M.rhs3 M.value P .produce - M.rhs3 M.value P .revise) (Set.Icc (0:ℝ) 1) := by
    simp only [Model.rhs3]
    exact (((continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul (hvc.comp hT hmap))).sub continuousOn_const)
  have cins : ContinuousOn (fun P => M.rhs3 M.value P .inspect - M.rhs3 M.value P .revise) (Set.Icc (0:ℝ) 1) := by
    simp only [Model.rhs3]
    fun_prop
  have p1 : 0 < M.rhs3 M.value 1 .produce - M.rhs3 M.value 1 .revise := by
    simp only [Model.rhs3, T_one]; linarith
  have p2 : 0 < M.rhs3 M.value 1 .inspect - M.rhs3 M.value 1 .revise := by
    simp only [Model.rhs3]; nlinarith
  have e1 := (cprod.continuousWithinAt one_mem').eventually (lt_mem_nhds p1)
  have e2 := (cins.continuousWithinAt one_mem').eventually (lt_mem_nhds p2)
  have e := e1.and e2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at e
  obtain ⟨ε, hε, hall⟩ := e
  refine ⟨ε, hε, fun P hP hPε => ?_⟩
  have hd : dist P 1 < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hP.2]
  obtain ⟨a, b⟩ := hall hd hP
  constructor <;> linarith

theorem theorem_3_4_core (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((∀ P ∈ Set.Icc (0 : ℝ) 1, M.psi P = M.value P) ↔
      M.C / (1 - M.β * (1 - M.π)) ≤ M.R) ∧
    (M.R < M.C / (1 - M.β * (1 - M.π)) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1, 1 - ε < P →
          M.rhs3 M.value P .revise < M.rhs3 M.value P .produce ∧
          M.rhs3 M.value P .revise < M.rhs3 M.value P .inspect) := by
  have h : Good M := ⟨hβ0, hβ1, hπ0, hπ1, hC0, hCI, hIR⟩
  have hk := kappa_pos h
  have hb : (1 - M.β) ≠ 0 := by linarith
  refine ⟨⟨fun hall => ?_, fun hle => ?_⟩, fun hlt => part_b h hlt⟩
  · by_contra hcon
    push_neg at hcon
    have hfix := value_fixed h one_mem'
    have hpsi1 : M.psi 1 = M.C / (1 - M.β) := by rw [psi_eq h]; simp
    have hv1 : M.value 1 = M.C / (1 - M.β) := by rw [← hall 1 one_mem', hpsi1]
    have hvpi : M.value M.π = M.psi M.π := (hall M.π (π_mem h)).symm
    have hle : M.value 1 ≤ M.rhs3 M.value 1 .revise := by
      refine hfix.trans_le ?_
      exact (min_le_right _ _).trans (min_le_right _ _)
    simp only [Model.rhs3] at hle
    rw [hvpi, psi_eq h] at hle
    have : M.R + M.β * (M.C / (1 - M.β) - M.C * (1 - M.π) / (1 - M.β * (1 - M.π))) - M.C / (1 - M.β)
          = M.R - M.C / (1 - M.β * (1 - M.π)) := by
      field_simp; ring
    linarith
  · have core := (eq_3_core M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR).2.2.2
    intro P hP
    refine core M.psi ⟨M.C / (1 - M.β), fun Q hQ => ?_⟩ (fun Q hQ => ?_) P hP
    · rw [abs_of_nonneg (psi_nonneg h hQ)]; exact psi_le_top h hQ
    · have hp := psi_produce h Q
      have hi := psi_inspect h Q
      have hr := psi_revise h Q
      have hq : M.psi Q ≤ M.rhs3 M.psi Q .revise := by
        rw [hr]
        have := psi_le_top h hQ
        linarith
      have hi' : M.psi Q ≤ M.rhs3 M.psi Q .inspect := by
        rw [hi]; nlinarith [hQ.2]
      rw [hp, min_eq_left (le_min hi' hq)]

end RossQC.AlwaysProduce

open RossQC.AlwaysProduce
open Filter RossQC.AlwaysProduce

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((∀ P ∈ Set.Icc (0 : ℝ) 1, M.psi P = M.value P) ↔
      M.C / (1 - M.β * (1 - M.π)) ≤ M.R) ∧
    (M.R < M.C / (1 - M.β * (1 - M.π)) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1, 1 - ε < P →
          M.rhs3 M.value P .revise < M.rhs3 M.value P .produce ∧
          M.rhs3 M.value P .revise < M.rhs3 M.value P .inspect) := by
  exact theorem_3_4_core M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR
