-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:48:20.87544+00:00
-- url     : https://prove2.me/submissions/decc12cb-9e1c-4049-8922-fb1c8badaf79

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis
import Theorems.Thm_OnlineMaxWeightMatch_Approx_corollary_4_10

open MeasureTheory ProbabilityTheory

namespace LPMCommon
open OnlineMaxWeightMatch.Approx

variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma cumX_le_one {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) : cumX x i t ≤ 1 := by
  calc cumX x i t ≤ ∑ s, x i s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => hx.nonneg i s)
    _ ≤ 1 := hx.bin_le_one i

lemma cumX_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) : 0 ≤ cumX x i t :=
  Finset.sum_nonneg (fun s _ => hx.nonneg i s)

lemma c_eq : (c : ℝ) = 1 / 100 := rfl

lemma acceptProb_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) : 0 ≤ acceptProb x i t := by
  unfold acceptProb
  have h1 := cumX_le_one hx i t
  have h0 := cumX_nonneg hx i t
  apply le_min zero_le_one
  apply div_nonneg
  · rw [c_eq]; norm_num
  · rw [c_eq]; nlinarith

lemma acceptProb_le_one (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : acceptProb x i t ≤ 1 :=
  min_le_left _ _

lemma pickWeight_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (o : Option ι) :
    0 ≤ pickWeight I x t o := by
  cases o with
  | some i => exact div_nonneg (hx.nonneg i t) (I.p_nonneg t)
  | none =>
    simp only [pickWeight]
    rw [← Finset.sum_div, htight t]
    rcases (I.p_nonneg t).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [div_self h.ne']; simp

lemma sum_pickWeight (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) :
    ∑ o : Option ι, pickWeight I x t o = 1 := by
  rw [Fintype.sum_option]
  simp [pickWeight]

lemma ballWeight_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (d : BallDraw ι) :
    0 ≤ ballWeight I x t d := by
  unfold ballWeight
  have hA : 0 ≤ (if d.arrives then I.p t else 1 - I.p t) := by
    split_ifs
    · exact I.p_nonneg t
    · linarith [I.p_le_one t]
  have hC : 0 ≤ ∏ i, (if d.coin i then acceptProb x i t else 1 - acceptProb x i t) := by
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact acceptProb_nonneg hx i t
    · linarith [acceptProb_le_one x i t]
  have := pickWeight_nonneg hx htight t d.firstPick
  have := pickWeight_nonneg hx htight t d.secondPick
  positivity

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : α → ℝ) (B : β → ℝ) (C : γ → ℝ) (D : δ → ℝ) :
    ∑ d : α × β × γ × δ, A d.1 * B d.2.1 * C d.2.2.1 * D d.2.2.2 =
      (∑ a, A a) * (∑ b, B b) * (∑ c, C c) * (∑ d, D d) := by
  simp only [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

open Classical in
lemma sum_ballWeight (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) :
    ∑ d : BallDraw ι, ballWeight I x t d = 1 := by
  have h := sum4 (fun b : Bool => if b then I.p t else 1 - I.p t) (pickWeight I x t)
    (fun f : ι → Bool => ∏ i, if f i then acceptProb x i t else 1 - acceptProb x i t)
    (pickWeight I x t)
  have hcoin : ∑ f : ι → Bool, ∏ i, (if f i then acceptProb x i t else 1 - acceptProb x i t)
      = 1 := by
    have h := Fintype.prod_sum (fun i (b : Bool) =>
      if b then acceptProb x i t else 1 - acceptProb x i t)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_sub_cancel,
      Finset.prod_const_one] at h
    exact h.symm
  rw [Fintype.sum_bool, sum_pickWeight, hcoin] at h
  simp only [if_true, Bool.false_eq_true, if_false, add_sub_cancel, mul_one] at h
  exact h

lemma outcomeWeight_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ}
    (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t) (ω : Outcome ι n) :
    0 ≤ outcomeWeight I x ω :=
  Finset.prod_nonneg (fun t _ => ballWeight_nonneg hx htight t (ω t))

lemma sum_outcomeWeight (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) :
    ∑ ω : Outcome ι n, outcomeWeight I x ω = 1 := by
  classical
  unfold outcomeWeight
  have h := Fintype.prod_sum (fun (t : Fin n) (d : BallDraw ι) => ballWeight I x t d)
  simp only [sum_ballWeight, Finset.prod_const_one] at h
  exact h.symm

lemma algMeasure_apply (I : RideHailInstance ι n) (x : ι → Fin n → ℝ)
    (s : Set (Outcome ι n)) :
    algMeasure I x s = ∑ ω, ENNReal.ofReal (outcomeWeight I x ω) * s.indicator 1 ω := by
  classical
  rw [algMeasure, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top), smul_eq_mul]

lemma isProb {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) : IsProbabilityMeasure (algMeasure I x) := by
  constructor
  rw [algMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => outcomeWeight_nonneg hx htight ω),
    sum_outcomeWeight]
  simp

/-- the probability of an event as a finite sum of weights -/
lemma real_apply {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (s : Set (Outcome ι n)) [DecidablePred (· ∈ s)] :
    (algMeasure I x).real s = ∑ ω, if ω ∈ s then outcomeWeight I x ω else 0 := by
  rw [measureReal_def, algMeasure_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ s
    · simp [h, Set.indicator, ENNReal.toReal_ofReal (outcomeWeight_nonneg hx htight ω)]
    · simp [h, Set.indicator]
  · intro ω _
    by_cases h : ω ∈ s <;> simp [h, Set.indicator]

end LPMCommon


open MeasureTheory ProbabilityTheory

namespace LPMStruct
open OnlineMaxWeightMatch.Approx

variable {ι : Type*} {n : ℕ}

/-- `step` only ever adds edges of the current ball. -/
lemma step_fst_sub (x : ι → Fin n → ℝ) (t : Fin n) (d : BallDraw ι) (S : AlgState ι n)
    (e : ι × Fin n) (he : e ∈ (step x t d S).1) : e ∈ S.1 ∨ e.2 = t := by
  classical
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] at * <;> (try split_ifs at *) <;> (try simp_all) <;>
    (try split_ifs at *) <;> (try simp_all) <;> (try split_ifs at *) <;> (try simp_all) <;>
    aesop

lemma step_snd_sub (x : ι → Fin n → ℝ) (t : Fin n) (d : BallDraw ι) (S : AlgState ι n)
    (e : ι × Fin n) (he : e ∈ (step x t d S).2) : e ∈ S.2 ∨ e.2 = t := by
  classical
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] at * <;> (try split_ifs at *) <;> (try simp_all) <;>
    (try split_ifs at *) <;> (try simp_all) <;> (try split_ifs at *) <;> (try simp_all) <;>
    aesop

/-- `step` keeps old edges. -/
lemma step_fst_sup (x : ι → Fin n → ℝ) (t : Fin n) (d : BallDraw ι) (S : AlgState ι n)
    (e : ι × Fin n) (he : e ∈ S.1) : e ∈ (step x t d S).1 := by
  classical
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] at * <;> (try (by_cases hv : IsVacantIn S i1 ∧ cn i1 = true <;>
      simp only [hv, if_true, if_false])) <;>
    (try split_ifs) <;> (try simp_all) <;> (try split_ifs) <;> simp_all

lemma step_snd_sup (x : ι → Fin n → ℝ) (t : Fin n) (d : BallDraw ι) (S : AlgState ι n)
    (e : ι × Fin n) (he : e ∈ S.2) : e ∈ (step x t d S).2 := by
  classical
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] at * <;> (try (by_cases hv : IsVacantIn S i1 ∧ cn i1 = true <;>
      simp only [hv, if_true, if_false])) <;>
    (try split_ifs) <;> (try simp_all) <;> (try split_ifs) <;> simp_all

/-- At step `t`, starting from a state with no edge of ball `t`, edge `(i, t)` cannot end up
in both `M1` and `M2`. -/
lemma step_excl (x : ι → Fin n → ℝ) (t : Fin n) (d : BallDraw ι) (S : AlgState ι n)
    (h1 : ∀ j, (j, t) ∉ S.1) (h2 : ∀ j, (j, t) ∉ S.2) (i : ι) :
    ¬ ((i, t) ∈ (step x t d S).1 ∧ (i, t) ∈ (step x t d S).2) := by
  classical
  rintro ⟨ha, hb⟩
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] at * <;> (try split_ifs at *) <;> (try simp_all) <;>
    (try split_ifs at *) <;> (try simp_all) <;> (try split_ifs at *) <;> (try simp_all) <;>
    aesop

/-- All edges in the state after `k` balls are of balls `< k`. -/
lemma stateAfter_lt (x : ι → Fin n → ℝ) (ω : Outcome ι n) (k : ℕ) (e : ι × Fin n) :
    (e ∈ (stateAfter x ω k).1 → e.2.val < k) ∧ (e ∈ (stateAfter x ω k).2 → e.2.val < k) := by
  induction k with
  | zero => simp [stateAfter]
  | succ k ih =>
    simp only [stateAfter]
    split_ifs with hk
    · constructor
      · intro he
        rcases step_fst_sub x _ _ _ e he with h | h
        · exact Nat.lt_succ_of_lt (ih.1 h)
        · rw [h]; exact Nat.lt_succ_self k
      · intro he
        rcases step_snd_sub x _ _ _ e he with h | h
        · exact Nat.lt_succ_of_lt (ih.2 h)
        · rw [h]; exact Nat.lt_succ_self k
    · exact ⟨fun he => Nat.lt_succ_of_lt (ih.1 he), fun he => Nat.lt_succ_of_lt (ih.2 he)⟩

/-- Edges of ball `s` are frozen after step `s`. -/
lemma stateAfter_frozen (x : ι → Fin n → ℝ) (ω : Outcome ι n) (k : ℕ) (e : ι × Fin n)
    (hk : e.2.val < k) : ∀ m, k ≤ m →
    ((e ∈ (stateAfter x ω m).1 ↔ e ∈ (stateAfter x ω k).1) ∧
     (e ∈ (stateAfter x ω m).2 ↔ e ∈ (stateAfter x ω k).2)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact ⟨Iff.rfl, Iff.rfl⟩
  | succ m hkm ih =>
    simp only [stateAfter]
    split_ifs with hmn
    · constructor
      · rw [← ih.1]
        constructor
        · intro he
          rcases step_fst_sub x _ _ _ e he with h | h
          · exact h
          · exfalso; rw [h] at hk; simp at hk; omega
        · exact step_fst_sup x _ _ _ e
      · rw [← ih.2]
        constructor
        · intro he
          rcases step_snd_sub x _ _ _ e he with h | h
          · exact h
          · exfalso; rw [h] at hk; simp at hk; omega
        · exact step_snd_sup x _ _ _ e
    · exact ih

lemma M1_iff (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n) :
    (i, t) ∈ M1 x ω ↔ (i, t) ∈ (step x t (ω t) (stateAfter x ω t.val)).1 := by
  have h := (stateAfter_frozen x ω (t.val + 1) (i, t) (Nat.lt_succ_self _) n t.isLt).1
  rw [M1, h]
  simp [stateAfter, t.isLt]

lemma M2_iff (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n) :
    (i, t) ∈ M2 x ω ↔ (i, t) ∈ (step x t (ω t) (stateAfter x ω t.val)).2 := by
  have h := (stateAfter_frozen x ω (t.val + 1) (i, t) (Nat.lt_succ_self _) n t.isLt).2
  rw [M2, h]
  simp [stateAfter, t.isLt]

/-- An edge is never in both `M1` and `M2`. -/
lemma not_mem_M1_and_M2 (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n) :
    ¬ ((i, t) ∈ M1 x ω ∧ (i, t) ∈ M2 x ω) := by
  rw [M1_iff, M2_iff]
  apply step_excl
  · intro j hj
    have := (stateAfter_lt x ω t.val (j, t)).1 hj
    simp at this
  · intro j hj
    have := (stateAfter_lt x ω t.val (j, t)).2 hj
    simp at this

end LPMStruct


open MeasureTheory ProbabilityTheory

namespace LPMAlg
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct

variable {ι : Type*} {n : ℕ}

/-- replace the draw of ball `t` -/
noncomputable def upd (ω : Outcome ι n) (t : Fin n) (d : BallDraw ι) : Outcome ι n :=
  fun s => if s = t then d else ω s

@[simp] lemma upd_self (ω : Outcome ι n) (t : Fin n) (d : BallDraw ι) : upd ω t d t = d := by
  simp [upd]

lemma upd_ne (ω : Outcome ι n) (t : Fin n) (d : BallDraw ι) (s : Fin n) (h : s ≠ t) :
    upd ω t d s = ω s := by
  simp [upd, h]

lemma stateAfter_congr (x : ι → Fin n → ℝ) (ω ω' : Outcome ι n) (k : ℕ)
    (h : ∀ s : Fin n, s.val < k → ω s = ω' s) : stateAfter x ω k = stateAfter x ω' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [stateAfter]
    split_ifs with hk
    · rw [ih', h ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · exact ih'

/-- the state before ball `t` does not depend on the draw of ball `t` -/
lemma stateAfter_update (x : ι → Fin n → ℝ) (ω : Outcome ι n) (t : Fin n) (d : BallDraw ι) :
    stateAfter x (upd ω t d) t.val = stateAfter x ω t.val := by
  apply stateAfter_congr
  intro s hs
  have : s ≠ t := by intro h; rw [h] at hs; exact lt_irrefl _ hs
  exact upd_ne ω t d s this

/-- characterization of a first-pick match -/
lemma mem_M1_iff (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n) :
    (i, t) ∈ M1 x ω ↔ (ω t).arrives = true ∧ (ω t).firstPick = some i ∧
      IsVacantIn (stateAfter x ω t.val) i ∧ (ω t).coin i = true := by
  classical
  rw [M1_iff]
  have h1 : ∀ j, (j, t) ∉ (stateAfter x ω t.val).1 := by
    intro j hj; have := (stateAfter_lt x ω t.val (j, t)).1 hj; simp at this
  have h2 : ∀ j, (j, t) ∉ (stateAfter x ω t.val).2 := by
    intro j hj; have := (stateAfter_lt x ω t.val (j, t)).2 hj; simp at this
  generalize stateAfter x ω t.val = S at h1 h2
  generalize ω t = d
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] <;>
    (try (by_cases hv : IsVacantIn S i1 ∧ cn i1 = true <;>
      simp only [hv, if_true, if_false])) <;>
    (try split_ifs) <;> simp_all <;> aesop

/-- characterization of a second-pick match -/
lemma mem_M2_iff (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n) :
    (i, t) ∈ M2 x ω ↔ (ω t).arrives = true ∧
      ¬ (∃ j, (ω t).firstPick = some j ∧ IsVacantIn (stateAfter x ω t.val) j ∧
          (ω t).coin j = true) ∧
      (ω t).secondPick = some i ∧ IsVacantIn (stateAfter x ω t.val) i ∧
      threshold < cumX x i t := by
  classical
  rw [M2_iff]
  have h1 : ∀ j, (j, t) ∉ (stateAfter x ω t.val).1 := by
    intro j hj; have := (stateAfter_lt x ω t.val (j, t)).1 hj; simp at this
  have h2 : ∀ j, (j, t) ∉ (stateAfter x ω t.val).2 := by
    intro j hj; have := (stateAfter_lt x ω t.val (j, t)).2 hj; simp at this
  generalize stateAfter x ω t.val = S at h1 h2
  generalize ω t = d
  rcases d with ⟨a, f1, cn, f2⟩
  cases a <;> rcases f1 with _ | i1 <;> rcases f2 with _ | i2 <;>
    simp only [step, BallDraw.arrives, BallDraw.firstPick, BallDraw.coin,
      BallDraw.secondPick] <;>
    (try (by_cases hv : IsVacantIn S i1 ∧ cn i1 = true <;>
      simp only [hv, if_true, if_false])) <;>
    (try split_ifs) <;> simp_all <;> aesop

/-- vacancy at time `t` in terms of the final matching -/
lemma vacant_iff (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n) :
    IsVacantIn (stateAfter x ω t.val) i ↔ ∀ s, s < t → (i, s) ∉ M1 x ω ∧ (i, s) ∉ M2 x ω := by
  unfold IsVacantIn
  constructor
  · intro h s hs
    have hs' : (i, s).2.val < t.val := hs
    have hf := stateAfter_frozen x ω t.val (i, s) hs' n t.isLt.le
    rw [M1, M2, hf.1, hf.2]
    exact h s
  · intro h s
    by_cases hs : s < t
    · have hs' : (i, s).2.val < t.val := hs
      have hf := stateAfter_frozen x ω t.val (i, s) hs' n t.isLt.le
      have := h s hs
      rw [M1, M2, hf.1, hf.2] at this
      exact this
    · constructor
      · intro hm
        have := (stateAfter_lt x ω t.val (i, s)).1 hm
        exact hs this
      · intro hm
        have := (stateAfter_lt x ω t.val (i, s)).2 hm
        exact hs this

lemma mem_M_vacant (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (t : Fin n)
    (h : (i, t) ∈ M1 x ω ∨ (i, t) ∈ M2 x ω) : IsVacantIn (stateAfter x ω t.val) i := by
  rcases h with h | h
  · exact ((mem_M1_iff x ω i t).mp h).2.2.1
  · exact ((mem_M2_iff x ω i t).mp h).2.2.2.1

/-- a bin is matched at most once -/
lemma bin_unique (x : ι → Fin n → ℝ) (ω : Outcome ι n) (i : ι) (s s' : Fin n)
    (h : (i, s) ∈ M1 x ω ∨ (i, s) ∈ M2 x ω) (h' : (i, s') ∈ M1 x ω ∨ (i, s') ∈ M2 x ω) :
    s = s' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hv := (vacant_iff x ω i s').mp (mem_M_vacant x ω i s' h') s hlt
    rcases h with h | h
    · exact hv.1 h
    · exact hv.2 h
  · have hv := (vacant_iff x ω i s).mp (mem_M_vacant x ω i s h) s' hlt
    rcases h' with h' | h'
    · exact hv.1 h'
    · exact hv.2 h'

variable [Fintype ι]

/-- probabilities as weighted sums -/
lemma prob_eq {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (s : Set (Outcome ι n)) [DecidablePred (· ∈ s)] :
    (algMeasure I x).real s = ∑ ω, outcomeWeight I x ω * (if ω ∈ s then 1 else 0) := by
  rw [real_apply hx htight]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

def d0 : BallDraw ι := (false, none, fun _ => false, none)

/-- splitting an outcome at ball `t` -/
noncomputable def splitO (t : Fin n) : Outcome ι n ≃ BallDraw ι × ({j // j ≠ t} → BallDraw ι) where
  toFun ω := (ω t, fun j => ω j.1)
  invFun p := fun s => if h : s = t then p.1 else p.2 ⟨s, h⟩
  left_inv ω := by
    funext s
    by_cases h : s = t
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨d, r⟩
    simp only [Prod.mk.injEq]
    constructor
    · simp
    · funext j; simp [j.2]

lemma splitO_symm_apply (t : Fin n) (p : BallDraw ι × ({j // j ≠ t} → BallDraw ι)) (s : Fin n) :
    (splitO t).symm p s = if h : s = t then p.1 else p.2 ⟨s, h⟩ := rfl

lemma splitO_symm_apply_self (t : Fin n) (d : BallDraw ι) (r : {j // j ≠ t} → BallDraw ι) :
    (splitO t).symm (d, r) t = d := by
  simp [splitO_symm_apply]

lemma split_eq' (t : Fin n) (d : BallDraw ι) (r : {j // j ≠ t} → BallDraw ι) :
    (splitO t).symm (d, r) = upd ((splitO t).symm (d0, r)) t d := by
  funext j
  by_cases h : j = t
  · subst h; rw [upd_self]; simp [splitO_symm_apply]
  · rw [upd_ne _ _ _ _ h]; simp [splitO_symm_apply, h]

lemma outcomeWeight_update (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (ω : Outcome ι n)
    (t : Fin n) (d : BallDraw ι) :
    outcomeWeight I x (upd ω t d) =
      ballWeight I x t d * ∏ s ∈ Finset.univ \ {t}, ballWeight I x s (ω s) := by
  classical
  unfold outcomeWeight
  have : ∀ s, ballWeight I x s (upd ω t d s) =
      Function.update (fun s => ballWeight I x s (ω s)) t (ballWeight I x t d) s := by
    intro s
    by_cases h : s = t
    · subst h; simp
    · rw [upd_ne _ _ _ _ h]; simp [Function.update_of_ne h]
  simp_rw [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ t)]

open Classical in
/-- factorization: the draw of ball `t` is independent of anything not depending on it -/
lemma factor (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n)
    (H : BallDraw ι → ℝ) (G : Outcome ι n → ℝ)
    (hG : ∀ ω d, G (upd ω t d) = G ω) :
    ∑ ω, outcomeWeight I x ω * (H (ω t) * G ω) =
      (∑ d, ballWeight I x t d * H d) * ∑ ω, outcomeWeight I x ω * G ω := by
  classical
  let e := splitO (ι := ι) t
  have hsum : ∀ F : Outcome ι n → ℝ, ∑ ω, F ω =
      ∑ r : {j // j ≠ t} → BallDraw ι, ∑ d : BallDraw ι, F (e.symm (d, r)) := by
    intro F
    rw [← Fintype.sum_prod_type_right (f := fun p => F (e.symm p))]
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
  rw [hsum, hsum]
  have hw : ∀ d r, outcomeWeight I x (e.symm (d, r)) =
      ballWeight I x t d * ∏ s ∈ Finset.univ \ {t}, ballWeight I x s (e.symm (d0, r) s) := by
    intro d r
    rw [show e.symm (d, r) = upd (e.symm (d0, r)) t d from split_eq' t d r]
    exact outcomeWeight_update I x _ t d
  have hg : ∀ d r, G (e.symm (d, r)) = G (e.symm (d0, r)) := by
    intro d r
    rw [show e.symm (d, r) = upd (e.symm (d0, r)) t d from split_eq' t d r, hG]
  have he : ∀ d r, e.symm (d, r) t = d := fun d r => splitO_symm_apply_self t d r
  simp only [hw, hg, he]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  set R := ∏ s ∈ Finset.univ \ {t}, ballWeight I x s (e.symm (d0, r) s)
  have h1 : ∑ d, ballWeight I x t d * R * (H d * G (e.symm (d0, r))) =
      (∑ d, ballWeight I x t d * H d) * (R * G (e.symm (d0, r))) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro d _; ring
  have h2 : ∑ d, ballWeight I x t d * R * G (e.symm (d0, r)) = R * G (e.symm (d0, r)) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_ballWeight]; ring
  rw [h1, h2]

end LPMAlg


open MeasureTheory ProbabilityTheory

namespace LPM44
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct LPMAlg
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma sumBall (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n)
    (fa : Bool → ℝ) (fp : Option ι → ℝ) (fc : (ι → Bool) → ℝ) (fs : Option ι → ℝ) :
    ∑ d : BallDraw ι, ballWeight I x t d * (fa d.1 * fp d.2.1 * fc d.2.2.1 * fs d.2.2.2) =
      (∑ b, (if b then I.p t else 1 - I.p t) * fa b) * (∑ o, pickWeight I x t o * fp o) *
      (∑ f : ι → Bool, (∏ j, if f j then acceptProb x j t else 1 - acceptProb x j t) * fc f) *
      (∑ o, pickWeight I x t o * fs o) := by
  rw [← sum4]
  apply Finset.sum_congr rfl
  intro d _
  have hb : ballWeight I x t d = (if d.1 then I.p t else 1 - I.p t) * pickWeight I x t d.2.1 *
      (∏ j, if d.2.2.1 j then acceptProb x j t else 1 - acceptProb x j t) *
      pickWeight I x t d.2.2.2 := rfl
  rw [hb]
  ring

lemma sum_arr_true (I : RideHailInstance ι n) (t : Fin n) :
    ∑ b : Bool, (if b then I.p t else 1 - I.p t) * (if b then 1 else 0) = I.p t := by
  simp

lemma sum_arr_one (I : RideHailInstance ι n) (t : Fin n) :
    ∑ b : Bool, (if b then I.p t else 1 - I.p t) * 1 = 1 := by
  simp

lemma sum_pick_some (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) (i : ι) :
    ∑ o, pickWeight I x t o * (if o = some i then 1 else 0) = x i t / I.p t := by
  rw [Fintype.sum_option]
  simp [pickWeight]

lemma sum_pick_one (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) :
    ∑ o, pickWeight I x t o * 1 = 1 := by
  simp only [mul_one]; exact sum_pickWeight I x t

lemma sum_coin_one (x : ι → Fin n → ℝ) (t : Fin n) :
    ∑ f : ι → Bool, (∏ j, if f j then acceptProb x j t else 1 - acceptProb x j t) * 1 = 1 := by
  have h := Fintype.prod_sum (fun j (b : Bool) =>
    if b then acceptProb x j t else 1 - acceptProb x j t)
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_sub_cancel,
    Finset.prod_const_one] at h
  simp only [mul_one]
  exact h.symm

lemma sum_coin_i (x : ι → Fin n → ℝ) (t : Fin n) (i : ι) :
    ∑ f : ι → Bool, (∏ j, if f j then acceptProb x j t else 1 - acceptProb x j t) *
      (if f i then 1 else 0) = acceptProb x i t := by
  let g : ι → Bool → ℝ := fun j b =>
    (if b then acceptProb x j t else 1 - acceptProb x j t) * (if j = i then (if b then 1 else 0) else 1)
  have hpt : ∀ f : ι → Bool, (∏ j, if f j then acceptProb x j t else 1 - acceptProb x j t) *
      (if f i then 1 else 0) = ∏ j, g j (f j) := by
    intro f
    simp only [g, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ i]
    simp
  simp_rw [hpt]
  rw [← Fintype.prod_sum]
  rw [Finset.prod_eq_single i]
  · simp [g]
  · intro j _ hj
    simp [g, hj]
  · simp

lemma x_eq (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) : I.p t * (x i t / I.p t) = x i t := by
  rcases (I.p_nonneg t).eq_or_lt with h | h
  · have : x i t ≤ I.p t := by
      rw [← htight t]
      exact Finset.single_le_sum (fun j _ => hx.nonneg j t) (Finset.mem_univ i)
    have h0 : x i t = 0 := le_antisymm (by rw [← h] at this; exact this) (hx.nonneg i t)
    rw [h0]; simp
  · field_simp

/-- `(F1)` -/
lemma m1_eq {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) :
    (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} =
      x i t * acceptProb x i t * (algMeasure I x).real (vacantSet x i t) := by
  rw [prob_eq hx htight, prob_eq hx htight]
  let H : BallDraw ι → ℝ := fun d => (if d.1 then 1 else 0) * (if d.2.1 = some i then 1 else 0) *
    (if d.2.2.1 i then 1 else 0) * 1
  let G : Outcome ι n → ℝ := fun ω => if IsVacantIn (stateAfter x ω t.val) i then 1 else 0
  have hpt : ∀ ω, (if ω ∈ {ω | (i, t) ∈ M1 x ω} then (1 : ℝ) else 0) = H (ω t) * G ω := by
    intro ω
    simp only [Set.mem_ofPred_eq, mem_M1_iff, H, G]
    by_cases h1 : (ω t).arrives = true <;> by_cases h2 : (ω t).firstPick = some i <;>
      by_cases h3 : IsVacantIn (stateAfter x ω t.val) i <;> by_cases h4 : (ω t).coin i = true <;>
      simp_all [BallDraw.arrives, BallDraw.firstPick, BallDraw.coin]
  simp_rw [hpt]
  rw [factor I x t H G (fun ω d => by simp only [G, stateAfter_update])]
  have hH : ∑ d, ballWeight I x t d * H d = x i t * acceptProb x i t := by
    have hs := sumBall I x t (fun b => if b then 1 else 0) (fun o => if o = some i then 1 else 0)
      (fun f => if f i then 1 else 0) (fun _ => 1)
    simp only [H]
    rw [hs, sum_arr_true, sum_pick_some, sum_coin_i, sum_pick_one, mul_one,
      x_eq I x hx htight]
  rw [hH]
  rfl

/-- `(F2)`: second-pick matches -/
lemma m2_le {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) :
    (algMeasure I x).real {ω | (i, t) ∈ M2 x ω} ≤
      x i t * (algMeasure I x).real (vacantSet x i t) := by
  rw [prob_eq hx htight, prob_eq hx htight]
  let H : BallDraw ι → ℝ := fun d => (if d.1 then 1 else 0) * 1 * 1 *
    (if d.2.2.2 = some i then 1 else 0)
  let G : Outcome ι n → ℝ := fun ω => if IsVacantIn (stateAfter x ω t.val) i then 1 else 0
  have hpt : ∀ ω, (if ω ∈ {ω | (i, t) ∈ M2 x ω} then (1 : ℝ) else 0) ≤ H (ω t) * G ω := by
    intro ω
    by_cases hm : (i, t) ∈ M2 x ω
    · have := (mem_M2_iff x ω i t).mp hm
      simp only [Set.mem_ofPred_eq, hm, if_true, H, G]
      simp only [BallDraw.arrives, BallDraw.secondPick] at this
      simp [this.1, this.2.2.1, this.2.2.2.1]
    · simp only [Set.mem_ofPred_eq, hm, if_false, H, G]
      positivity
  calc ∑ ω, outcomeWeight I x ω * (if ω ∈ {ω | (i, t) ∈ M2 x ω} then (1 : ℝ) else 0)
      ≤ ∑ ω, outcomeWeight I x ω * (H (ω t) * G ω) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω)
          (outcomeWeight_nonneg hx htight ω))
    _ = (∑ d, ballWeight I x t d * H d) * ∑ ω, outcomeWeight I x ω * G ω :=
        factor I x t H G (fun ω d => by simp only [G, stateAfter_update])
    _ = x i t * ∑ ω, outcomeWeight I x ω * (if ω ∈ vacantSet x i t then 1 else 0) := by
        have hs := sumBall I x t (fun b => if b then 1 else 0) (fun _ => 1)
          (fun _ => 1) (fun o => if o = some i then 1 else 0)
        simp only [H]
        rw [hs, sum_arr_true, sum_pick_one, sum_coin_one, sum_pick_some, mul_one, mul_one,
          x_eq I x hx htight]
        rfl

lemma m2_early {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) (he : IsEarly x i t) :
    (algMeasure I x).real {ω | (i, t) ∈ M2 x ω} = 0 := by
  have : {ω | (i, t) ∈ M2 x ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hm
    have := ((mem_M2_iff x ω i t).mp hm).2.2.2.2
    exact absurd he (not_le.mpr this)
  rw [this]; simp

/-- `(F3)` -/
lemma v_eq {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) :
    (algMeasure I x).real (vacantSet x i t) = 1 - ∑ s ∈ Finset.Iio t,
      ((algMeasure I x).real {ω | (i, s) ∈ M1 x ω} +
        (algMeasure I x).real {ω | (i, s) ∈ M2 x ω}) := by
  simp only [prob_eq hx htight]
  have hpt : ∀ ω, (if ω ∈ vacantSet x i t then (1 : ℝ) else 0) = 1 - ∑ s ∈ Finset.Iio t,
      ((if ω ∈ {ω | (i, s) ∈ M1 x ω} then (1 : ℝ) else 0) +
        (if ω ∈ {ω | (i, s) ∈ M2 x ω} then (1 : ℝ) else 0)) := by
    intro ω
    have hpair : ∀ s, ((if ω ∈ {ω | (i, s) ∈ M1 x ω} then (1 : ℝ) else 0) +
        (if ω ∈ {ω | (i, s) ∈ M2 x ω} then (1 : ℝ) else 0)) =
        if ((i, s) ∈ M1 x ω ∨ (i, s) ∈ M2 x ω) then 1 else 0 := by
      intro s
      have := not_mem_M1_and_M2 x ω i s
      by_cases h1 : (i, s) ∈ M1 x ω <;> by_cases h2 : (i, s) ∈ M2 x ω <;> simp_all
    simp_rw [hpair]
    rw [Finset.sum_boole]
    by_cases hv : ω ∈ vacantSet x i t
    · have hv' := (vacant_iff x ω i t).mp hv
      rw [if_pos hv]
      have : (Finset.Iio t).filter (fun s => (i, s) ∈ M1 x ω ∨ (i, s) ∈ M2 x ω) = ∅ := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_Iio, Finset.notMem_empty, iff_false, not_and]
        intro hs hm
        rcases hm with hm | hm
        · exact (hv' s hs).1 hm
        · exact (hv' s hs).2 hm
      rw [this]; simp
    · rw [if_neg hv]
      have hv' : ¬ ∀ s, s < t → (i, s) ∉ M1 x ω ∧ (i, s) ∉ M2 x ω := by
        intro h; exact hv ((vacant_iff x ω i t).mpr h)
      push Not at hv'
      obtain ⟨s0, hs0, hm0⟩ := hv'
      have hm0' : (i, s0) ∈ M1 x ω ∨ (i, s0) ∈ M2 x ω := by
        by_cases h : (i, s0) ∈ M1 x ω
        · exact Or.inl h
        · exact Or.inr (hm0 h)
      have : (Finset.Iio t).filter (fun s => (i, s) ∈ M1 x ω ∨ (i, s) ∈ M2 x ω) = {s0} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hm⟩
          exact bin_unique x ω i s s0 hm hm0'
        · rintro rfl
          exact ⟨hs0, hm0'⟩
      rw [this]; simp
  simp_rw [hpt, mul_sub, mul_one, Finset.sum_sub_distrib, sum_outcomeWeight, Finset.mul_sum,
    mul_add]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]

lemma c_val : (c : ℝ) = 1 / 100 := rfl
lemma thr_val : (threshold : ℝ) = 49 / 51 := by
  unfold threshold; rw [c_val]; norm_num

lemma cumX_mono {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) {s t : Fin n} (h : s ≤ t) : cumX x i s ≤ cumX x i t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr; simp only [Finset.mem_Iio] at hr ⊢; exact lt_of_lt_of_le hr h
  · intro r _ _; exact hx.nonneg i r

lemma acceptProb_early {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) (he : IsEarly x i t) :
    acceptProb x i t = (1 / 2 + c) / (1 - cumX x i t * (1 / 2 + c)) := by
  unfold IsEarly at he
  rw [thr_val] at he
  have h0 := cumX_nonneg hx i t
  unfold acceptProb
  apply min_eq_right
  rw [c_val] at *
  rw [div_le_one (by nlinarith)]
  nlinarith

lemma acceptProb_late {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) (hl : IsLate x i t) : acceptProb x i t = 1 := by
  unfold IsLate at hl
  rw [thr_val] at hl
  have h1 := cumX_le_one hx i t
  unfold acceptProb
  apply min_eq_left
  rw [c_val]
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-- the early mass before a late ball exceeds the threshold -/
lemma early_mass {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) (hl : IsLate x i t) :
    threshold < ∑ s ∈ (Finset.Iio t).filter (fun s => IsEarly x i s), x i s := by
  let L := (Finset.univ : Finset (Fin n)).filter (fun s => IsLate x i s ∧ s ≤ t)
  have hL : L.Nonempty := ⟨t, by simp [L, hl]⟩
  let t0 := L.min' hL
  have ht0 : t0 ∈ L := Finset.min'_mem L hL
  simp only [L, Finset.mem_filter] at ht0
  have hsub : Finset.Iio t0 ⊆ (Finset.Iio t).filter (fun s => IsEarly x i s) := by
    intro s hs
    simp only [Finset.mem_Iio] at hs
    simp only [Finset.mem_filter, Finset.mem_Iio]
    refine ⟨lt_of_lt_of_le hs ht0.2.2, ?_⟩
    by_contra hne
    have hlate : IsLate x i s := lt_of_not_ge hne
    have : t0 ≤ s := Finset.min'_le L s (by simp [L, hlate, (lt_of_lt_of_le hs ht0.2.2).le])
    exact absurd hs (not_lt.mpr this)
  calc threshold < cumX x i t0 := ht0.2.1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => hx.nonneg i s)

end LPM44


open MeasureTheory ProbabilityTheory

namespace LPM44
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct LPMAlg
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- the inductive statement behind Lemma 4.4 and Corollary 4.5 -/
theorem main {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) :
    (IsEarly x i t → (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} = x i t * (1 / 2 + c)) ∧
    x i t * (1 / 2 - 3 * c) ≤ (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} ∧
    (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} ≤ x i t * (1 / 2 + c) ∧
    1 / 2 - 3 * c ≤ (algMeasure I x).real (vacantSet x i t) ∧
    (IsLate x i t → (algMeasure I x).real (vacantSet x i t) ≤ 1 / 2 + c) ∧
    (IsEarly x i t → (algMeasure I x).real (vacantSet x i t) = 1 - cumX x i t * (1 / 2 + c)) := by
  set μ := algMeasure I x
  induction h : t.val using Nat.strong_induction_on generalizing t with
  | _ k IH =>
  have IH' : ∀ s : Fin n, s < t → _ := fun s hs => IH s.val (h ▸ hs) s rfl
  have hv := v_eq hx htight i t
  have hm1 := m1_eq hx htight i t
  have hxt := hx.nonneg i t
  have hcum0 := cumX_nonneg hx i t
  have hcum1 := cumX_le_one hx i t
  have hthr := thr_val
  have hc := c_val
  by_cases hE : IsEarly x i t
  · have hEs : ∀ s ∈ Finset.Iio t, IsEarly x i s := by
      intro s hs
      exact le_trans (cumX_mono hx i (Finset.mem_Iio.mp hs).le) hE
    have hsum : ∑ s ∈ Finset.Iio t, (μ.real {ω | (i, s) ∈ M1 x ω} + μ.real {ω | (i, s) ∈ M2 x ω})
        = cumX x i t * (1 / 2 + c) := by
      unfold cumX
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(IH' s (Finset.mem_Iio.mp hs)).1 (hEs s hs), m2_early hx htight i s (hEs s hs), add_zero]
    rw [hsum] at hv
    have hE' := hE
    unfold IsEarly at hE'
    rw [hthr] at hE'
    have hvpos : 0 < 1 - cumX x i t * (1 / 2 + c) := by rw [hc]; nlinarith
    have hm1' : μ.real {ω | (i, t) ∈ M1 x ω} = x i t * (1 / 2 + c) := by
      rw [hm1, hv, acceptProb_early hx i t hE]
      field_simp
      apply mul_div_cancel_right₀
      rw [hc] at hvpos ⊢; nlinarith
    refine ⟨fun _ => hm1', ?_, ?_, ?_, ?_, fun _ => hv⟩
    · rw [hm1']; rw [hc]; nlinarith
    · rw [hm1']
    · rw [hv, hc]; rw [hc] at hvpos; nlinarith
    · intro hl; exact absurd hE (not_le.mpr hl)
  · have hL : IsLate x i t := lt_of_not_ge hE
    have hq := acceptProb_late hx i t hL
    have hm1' : μ.real {ω | (i, t) ∈ M1 x ω} = x i t * μ.real (vacantSet x i t) := by
      rw [hm1, hq, mul_one]
    have hearly := early_mass hx i t hL
    set Es := (Finset.Iio t).filter (fun s => IsEarly x i s)
    -- upper bound on vacancy
    have hup : μ.real (vacantSet x i t) ≤ 1 / 2 + c := by
      have h1 : ∑ s ∈ Es, x i s * (1 / 2 + c) ≤
          ∑ s ∈ Finset.Iio t, (μ.real {ω | (i, s) ∈ M1 x ω} + μ.real {ω | (i, s) ∈ M2 x ω}) := by
        calc ∑ s ∈ Es, x i s * (1 / 2 + c)
            = ∑ s ∈ Es, μ.real {ω | (i, s) ∈ M1 x ω} := by
              apply Finset.sum_congr rfl
              intro s hs
              simp only [Es, Finset.mem_filter, Finset.mem_Iio] at hs
              exact ((IH' s hs.1).1 hs.2).symm
          _ ≤ ∑ s ∈ Es, (μ.real {ω | (i, s) ∈ M1 x ω} + μ.real {ω | (i, s) ∈ M2 x ω}) :=
              Finset.sum_le_sum (fun s _ => le_add_of_nonneg_right measureReal_nonneg)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun s _ _ => add_nonneg measureReal_nonneg measureReal_nonneg)
      rw [← Finset.sum_mul] at h1
      rw [hv]
      rw [hthr] at hearly
      rw [hc] at h1 ⊢
      nlinarith
    -- lower bound on vacancy
    have hlow : 1 / 2 - 3 * c ≤ μ.real (vacantSet x i t) := by
      have h1 : ∑ s ∈ Finset.Iio t, (μ.real {ω | (i, s) ∈ M1 x ω} + μ.real {ω | (i, s) ∈ M2 x ω})
          ≤ ∑ s ∈ Finset.Iio t, (x i s * (1 / 2 + c) +
              (if IsEarly x i s then 0 else x i s) * (1 / 2 + c)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs' := Finset.mem_Iio.mp hs
        apply add_le_add ((IH' s hs').2.2.1)
        split_ifs with hEs
        · rw [m2_early hx htight i s hEs, zero_mul]
        · calc μ.real {ω | (i, s) ∈ M2 x ω} ≤ x i s * μ.real (vacantSet x i s) :=
                m2_le hx htight i s
            _ ≤ x i s * (1 / 2 + c) := mul_le_mul_of_nonneg_left
                ((IH' s hs').2.2.2.2.1 (lt_of_not_ge hEs)) (hx.nonneg i s)
      have h2 : ∑ s ∈ Finset.Iio t, (if IsEarly x i s then 0 else x i s) =
          cumX x i t - ∑ s ∈ Es, x i s := by
        unfold cumX
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Iio t) (fun s => IsEarly x i s)
          (fun s => x i s)]
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, zero_add, Es]
        ring
      have hR : ∑ s ∈ Finset.Iio t, (x i s * (1 / 2 + c) +
              (if IsEarly x i s then 0 else x i s) * (1 / 2 + c)) =
          cumX x i t * (1 / 2 + c) + (cumX x i t - ∑ s ∈ Es, x i s) * (1 / 2 + c) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, h2]
        rfl
      rw [hR] at h1
      rw [hv]
      rw [hthr] at hearly
      rw [hc] at h1 ⊢
      nlinarith
    refine ⟨fun h => absurd h hE, ?_, ?_, hlow, fun _ => hup, fun h => absurd h hE⟩
    · rw [hm1']; exact mul_le_mul_of_nonneg_left hlow hxt
    · rw [hm1']; exact mul_le_mul_of_nonneg_left hup hxt

end LPM44


open MeasureTheory ProbabilityTheory

namespace LPM48
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct LPMAlg LPM44
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma integral_eq_sum {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (f : Outcome ι n → ℝ) :
    ∫ ω, f ω ∂(algMeasure I x) = ∑ ω, outcomeWeight I x ω * f ω := by
  rw [algMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro ω _
    rw [integral_smul_measure, integral_dirac' _ _ (Measurable.of_discrete).stronglyMeasurable,
      ENNReal.toReal_ofReal (outcomeWeight_nonneg hx htight ω), smul_eq_mul]
  · intro ω _
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact Integrable.of_finite

lemma memLp_ind {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (s : Set (Outcome ι n)) :
    MemLp (s.indicator (1 : Outcome ι n → ℝ)) 2 (algMeasure I x) := by
  haveI : IsFiniteMeasure (algMeasure I x) := by
    constructor
    rw [algMeasure_apply]
    exact ENNReal.sum_lt_top.mpr (fun ω _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by by_cases h : ω ∈ (Set.univ : Set (Outcome ι n)) <;> simp [Set.indicator, h]))
  apply MemLp.of_bound (C := 1)
  · exact (Measurable.of_discrete).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    by_cases h : ω ∈ s <;> simp [Set.indicator, h]

/-- the early-occupancy event is contained in the occupancy event -/
lemma early_sub (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) :
    occupiedEarlySet x i t ⊆ occupiedSet x i t := by
  intro ω ⟨s, _, hs⟩ hv
  rcases hs with hs | hs
  · exact (hv s).1 hs
  · exact (hv s).2 hs

/-- before an early ball, every occupancy is early -/
lemma occ_eq_early {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) (hE : IsEarly x i t) :
    occupiedSet x i t ⊆ occupiedEarlySet x i t := by
  intro ω hω
  simp only [occupiedSet, vacantSet, Set.mem_compl_iff, Set.mem_ofPred_eq, IsVacantIn] at hω
  push Not at hω
  obtain ⟨s, hs⟩ := hω
  refine ⟨s, ?_, ?_⟩
  · have hlt : s.val < t.val := by
      by_cases h1 : (i, s) ∈ (stateAfter x ω t.val).1
      · exact (stateAfter_lt x ω t.val (i, s)).1 h1
      · exact (stateAfter_lt x ω t.val (i, s)).2 (hs h1)
    exact le_trans (cumX_mono hx i (le_of_lt hlt)) hE
  · by_cases h1 : (i, s) ∈ (stateAfter x ω t.val).1
    · exact Or.inl h1
    · exact Or.inr (hs h1)

lemma ind_apply (s : Set (Outcome ι n)) (ω : Outcome ι n) :
    s.indicator (1 : Outcome ι n → ℝ) ω = if ω ∈ s then 1 else 0 := by
  by_cases h : ω ∈ s <;> simp [Set.indicator, h]

/-- `Pr[O^L_{i,t}] ≤ 4c` -/
lemma late_occ {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) :
    ∑ ω, outcomeWeight I x ω *
      ((if ω ∈ occupiedSet x i t then 1 else 0) - (if ω ∈ occupiedEarlySet x i t then 1 else 0))
      ≤ 4 * c := by
  have hw := outcomeWeight_nonneg hx htight
  by_cases hE : IsEarly x i t
  · have : ∀ ω, ((if ω ∈ occupiedSet x i t then (1 : ℝ) else 0) -
        (if ω ∈ occupiedEarlySet x i t then 1 else 0)) = 0 := by
      intro ω
      by_cases h : ω ∈ occupiedSet x i t
      · rw [if_pos h, if_pos (occ_eq_early hx i t hE h)]; ring
      · have h' : ω ∉ occupiedEarlySet x i t := fun h' => h (early_sub x i t h')
        rw [if_neg h, if_neg h']; ring
    simp_rw [this, mul_zero, Finset.sum_const_zero]
    rw [c_val]; norm_num
  · have hL : IsLate x i t := lt_of_not_ge hE
    have hm := main hx htight i t
    -- `Pr[O] ≤ 1/2 + 3c`
    have hO : ∑ ω, outcomeWeight I x ω * (if ω ∈ occupiedSet x i t then 1 else 0) ≤
        1 / 2 + 3 * c := by
      have hv := hm.2.2.2.1
      rw [prob_eq hx htight] at hv
      have : ∀ ω, (if ω ∈ occupiedSet x i t then (1 : ℝ) else 0) =
          1 - (if ω ∈ vacantSet x i t then 1 else 0) := by
        intro ω
        by_cases h : ω ∈ vacantSet x i t
        · have : ω ∉ occupiedSet x i t := fun h' => h' h
          simp [this, h]
        · have : ω ∈ occupiedSet x i t := h
          simp [this, h]
      simp_rw [this, mul_sub, mul_one, Finset.sum_sub_distrib, sum_outcomeWeight]
      linarith
    -- `Pr[O^E] > 1/2 - c`
    set Es := (Finset.Iio t).filter (fun s => IsEarly x i s)
    have hOE : ∑ s ∈ Es, x i s * (1 / 2 + c) ≤
        ∑ ω, outcomeWeight I x ω * (if ω ∈ occupiedEarlySet x i t then 1 else 0) := by
      have hpt : ∀ ω, ∑ s ∈ Es, (if ω ∈ {ω | (i, s) ∈ M1 x ω} then (1 : ℝ) else 0) ≤
          (if ω ∈ occupiedEarlySet x i t then 1 else 0) := by
        intro ω
        rw [Finset.sum_boole]
        by_cases h : ∃ s ∈ Es, (i, s) ∈ M1 x ω
        · obtain ⟨s0, hs0, hm0⟩ := h
          have hmem : ω ∈ occupiedEarlySet x i t := by
            simp only [Es, Finset.mem_filter, Finset.mem_Iio] at hs0
            refine ⟨s0, hs0.2, Or.inl ?_⟩
            have hf := (stateAfter_frozen x ω t.val (i, s0) hs0.1 n t.isLt.le).1
            rw [← hf]; exact hm0
          rw [if_pos hmem]
          have : (Es.filter (fun s => ω ∈ {ω | (i, s) ∈ M1 x ω})).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Set.mem_ofPred_eq] at ha hb
            exact bin_unique x ω i a b (Or.inl ha.2) (Or.inl hb.2)
          exact_mod_cast this
        · push Not at h
          have : Es.filter (fun s => ω ∈ {ω | (i, s) ∈ M1 x ω}) = ∅ := by
            ext s; simp only [Finset.mem_filter, Set.mem_ofPred_eq, Finset.notMem_empty,
              iff_false, not_and]
            exact h s
          rw [this]
          split_ifs <;> simp
      calc ∑ s ∈ Es, x i s * (1 / 2 + c)
          = ∑ s ∈ Es, ∑ ω, outcomeWeight I x ω * (if ω ∈ {ω | (i, s) ∈ M1 x ω} then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro s hs
            simp only [Es, Finset.mem_filter, Finset.mem_Iio] at hs
            rw [← prob_eq hx htight, (main hx htight i s).1 hs.2]
        _ = ∑ ω, outcomeWeight I x ω *
              ∑ s ∈ Es, (if ω ∈ {ω | (i, s) ∈ M1 x ω} then 1 else 0) := by
            rw [Finset.sum_comm]
            simp_rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw ω))
    have hearly := early_mass hx i t hL
    rw [← Finset.sum_mul] at hOE
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [thr_val] at hearly
    rw [c_val] at hO hOE ⊢
    nlinarith

end LPM48


open MeasureTheory ProbabilityTheory

open OnlineMaxWeightMatch.Approx LPMCommon LPM44 LPM48 in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (t : Fin n) {i j : ι} (hij : i ≠ j) :
    cov[vacancy x i t, vacancy x j t; algMeasure I x] ≤ 12 * c := by
  classical
  haveI := isProb hx htight
  have hcov := OnlineMaxWeightMatch.Approx.corollary_4_10 I x hx htight t hij
  unfold vacancy occupancyEarly at *
  rw [covariance_eq_sub (memLp_ind (vacantSet x i t)) (memLp_ind (vacantSet x j t))]
  rw [covariance_eq_sub (memLp_ind (occupiedEarlySet x i t))
    (memLp_ind (occupiedEarlySet x j t))] at hcov
  simp only [integral_eq_sum hx htight, Pi.mul_apply, ind_apply] at hcov ⊢
  have hw := outcomeWeight_nonneg hx htight (I := I)
  have h1 := sum_outcomeWeight I x
  have hLi := late_occ hx htight i t
  have hLj := late_occ hx htight j t
  set A := vacantSet x i t
  set B := vacantSet x j t
  set Ei := occupiedEarlySet x i t
  set Ej := occupiedEarlySet x j t
  have hEi : ∀ ω, ω ∈ Ei → ω ∉ A := fun ω h => early_sub x i t h
  have hEj : ∀ ω, ω ∈ Ej → ω ∉ B := fun ω h => early_sub x j t h
  have hoccA : ∀ ω, (if ω ∈ occupiedSet x i t then (1 : ℝ) else 0) = 1 - (if ω ∈ A then 1 else 0) := by
    intro ω; by_cases h : ω ∈ A
    · have : ω ∉ occupiedSet x i t := fun h' => h' h
      simp [this, h]
    · have : ω ∈ occupiedSet x i t := h
      simp [this, h]
  have hoccB : ∀ ω, (if ω ∈ occupiedSet x j t then (1 : ℝ) else 0) = 1 - (if ω ∈ B then 1 else 0) := by
    intro ω; by_cases h : ω ∈ B
    · have : ω ∉ occupiedSet x j t := fun h' => h' h
      simp [this, h]
    · have : ω ∈ occupiedSet x j t := h
      simp [this, h]
  simp only [hoccA] at hLi
  simp only [hoccB] at hLj
  -- notation for the expectations
  set S : (Outcome ι n → ℝ) → ℝ := fun f => ∑ ω, outcomeWeight I x ω * f ω with hS
  let a : Outcome ι n → ℝ := fun ω => if ω ∈ A then 1 else 0
  let b : Outcome ι n → ℝ := fun ω => if ω ∈ B then 1 else 0
  let ei : Outcome ι n → ℝ := fun ω => if ω ∈ Ei then 1 else 0
  let ej : Outcome ι n → ℝ := fun ω => if ω ∈ Ej then 1 else 0
  -- linearity
  have Sadd : ∀ f g, S (fun ω => f ω + g ω) = S f + S g := by
    intro f g; simp only [hS, mul_add, Finset.sum_add_distrib]
  have Ssub : ∀ f g, S (fun ω => f ω - g ω) = S f - S g := by
    intro f g; simp only [hS, mul_sub, Finset.sum_sub_distrib]
  have Ssmul : ∀ (k : ℝ) f, S (fun ω => k * f ω) = k * S f := by
    intro k f; simp only [hS, Finset.mul_sum]; apply Finset.sum_congr rfl; intro ω _; ring
  have Sone : S (fun _ => 1) = 1 := by simp only [hS, mul_one]; exact h1
  have Smono : ∀ f g, (∀ ω, f ω ≤ g ω) → S f ≤ S g := by
    intro f g h
    exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω))
  -- pointwise facts
  have p1 : ∀ ω, (1 - a ω) * (1 - b ω) ≤ ei ω * ej ω + 2 * ((1 - a ω) - ei ω) +
      ((1 - b ω) - ej ω) := by
    intro ω
    simp only [a, b, ei, ej]
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> by_cases h3 : ω ∈ Ei <;>
      by_cases h4 : ω ∈ Ej <;> simp [ha, hb, h3, h4] <;>
      first | exact absurd ha (hEi ω h3) | exact absurd hb (hEj ω h4) | norm_num
  have p2 : ∀ ω, ei ω ≤ 1 - a ω := by
    intro ω; simp only [a, ei]
    by_cases ha : ω ∈ A <;> by_cases h3 : ω ∈ Ei <;> simp [ha, h3]
    exact absurd ha (hEi ω h3)
  have p3 : ∀ ω, ej ω ≤ 1 - b ω := by
    intro ω; simp only [b, ej]
    by_cases hb : ω ∈ B <;> by_cases h4 : ω ∈ Ej <;> simp [hb, h4]
    exact absurd hb (hEj ω h4)
  have p4 : ∀ ω, 0 ≤ ei ω := fun ω => by simp only [ei]; split_ifs <;> norm_num
  have p5 : ∀ ω, 0 ≤ ej ω := fun ω => by simp only [ej]; split_ifs <;> norm_num
  -- expectations
  have e1 : S (fun ω => a ω * b ω) = S (fun ω => (1 - a ω) * (1 - b ω)) - 1 + S a + S b := by
    have : (fun ω => a ω * b ω) = fun ω => (1 - a ω) * (1 - b ω) - 1 + a ω + b ω := by
      funext ω; ring
    rw [this]
    have := Sadd (fun ω => (1 - a ω) * (1 - b ω) - 1 + a ω) b
    have h2 := Sadd (fun ω => (1 - a ω) * (1 - b ω) - 1) a
    have h3 := Ssub (fun ω => (1 - a ω) * (1 - b ω)) (fun _ => 1)
    simp only at this h2 h3
    rw [this, h2, h3, Sone]
  have e2 := Smono _ _ p1
  have e3 : S (fun ω => ei ω * ej ω + 2 * ((1 - a ω) - ei ω) + ((1 - b ω) - ej ω)) =
      S (fun ω => ei ω * ej ω) + 2 * (1 - S a - S ei) + (1 - S b - S ej) := by
    rw [Sadd, Sadd, Ssmul, Ssub, Ssub, Ssub, Ssub, Sone]
  have hEi_le := Smono _ _ p2
  have hEj_le := Smono _ _ p3
  rw [Ssub, Sone] at hEi_le hEj_le
  have hEi0 := Smono _ _ p4
  have hEj0 := Smono _ _ p5
  have z : S (fun _ => (0 : ℝ)) = 0 := by simp [hS]
  rw [z] at hEi0 hEj0
  -- the late-occupancy bounds
  have hLi' : 1 - S a - S ei ≤ 4 * c := by
    calc 1 - S a - S ei = S (fun ω => (1 - a ω) - ei ω) := by rw [Ssub, Ssub, Sone]
      _ ≤ 4 * c := hLi
  have hLj' : 1 - S b - S ej ≤ 4 * c := by
    calc 1 - S b - S ej = S (fun ω => (1 - b ω) - ej ω) := by rw [Ssub, Ssub, Sone]
      _ ≤ 4 * c := hLj
  -- conclude
  change S (fun ω => a ω * b ω) - S a * S b ≤ 12 * c
  change S (fun ω => ei ω * ej ω) - S ei * S ej ≤ 0 at hcov
  rw [e1]
  have hprod : (1 - S a) * (1 - S b) ≥ S ei * S ej :=
    mul_le_mul hEi_le hEj_le hEj0 (by linarith)
  have hexp : (1 - S a) * (1 - S b) = 1 - S a - S b + S a * S b := by ring
  rw [hexp] at hprod
  rw [e3] at e2
  linarith
