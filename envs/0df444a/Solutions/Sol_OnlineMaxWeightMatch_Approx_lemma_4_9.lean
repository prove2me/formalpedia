-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:07:19.649233+00:00
-- url     : https://prove2.me/submissions/555dffa3-3fa1-4b4c-a2b3-4c927bbd27df

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated
import Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_6
import Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_7_1
import Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_7_2

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

namespace LPM47
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct LPMAlg LPM44
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma cond_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s t : Set Ω) (hs : MeasurableSet s) :
    (μ[|s]).real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  rw [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rfl

/-- probability of an event of the draw of ball `t` jointly with a history event -/
lemma prob_split {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (Q : BallDraw ι → Prop) [DecidablePred Q]
    (R : Outcome ι n → Prop) [DecidablePred R] (hR : ∀ ω d, R (upd ω t d) ↔ R ω) :
    (algMeasure I x).real {ω | Q (ω t) ∧ R ω} =
      (∑ d, ballWeight I x t d * (if Q d then 1 else 0)) * (algMeasure I x).real {ω | R ω} := by
  rw [prob_eq hx htight, prob_eq hx htight]
  let H : BallDraw ι → ℝ := fun d => if Q d then 1 else 0
  let G : Outcome ι n → ℝ := fun ω => if R ω then 1 else 0
  have hpt : ∀ ω : Outcome ι n, (if ω ∈ {ω | Q (ω t) ∧ R ω} then (1 : ℝ) else 0) =
      H (ω t) * G ω := by
    intro ω
    simp only [Set.mem_ofPred_eq, H, G]
    by_cases h1 : Q (ω t) <;> by_cases h2 : R ω <;> simp [h1, h2]
  simp_rw [hpt]
  rw [factor I x t H G (fun ω d => by simp only [G, hR])]
  rfl

lemma prob_ball {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (Q : BallDraw ι → Prop) [DecidablePred Q] :
    (algMeasure I x).real {ω | Q (ω t)} =
      ∑ d, ballWeight I x t d * (if Q d then 1 else 0) := by
  haveI := isProb hx htight
  have := prob_split hx htight t Q (fun _ => True) (fun _ _ => Iff.rfl)
  simp only [and_true, Set.ofPred_true, probReal_univ, mul_one] at this
  exact this

lemma sum_pick_ne (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) (i : ι) :
    ∑ o, pickWeight I x t o * (if o = some i then 0 else 1) = 1 - x i t / I.p t := by
  have h1 := sum_pickWeight I x t
  have h2 := sum_pick_some I x t i
  have : ∀ o, pickWeight I x t o * (if o = some i then 0 else 1) =
      pickWeight I x t o - pickWeight I x t o * (if o = some i then 1 else 0) := by
    intro o; split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, h1, h2]

lemma ballsum_arr {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (t : Fin n) :
    ∑ d, ballWeight I x t d * (if d.arrives = true then 1 else 0) = I.p t := by
  have hs := sumBall I x t (fun b => if b then 1 else 0) (fun _ => 1) (fun _ => 1) (fun _ => 1)
  have e : ∀ d : BallDraw ι, (if d.arrives = true then (1 : ℝ) else 0) =
      (if d.1 = true then 1 else 0) * 1 * 1 * 1 := by
    intro d; rcases d with ⟨a, f1, cn, f2⟩; cases a <;> simp [BallDraw.arrives]
  simp_rw [e]
  rw [hs, sum_arr_true, sum_pick_one, sum_coin_one]
  ring

lemma ballsum_arr_ne {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (t : Fin n) (i : ι) :
    ∑ d, ballWeight I x t d * (if d.arrives = true ∧ d.firstPick ≠ some i then 1 else 0) =
      I.p t * (1 - x i t / I.p t) := by
  have hs := sumBall I x t (fun b => if b then 1 else 0) (fun o => if o = some i then 0 else 1)
    (fun _ => 1) (fun _ => 1)
  have e : ∀ d : BallDraw ι, (if d.arrives = true ∧ d.firstPick ≠ some i then (1 : ℝ) else 0) =
      (if d.1 = true then 1 else 0) * (if d.2.1 = some i then 0 else 1) * 1 * 1 := by
    intro d
    rcases d with ⟨a, f1, cn, f2⟩
    by_cases h2 : f1 = some i <;> cases a <;> simp [BallDraw.arrives, BallDraw.firstPick, h2]
  simp_rw [e]
  rw [hs, sum_arr_true, sum_pick_ne, sum_coin_one, sum_pick_one]
  ring

lemma ballsum_arr_eq {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (j : ι) :
    ∑ d, ballWeight I x t d * (if d.arrives = true ∧ d.firstPick = some j then 1 else 0) =
      x j t := by
  have hs := sumBall I x t (fun b => if b then 1 else 0) (fun o => if o = some j then 1 else 0)
    (fun _ => 1) (fun _ => 1)
  have e : ∀ d : BallDraw ι, (if d.arrives = true ∧ d.firstPick = some j then (1 : ℝ) else 0) =
      (if d.1 = true then 1 else 0) * (if d.2.1 = some j then 1 else 0) * 1 * 1 := by
    intro d
    rcases d with ⟨a, f1, cn, f2⟩
    by_cases h2 : f1 = some j <;> cases a <;> simp [BallDraw.arrives, BallDraw.firstPick, h2]
  simp_rw [e]
  rw [hs, sum_arr_true, sum_pick_some, sum_coin_one, sum_pick_one, mul_one, mul_one,
    x_eq I x hx htight]

lemma ballsum_arr_eq_coin {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (j : ι) :
    ∑ d, ballWeight I x t d *
      (if d.arrives = true ∧ d.firstPick = some j ∧ d.coin j = true then 1 else 0) =
      x j t * acceptProb x j t := by
  have hs := sumBall I x t (fun b => if b then 1 else 0) (fun o => if o = some j then 1 else 0)
    (fun f => if f j then 1 else 0) (fun _ => 1)
  have e : ∀ d : BallDraw ι,
      (if d.arrives = true ∧ d.firstPick = some j ∧ d.coin j = true then (1 : ℝ) else 0) =
      (if d.1 = true then 1 else 0) * (if d.2.1 = some j then 1 else 0) *
        (if d.2.2.1 j = true then 1 else 0) * 1 := by
    intro d
    rcases d with ⟨a, f1, cn, f2⟩
    by_cases h2 : f1 = some j <;> cases a <;> cases h3 : cn j <;>
      simp [BallDraw.arrives, BallDraw.firstPick, BallDraw.coin, h2, h3]
  simp_rw [e]
  rw [hs, sum_arr_true, sum_pick_some, sum_coin_i, sum_pick_one, mul_one,
    x_eq I x hx htight]

lemma prob_arr {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) :
    (algMeasure I x).real (arrivalSet t) = I.p t := by
  have := prob_ball hx htight t (fun d => d.arrives = true)
  rw [ballsum_arr] at this
  exact this

theorem lemma47 {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (i : ι) (t : Fin n) (hlate : IsLate x i t)
    (hp : 0 < I.p t) :
    1 - 4 * c ≤ (algMeasure I x)[|arrivalSet t].real ((firstPickSet t i)ᶜ) := by
  haveI := isProb hx htight
  rw [cond_real _ _ _ (MeasurableSpace.measurableSet_top), prob_arr hx htight]
  have hinter : arrivalSet t ∩ (firstPickSet t i)ᶜ =
      {ω : Outcome ι n | (ω t).arrives = true ∧ (ω t).firstPick ≠ some i} := by
    ext ω; simp [arrivalSet, firstPickSet]
  rw [hinter, prob_ball hx htight t (fun d => d.arrives = true ∧ d.firstPick ≠ some i),
    ballsum_arr_ne]
  rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  -- `x_{i,t}/p_t ≤ 1 - X_t < 1 - θ ≤ 4c`
  have h11 := hx.online i t
  have hl := hlate
  unfold IsLate at hl
  rw [thr_val] at hl
  have hle : x i t / I.p t ≤ 1 - cumX x i t := by
    rw [div_le_iff₀ hp]; linarith
  rw [c_val]
  linarith

theorem eq20 {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (j : ι) (t : Fin n) (hpos : 0 < x j t) :
    1 / 2 - c ≤ (algMeasure I x)[|arrivalSet t ∩ firstPickSet t j].real
      (unmatchedAfterFirstSet x t) := by
  haveI := isProb hx htight
  rw [cond_real _ _ _ (MeasurableSpace.measurableSet_top)]
  have hA : arrivalSet t ∩ firstPickSet t j =
      {ω : Outcome ι n | (ω t).arrives = true ∧ (ω t).firstPick = some j} := by
    ext ω; simp [arrivalSet, firstPickSet]
  have hA' : (algMeasure I x).real (arrivalSet t ∩ firstPickSet t j) = x j t := by
    rw [hA, prob_ball hx htight t (fun d => d.arrives = true ∧ d.firstPick = some j),
      ballsum_arr_eq hx htight]
  -- the joint event
  have hB : (algMeasure I x).real (arrivalSet t ∩ firstPickSet t j ∩ unmatchedAfterFirstSet x t)
      = x j t - x j t * acceptProb x j t * (algMeasure I x).real (vacantSet x j t) := by
    rw [prob_eq hx htight]
    have hpt : ∀ ω : Outcome ι n,
        (if ω ∈ arrivalSet t ∩ firstPickSet t j ∩ unmatchedAfterFirstSet x t then (1 : ℝ) else 0)
        = (if (ω t).arrives = true ∧ (ω t).firstPick = some j then 1 else 0) * 1 -
          (if (ω t).arrives = true ∧ (ω t).firstPick = some j ∧ (ω t).coin j = true then 1 else 0)
            * (if IsVacantIn (stateAfter x ω t.val) j then 1 else 0) := by
      intro ω
      simp only [arrivalSet, firstPickSet, unmatchedAfterFirstSet, Set.mem_inter_iff,
        Set.mem_ofPred_eq, mem_M1_iff]
      by_cases h1 : (ω t).arrives = true <;> by_cases h2 : (ω t).firstPick = some j <;>
        by_cases h3 : (ω t).coin j = true <;>
        by_cases h4 : IsVacantIn (stateAfter x ω t.val) j <;> simp [h1, h2, h3, h4]
    simp_rw [hpt, mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [factor I x t (fun d => if d.arrives = true ∧ d.firstPick = some j then 1 else 0)
      (fun _ => 1) (fun _ _ => rfl)]
    rw [factor I x t
      (fun d => if d.arrives = true ∧ d.firstPick = some j ∧ d.coin j = true then 1 else 0)
      (fun ω => if IsVacantIn (stateAfter x ω t.val) j then 1 else 0)
      (fun ω d => by simp only [stateAfter_update])]
    rw [ballsum_arr_eq hx htight, ballsum_arr_eq_coin hx htight, prob_eq hx htight]
    simp only [mul_one, sum_outcomeWeight]
    congr 1
  rw [hA', hB]
  -- `q_{j,t} · Pr[V_{j,t}] ≤ 1/2 + c`
  have hqv : acceptProb x j t * (algMeasure I x).real (vacantSet x j t) ≤ 1 / 2 + c := by
    have hm := main hx htight j t
    by_cases hE : IsEarly x j t
    · rw [acceptProb_early hx j t hE, hm.2.2.2.2.2 hE]
      have hE' := hE
      unfold IsEarly at hE'
      rw [thr_val] at hE'
      have h0 := cumX_nonneg hx j t
      have hpos' : 0 < 1 - cumX x j t * (1 / 2 + c) := by rw [c_val]; nlinarith
      rw [div_mul_cancel₀ _ hpos'.ne']
    · have hL : IsLate x j t := lt_of_not_ge hE
      rw [acceptProb_late hx j t hL, one_mul]
      exact hm.2.2.2.2.1 hL
  rw [show x j t - x j t * acceptProb x j t * (algMeasure I x).real (vacantSet x j t) =
    x j t * (1 - acceptProb x j t * (algMeasure I x).real (vacantSet x j t)) by ring]
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [c_val] at hqv ⊢
  linarith

end LPM47


open MeasureTheory ProbabilityTheory

namespace LPM49
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct LPMAlg LPM44 LPM47
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- NA is preserved by injective reindexing (a special case of Proposition 2.7.2) -/
lemma NA_reindex {Ω κ κ' : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : κ → Ω → ℝ)
    (hX : NegativelyAssociated X μ) (e : κ' → κ) (he : Function.Injective e) :
    NegativelyAssociated (fun k ω => X (e k) ω) μ := by
  have := OnlineMaxWeightMatch.Approx.proposition_2_7_2 μ X hX (fun k => {e k})
    (fun j k hjk => by
      simp only [Finset.disjoint_singleton]
      exact fun h => hjk (he h))
    (fun k z => z ⟨e k, Finset.mem_singleton_self _⟩)
    (fun k z z' h => h _) (fun k => measurable_pi_apply _)
  exact this

/-- NA of an empty family -/
lemma NA_empty {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [IsEmpty κ] (X : κ → Ω → ℝ) : NegativelyAssociated X μ := by
  intro A B _ f g _ _ _ _ _ _
  have hA : ∀ ω, (fun a : A => X a ω) = fun a => isEmptyElim (a.1) := by
    intro ω; funext a; exact isEmptyElim a.1
  have hB : ∀ ω, (fun b : B => X b ω) = fun b => isEmptyElim (b.1) := by
    intro ω; funext b; exact isEmptyElim b.1
  simp only [hA, hB, integral_const, probReal_univ, one_smul]
  exact le_rfl

/-- the first-pick acceptance indicators `W_{j,s} = X_{j,s} ∧ Y_{j,s}` -/
noncomputable def W (k : ι × Fin n) (ω : Outcome ι n) : ℝ :=
  if (ω k.2).arrives = true ∧ (ω k.2).firstPick = some k.1 ∧ (ω k.2).coin k.1 = true
  then 1 else 0

lemma W_upd (k : ι × Fin n) (ω : Outcome ι n) (s : Fin n) (d : BallDraw ι) (h : k.2 ≠ s) :
    W k (upd ω s d) = W k ω := by
  simp only [W, upd_ne ω s d k.2 h]

/-- independence of a function of the draw of ball `s` from a function of the other draws -/
lemma indep_ball {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (s : Fin n) {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] (Fb : BallDraw ι → β) (G : Outcome ι n → γ)
    (hG : ∀ ω d, G (upd ω s d) = G ω) :
    IndepFun (fun ω : Outcome ι n => Fb (ω s)) G (algMeasure I x) := by
  haveI := isProb hx htight
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B _ _
  have h1 : (algMeasure I x).real ((fun ω : Outcome ι n => Fb (ω s)) ⁻¹' A ∩ G ⁻¹' B) =
      (algMeasure I x).real ((fun ω : Outcome ι n => Fb (ω s)) ⁻¹' A) *
        (algMeasure I x).real (G ⁻¹' B) := by
    have e1 : (fun ω : Outcome ι n => Fb (ω s)) ⁻¹' A ∩ G ⁻¹' B =
      {ω | Fb (ω s) ∈ A ∧ G ω ∈ B} := rfl
    have e2 : (fun ω : Outcome ι n => Fb (ω s)) ⁻¹' A = {ω | Fb (ω s) ∈ A} := rfl
    have e3 : G ⁻¹' B = {ω | G ω ∈ B} := rfl
    rw [e1, e2, e3, prob_split hx htight s (fun d => Fb d ∈ A) (fun ω => G ω ∈ B)
      (fun ω d => by simp only [hG]), prob_ball hx htight s (fun d => Fb d ∈ A)]
  rw [← ofReal_measureReal, ← ofReal_measureReal, ← ofReal_measureReal, h1,
    ENNReal.ofReal_mul measureReal_nonneg]

/-- the family `{W_{j,s}}_j` of one ball is NA (0-1 principle) -/
lemma NA_ball {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (s : Fin n) :
    NegativelyAssociated (fun j ω => W ((j, s) : ι × Fin n) ω) (algMeasure I x) := by
  haveI := isProb hx htight
  apply OnlineMaxWeightMatch.Approx.proposition_2_6
  · intro j; exact Measurable.of_discrete
  · intro j ω; simp only [W]; split_ifs <;> simp
  · intro ω
    rcases hf : (ω s).firstPick with _ | j0
    · rw [Finset.sum_eq_zero]
      · norm_num
      · intro j _; simp [W, hf]
    · rw [Finset.sum_eq_single j0]
      · simp only [W]; split_ifs <;> norm_num
      · intro j _ hj
        have : ¬ (some j0 = some j) := by simp [Ne.symm hj]
        simp [W, hf, this]
      · simp

/-- the whole family `{W_{j,s}}_{j, s ∈ T}` is NA, by induction on `T` -/
lemma NA_set {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (T : Finset (Fin n)) :
    NegativelyAssociated (fun (k : ι × {r // r ∈ T}) ω => W ((k.1, k.2.1) : ι × Fin n) ω)
      (algMeasure I x) := by
  haveI := isProb hx htight
  induction T using Finset.induction_on with
  | empty =>
    haveI : IsEmpty (ι × {r // r ∈ (∅ : Finset (Fin n))}) := by
      constructor; rintro ⟨_, r, hr⟩; simp at hr
    exact NA_empty _ _
  | insert s T hs ih =>
    -- `X`: the variables of ball `s`; `Y`: those of the balls in `T`
    let X : ι → Outcome ι n → ℝ := fun j ω => W ((j, s) : ι × Fin n) ω
    let Y : ι × {r // r ∈ T} → Outcome ι n → ℝ := fun k ω => W ((k.1, k.2.1) : ι × Fin n) ω
    have hind : IndepFun (fun ω j => X j ω) (fun ω k => Y k ω) (algMeasure I x) := by
      have := indep_ball hx htight s (fun d => fun j : ι =>
          if d.arrives = true ∧ d.firstPick = some j ∧ d.coin j = true then (1 : ℝ) else 0)
        (fun ω k => Y k ω) (by
          intro ω d
          funext k
          apply W_upd
          intro h
          apply hs
          rw [← h]; exact k.2.2)
      exact this
    have hU := OnlineMaxWeightMatch.Approx.proposition_2_7_1 (algMeasure I x) X Y
      (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete) hind
      (NA_ball hx htight s) ih
    -- reindex `ι × (insert s T)` into `ι ⊕ (ι × T)`
    let e : ι × {r // r ∈ insert s T} → ι ⊕ (ι × {r // r ∈ T}) := fun k =>
      if h : k.2.1 = s then Sum.inl k.1 else
        Sum.inr (k.1, ⟨k.2.1, by
          have := k.2.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left h⟩)
    have he : Function.Injective e := by
      rintro ⟨j, r, hr⟩ ⟨j', r', hr'⟩ h
      simp only [e] at h
      by_cases h1 : r = s <;> by_cases h2 : r' = s
      · subst h1; subst h2
        simp at h
        subst h; rfl
      · simp [h1, h2] at h
      · simp [h1, h2] at h
      · simp [h1, h2] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    have hR := NA_reindex (algMeasure I x) (Sum.elim X Y) hU e he
    convert hR using 1
    funext k ω
    rcases k with ⟨j, r, hr⟩
    simp only [e]
    by_cases h1 : r = s
    · subst h1; simp [X]
    · simp [h1, Y]

end LPM49


open MeasureTheory ProbabilityTheory

namespace LPM49
open OnlineMaxWeightMatch.Approx LPMCommon LPMStruct LPMAlg LPM44 LPM47
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- `O^E_{i,t} = ⋁_{s < t early} (X_{i,s} ∧ Y_{i,s})` -/
lemma occEarly_iff {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) (ω : Outcome ι n) :
    ω ∈ occupiedEarlySet x i t ↔ ∃ s, s < t ∧ IsEarly x i s ∧
      ((ω s).arrives = true ∧ (ω s).firstPick = some i ∧ (ω s).coin i = true) := by
  constructor
  · rintro ⟨s, hE, hmem⟩
    have hlt : s < t := by
      rcases hmem with h | h
      · exact (stateAfter_lt x ω t.val (i, s)).1 h
      · exact (stateAfter_lt x ω t.val (i, s)).2 h
    have hf := stateAfter_frozen x ω t.val (i, s) hlt n t.isLt.le
    rcases hmem with h | h
    · have hM1 : (i, s) ∈ M1 x ω := by rw [M1, hf.1]; exact h
      obtain ⟨h1, h2, _, h4⟩ := (mem_M1_iff x ω i s).mp hM1
      exact ⟨s, hlt, hE, h1, h2, h4⟩
    · have hM2 : (i, s) ∈ M2 x ω := by rw [M2, hf.2]; exact h
      have := ((mem_M2_iff x ω i s).mp hM2).2.2.2.2
      exact absurd hE (not_le.mpr this)
  · rintro ⟨s, hs, hE, hc⟩
    let S := (Finset.univ : Finset (Fin n)).filter (fun r => r < t ∧ IsEarly x i r ∧
      ((ω r).arrives = true ∧ (ω r).firstPick = some i ∧ (ω r).coin i = true))
    have hne : S.Nonempty := ⟨s, by simp [S, hs, hE, hc]⟩
    let s0 := S.min' hne
    have hs0 : s0 ∈ S := Finset.min'_mem S hne
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs0
    have hvac : IsVacantIn (stateAfter x ω s0.val) i := by
      rw [vacant_iff]
      intro r hr
      have hrE : IsEarly x i r := le_trans (cumX_mono hx i hr.le) hs0.2.1
      constructor
      · intro hm
        obtain ⟨h1, h2, _, h4⟩ := (mem_M1_iff x ω i r).mp hm
        have : s0 ≤ r := Finset.min'_le S r (by
          simp [S, lt_trans hr hs0.1, hrE, h1, h2, h4])
        exact absurd hr (not_lt.mpr this)
      · intro hm
        have := ((mem_M2_iff x ω i r).mp hm).2.2.2.2
        exact absurd hrE (not_le.mpr this)
    have hM1 : (i, s0) ∈ M1 x ω :=
      (mem_M1_iff x ω i s0).mpr ⟨hs0.2.2.1, hs0.2.2.2.1, hvac, hs0.2.2.2.2⟩
    have hf := stateAfter_frozen x ω t.val (i, s0) hs0.1 n t.isLt.le
    refine ⟨s0, hs0.2.1, Or.inl ?_⟩
    rw [← hf.1]; exact hM1

theorem lemma49 {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) :
    NegativelyAssociated (fun i => occupancyEarly x i t) (algMeasure I x) := by
  haveI := isProb hx htight
  -- the full family `{W_{j,s}}_{j,s}` is NA
  have hZ : NegativelyAssociated (fun (k : ι × Fin n) ω => W k ω) (algMeasure I x) := by
    have := NA_reindex (algMeasure I x) _ (NA_set hx htight Finset.univ)
      (fun k : ι × Fin n => (k.1, (⟨k.2, Finset.mem_univ _⟩ : {r // r ∈ Finset.univ})))
      (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; rfl)
    exact this
  -- monotone composition
  let S : ι → Finset (ι × Fin n) := fun i =>
    ((Finset.univ : Finset (Fin n)).filter (fun s => s < t ∧ IsEarly x i s)).image
      (fun s => (i, s))
  have hS : Pairwise fun j k => Disjoint (S j) (S k) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [S, Finset.mem_image] at ha hb
    obtain ⟨s, _, rfl⟩ := ha
    obtain ⟨s', _, h⟩ := hb
    exact hjk (congrArg Prod.fst h).symm
  let f : (i : ι) → (S i → ℝ) → ℝ := fun i z => if ∃ a, 1 ≤ z a then 1 else 0
  have hmono : ∀ i, Monotone (f i) := by
    intro i z z' h
    simp only [f]
    by_cases hz : ∃ a, 1 ≤ z a
    · obtain ⟨a, ha⟩ := hz
      rw [if_pos ⟨a, ha⟩, if_pos ⟨a, le_trans ha (h a)⟩]
    · rw [if_neg hz]; split_ifs <;> norm_num
  have hmeas : ∀ i, Measurable (f i) := by
    intro i
    apply Measurable.ite
    · have : {z : S i → ℝ | ∃ a, 1 ≤ z a} = ⋃ a, {z | 1 ≤ z a} := by ext z; simp
      rw [this]
      exact MeasurableSet.iUnion (fun a => measurableSet_le measurable_const
        (measurable_pi_apply a))
    · exact measurable_const
    · exact measurable_const
  have hC := OnlineMaxWeightMatch.Approx.proposition_2_7_2 (algMeasure I x)
    (fun k ω => W k ω) hZ S hS f hmono hmeas
  convert hC using 1
  funext i ω
  simp only [occupancyEarly, f]
  rw [show (occupiedEarlySet x i t).indicator (1 : Outcome ι n → ℝ) ω =
    if ω ∈ occupiedEarlySet x i t then 1 else 0 by
      by_cases h : ω ∈ occupiedEarlySet x i t <;> simp [Set.indicator, h]]
  congr 1
  apply propext
  rw [occEarly_iff hx i t ω]
  constructor
  · rintro ⟨s, hs, hE, hc⟩
    refine ⟨⟨(i, s), ?_⟩, ?_⟩
    · simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨s, ⟨hs, hE⟩, rfl⟩
    · simp [W, hc]
  · rintro ⟨⟨a, ha⟩, h1⟩
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨s, ⟨hs, hE⟩, rfl⟩ := ha
    refine ⟨s, hs, hE, ?_⟩
    simp only [W] at h1
    by_contra hc
    rw [if_neg hc] at h1
    norm_num at h1

end LPM49


open MeasureTheory ProbabilityTheory

open OnlineMaxWeightMatch.Approx in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (t : Fin n) :
    NegativelyAssociated (fun i => occupancyEarly x i t) (algMeasure I x) :=
  LPM49.lemma49 hx htight t
