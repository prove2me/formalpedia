-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:19:01.173672+00:00
-- url     : https://prove2.me/submissions/c83d9d26-07b9-4663-bab0-d6d18eb34f70

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis
import Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_4
import Theorems.Thm_OnlineMaxWeightMatch_Approx_theorem_4_6

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

open OnlineMaxWeightMatch.Approx in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (i : ι) (t : Fin n) :
    x i t * (1 / 2 + c) ≤ (algMeasure I x).real {ω | (i, t) ∈ algMatching x ω} := by
  haveI := LPMCommon.isProb hx htight
  obtain ⟨hearly, hall⟩ := OnlineMaxWeightMatch.Approx.lemma_4_4 I x hx htight
  have hunion : {ω | (i, t) ∈ algMatching x ω} =
      {ω | (i, t) ∈ M1 x ω} ∪ {ω | (i, t) ∈ M2 x ω} := by
    ext ω; simp [algMatching]
  have hsub : {ω | (i, t) ∈ M1 x ω} ⊆ {ω | (i, t) ∈ algMatching x ω} := by
    rw [hunion]; exact Set.subset_union_left
  by_cases hlate : IsLate x i t
  · have h2 := OnlineMaxWeightMatch.Approx.theorem_4_6 I x hx htight i t hlate
    have h1 := (hall i t).1
    have hdisj : Disjoint {ω | (i, t) ∈ M1 x ω} {ω | (i, t) ∈ M2 x ω} := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      exact LPMStruct.not_mem_M1_and_M2 x ω i t ⟨h1, h2⟩
    rw [hunion, measureReal_union hdisj (MeasurableSpace.measurableSet_top)]
    have : x i t * (1 / 2 + c) = x i t * (1 / 2 - 3 * c) + x i t * (4 * c) := by ring
    rw [this]
    exact add_le_add h1 h2
  · have hE : IsEarly x i t := le_of_not_gt hlate
    rw [← hearly i t hE]
    exact measureReal_mono hsub
