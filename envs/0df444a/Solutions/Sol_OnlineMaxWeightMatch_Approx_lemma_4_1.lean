-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:25:36.425484+00:00
-- url     : https://prove2.me/submissions/d99a66c9-e318-4ce8-be1f-26493b439ca9

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_LPMatch

open MeasureTheory ProbabilityTheory

namespace LPM41
open OnlineMaxWeightMatch.Approx

variable {ι : Type*} {n : ℕ}

lemma mUT_succ (π : OnlinePolicy ι n) (a : Fin n → Bool) (k : ℕ) (e : ι × Fin n) :
    e ∈ π.matchingUpTo a (k + 1) ↔ e ∈ π.matchingUpTo a k ∨
      (∃ h : k < n, ∃ i, π ⟨k, h⟩ (fun s => a s.1) = some i ∧ a ⟨k, h⟩ = true ∧
        (∀ s, (i, s) ∉ π.matchingUpTo a k) ∧ e = (i, ⟨k, h⟩)) := by
  classical
  simp only [OnlinePolicy.matchingUpTo]
  split_ifs with h
  · rcases hπ : π ⟨k, h⟩ (fun s => a s.1) with _ | i
    · simp only
      constructor
      · intro he; exact Or.inl he
      · rintro (he | ⟨h', j, hj, _, _, _⟩)
        · exact he
        · have := hπ.symm.trans hj; cases this
    · simp only
      split_ifs with hc
      · rw [Finset.mem_insert]
        constructor
        · rintro (he | he)
          · exact Or.inr ⟨h, i, hπ, hc.1, hc.2, he⟩
          · exact Or.inl he
        · rintro (he | ⟨h', j, hj, ha, hf, he⟩)
          · exact Or.inr he
          · have := hπ.symm.trans hj; cases this; exact Or.inl he
      · constructor
        · intro he; exact Or.inl he
        · rintro (he | ⟨h', j, hj, ha, hf, he⟩)
          · exact he
          · have := hπ.symm.trans hj; cases this; exact absurd ⟨ha, hf⟩ hc
  · simp [h]

lemma mUT_lt (π : OnlinePolicy ι n) (a : Fin n → Bool) (k : ℕ) (e : ι × Fin n)
    (he : e ∈ π.matchingUpTo a k) : e.2.val < k := by
  induction k with
  | zero => simp [OnlinePolicy.matchingUpTo] at he
  | succ k ih =>
    rcases (mUT_succ π a k e).mp he with h | ⟨h, i, _, _, _, rfl⟩
    · exact Nat.lt_succ_of_lt (ih h)
    · exact Nat.lt_succ_self k

lemma mUT_frozen (π : OnlinePolicy ι n) (a : Fin n → Bool) (k : ℕ) (e : ι × Fin n)
    (hk : e.2.val < k) : ∀ m, k ≤ m →
    (e ∈ π.matchingUpTo a m ↔ e ∈ π.matchingUpTo a k) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact Iff.rfl
  | succ m hkm ih =>
    rw [mUT_succ, ih]
    constructor
    · rintro (h | ⟨h, i, _, _, _, rfl⟩)
      · exact h
      · exfalso; simp at hk; omega
    · intro h; exact Or.inl h

lemma mUT_congr (π : OnlinePolicy ι n) (a a' : Fin n → Bool) (k : ℕ)
    (haa : ∀ s : Fin n, s.val < k → a s = a' s) :
    π.matchingUpTo a k = π.matchingUpTo a' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (fun s hs => haa s (Nat.lt_succ_of_lt hs))
    simp only [OnlinePolicy.matchingUpTo]
    split_ifs with h
    · have e1 : (fun s : {s : Fin n // s ≤ ⟨k, h⟩} => a s.1) = (fun s => a' s.1) := by
        funext s
        apply haa
        have : s.1 ≤ ⟨k, h⟩ := s.2
        rw [Fin.le_def] at this
        simp at this
        omega
      have e2 : a ⟨k, h⟩ = a' ⟨k, h⟩ := haa _ (by simp)
      rw [e1, e2, ih']
    · exact ih'

/-- the matching of `π` -/
lemma mem_matching_iff (π : OnlinePolicy ι n) (a : Fin n → Bool) (i : ι) (t : Fin n) :
    (i, t) ∈ π.matching a ↔ π t (fun s => a s.1) = some i ∧ a t = true ∧
      (∀ s, (i, s) ∉ π.matchingUpTo a t.val) := by
  have h := mUT_frozen π a (t.val + 1) (i, t) (Nat.lt_succ_self _) n t.isLt
  rw [OnlinePolicy.matching, h, mUT_succ]
  constructor
  · rintro (h1 | ⟨h, j, hj, ha, hf, he⟩)
    · have := mUT_lt π a _ _ h1; simp at this
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact ⟨hj, ha, hf⟩
  · rintro ⟨hj, ha, hf⟩
    exact Or.inr ⟨t.isLt, i, hj, ha, hf, rfl⟩

lemma matching_bin_unique (π : OnlinePolicy ι n) (a : Fin n → Bool) (i : ι) (s s' : Fin n)
    (hs : (i, s) ∈ π.matching a) (hs' : (i, s') ∈ π.matching a) : s = s' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := ((mem_matching_iff π a i s').mp hs').2.2 s
    apply h1
    rw [← mUT_frozen π a s'.val (i, s) h n s'.isLt.le]
    exact hs
  · have h1 := ((mem_matching_iff π a i s).mp hs).2.2 s'
    apply h1
    rw [← mUT_frozen π a s.val (i, s') h n s.isLt.le]
    exact hs'

lemma matching_ball_unique (π : OnlinePolicy ι n) (a : Fin n → Bool) (i i' : ι) (t : Fin n)
    (h : (i, t) ∈ π.matching a) (h' : (i', t) ∈ π.matching a) : i = i' := by
  have h1 := ((mem_matching_iff π a i t).mp h).1
  have h2 := ((mem_matching_iff π a i' t).mp h').1
  rw [h1] at h2
  exact Option.some.inj h2

variable [Fintype ι]

lemma arrivalProb_nonneg (I : RideHailInstance ι n) (a : Fin n → Bool) :
    0 ≤ arrivalProb I a := by
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact I.p_nonneg t
  · linarith [I.p_le_one t]

lemma sum_arrivalProb (I : RideHailInstance ι n) : ∑ a, arrivalProb I a = 1 := by
  unfold arrivalProb
  have h := Fintype.prod_sum (fun (t : Fin n) (b : Bool) => if b then I.p t else 1 - I.p t)
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_sub_cancel,
    Finset.prod_const_one] at h
  exact h.symm

lemma split_eq (t : Fin n) (b : Bool) (r : {j // j ≠ t} → Bool) :
    (Equiv.funSplitAt t Bool).symm (b, r) =
      Function.update ((Equiv.funSplitAt t Bool).symm (true, r)) t b := by
  funext j
  by_cases h : j = t
  · subst h; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma arrivalProb_update (I : RideHailInstance ι n) (a : Fin n → Bool) (t : Fin n) (b : Bool) :
    arrivalProb I (Function.update a t b) =
      (if b then I.p t else 1 - I.p t) *
        ∏ s ∈ Finset.univ \ {t}, (if a s then I.p s else 1 - I.p s) := by
  unfold arrivalProb
  have : ∀ s, (if Function.update a t b s then I.p s else 1 - I.p s) =
      Function.update (fun s => if a s then I.p s else 1 - I.p s) t
        (if b then I.p t else 1 - I.p t) s := by
    intro s
    by_cases h : s = t
    · subst h; simp
    · simp [Function.update_of_ne h]
  simp_rw [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ t)]

/-- independence of the arrival of ball `t` from anything not depending on it -/
lemma indep (I : RideHailInstance ι n) (t : Fin n) (G : (Fin n → Bool) → ℝ)
    (hG : ∀ a b, G (Function.update a t b) = G a) :
    ∑ a, arrivalProb I a * (if a t then G a else 0) = I.p t * ∑ a, arrivalProb I a * G a := by
  rw [← (Equiv.funSplitAt t Bool).symm.sum_comp, ← (Equiv.funSplitAt t Bool).symm.sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Bool)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.sum_bool, Fintype.sum_bool]
  rw [split_eq t true r, split_eq t false r]
  set a0 := (Equiv.funSplitAt t Bool).symm (true, r)
  simp only [arrivalProb_update, hG, Function.update_self]
  simp
  ring

end LPM41


open MeasureTheory ProbabilityTheory

namespace LPM41
open OnlineMaxWeightMatch.Approx
open Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- the matching probabilities of a policy -/
noncomputable def xPol (I : RideHailInstance ι n) (π : OnlinePolicy ι n) (i : ι) (t : Fin n) : ℝ :=
  ∑ a, arrivalProb I a * (if (i, t) ∈ π.matching a then 1 else 0)

lemma xPol_nonneg (I : RideHailInstance ι n) (π : OnlinePolicy ι n) (i : ι) (t : Fin n) :
    0 ≤ xPol I π i t :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (arrivalProb_nonneg I a) (by split_ifs <;> norm_num))

/-- weighted sums of pointwise bounds -/
lemma wsum_le (I : RideHailInstance ι n) (f g : (Fin n → Bool) → ℝ) (h : ∀ a, f a ≤ g a) :
    ∑ a, arrivalProb I a * f a ≤ ∑ a, arrivalProb I a * g a :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (arrivalProb_nonneg I a))

lemma bin_count (π : OnlinePolicy ι n) (a : Fin n → Bool) (i : ι) (S : Finset (Fin n)) :
    ∑ s ∈ S, (if (i, s) ∈ π.matching a then (1 : ℝ) else 0) ≤ 1 := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (S.filter (fun s => (i, s) ∈ π.matching a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro s hs s' hs'
    simp only [Finset.mem_filter] at hs hs'
    exact matching_bin_unique π a i s s' hs.2 hs'.2
  exact_mod_cast this

lemma ball_count (π : OnlinePolicy ι n) (a : Fin n → Bool) (t : Fin n) :
    ∑ i, (if (i, t) ∈ π.matching a then (1 : ℝ) else 0) ≤ if a t then 1 else 0 := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases h : ∃ i, (i, t) ∈ π.matching a
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ((mem_matching_iff π a i t).mp hi).2.1]
    have : (Finset.univ.filter (fun i => (i, t) ∈ π.matching a)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro j hj j' hj'
      simp only [Finset.mem_filter] at hj hj'
      exact matching_ball_unique π a j j' t hj.2 hj'.2
    exact_mod_cast this
  · push Not at h
    have : Finset.univ.filter (fun i => (i, t) ∈ π.matching a) = ∅ := by
      ext i; simp [h i]
    rw [this]
    split_ifs <;> simp

lemma feasible (I : RideHailInstance ι n) (π : OnlinePolicy ι n) :
    LPFeasible I (xPol I π) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    unfold xPol
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc ∑ a, arrivalProb I a * ∑ t, (if (i, t) ∈ π.matching a then (1 : ℝ) else 0)
        ≤ ∑ a, arrivalProb I a * 1 := wsum_le I _ _ (fun a => bin_count π a i _)
      _ = 1 := by simp [sum_arrivalProb]
  · intro t
    unfold xPol
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc ∑ a, arrivalProb I a * ∑ i, (if (i, t) ∈ π.matching a then (1 : ℝ) else 0)
        ≤ ∑ a, arrivalProb I a * (if a t then 1 else 0) :=
          wsum_le I _ _ (fun a => ball_count π a t)
      _ = I.p t := by
          rw [indep I t (fun _ => 1) (fun _ _ => rfl)]
          simp [sum_arrivalProb]
  · intro i t
    -- `F a`: bin `i` is free before `t`
    let F : (Fin n → Bool) → ℝ := fun a =>
      if ∀ s ∈ Finset.Iio t, (i, s) ∉ π.matching a then 1 else 0
    have hF : ∀ a b, F (Function.update a t b) = F a := by
      intro a b
      have hcong := mUT_congr π (Function.update a t b) a t.val (by
        intro s hs
        have : s ≠ t := by intro h; rw [h] at hs; exact lt_irrefl _ hs
        simp [Function.update_of_ne this])
      have key : ∀ a' : Fin n → Bool, (∀ s ∈ Finset.Iio t, (i, s) ∉ π.matching a') ↔
          (∀ s ∈ Finset.Iio t, (i, s) ∉ π.matchingUpTo a' t.val) := by
        intro a'
        apply forall_congr'; intro s; apply imp_congr_right; intro hs
        rw [Finset.mem_Iio] at hs
        rw [OnlinePolicy.matching, mUT_frozen π a' t.val (i, s) hs n t.isLt.le]
      simp only [F, key, hcong]
    have h1 : xPol I π i t ≤ ∑ a, arrivalProb I a * (if a t then F a else 0) := by
      apply wsum_le
      intro a
      by_cases hm : (i, t) ∈ π.matching a
      · have hat := ((mem_matching_iff π a i t).mp hm).2.1
        have hfree : ∀ s ∈ Finset.Iio t, (i, s) ∉ π.matching a := by
          intro s hs hs'
          have := matching_bin_unique π a i s t hs' hm
          rw [this, Finset.mem_Iio] at hs
          exact lt_irrefl _ hs
        have hF1 : F a = 1 := if_pos hfree
        simp [hm, hat, hF1]
      · simp only [hm, if_false]
        split_ifs <;> simp [F] <;> split_ifs <;> norm_num
    have h2 : ∑ a, arrivalProb I a * F a ≤ 1 - cumX (xPol I π) i t := by
      have : 1 - cumX (xPol I π) i t = ∑ a, arrivalProb I a *
          (1 - ∑ s ∈ Finset.Iio t, (if (i, s) ∈ π.matching a then (1 : ℝ) else 0)) := by
        simp only [mul_sub, Finset.sum_sub_distrib, mul_one, sum_arrivalProb, cumX, xPol]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      rw [this]
      apply wsum_le
      intro a
      simp only [F]
      split_ifs with hf
      · rw [Finset.sum_eq_zero (fun s hs => by simp [hf s hs])]
        simp
      · linarith [bin_count π a i (Finset.Iio t)]
    calc xPol I π i t ≤ ∑ a, arrivalProb I a * (if a t then F a else 0) := h1
      _ = I.p t * ∑ a, arrivalProb I a * F a := indep I t F hF
      _ ≤ I.p t * (1 - cumX (xPol I π) i t) := mul_le_mul_of_nonneg_left h2 (I.p_nonneg t)
  · exact xPol_nonneg I π

lemma objective (I : RideHailInstance ι n) (π : OnlinePolicy ι n) :
    lpObjective I (xPol I π) = policyValue I π := by
  classical
  unfold lpObjective xPol policyValue
  calc ∑ i, ∑ t, I.w i t * ∑ a, arrivalProb I a * (if (i, t) ∈ π.matching a then (1 : ℝ) else 0)
      = ∑ i, ∑ t, ∑ a, arrivalProb I a * (if (i, t) ∈ π.matching a then I.w i t else 0) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        split_ifs <;> ring
    _ = ∑ a, ∑ i, ∑ t, arrivalProb I a * (if (i, t) ∈ π.matching a then I.w i t else 0) := by
        calc _ = ∑ i, ∑ a, ∑ t, arrivalProb I a *
              (if (i, t) ∈ π.matching a then I.w i t else 0) :=
              Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
          _ = _ := Finset.sum_comm
    _ = ∑ a, arrivalProb I a * ∑ e ∈ π.matching a, I.w e.1 e.2 := by
        apply Finset.sum_congr rfl; intro a _
        conv_rhs => rw [← Finset.univ_inter (π.matching a), ← Finset.sum_ite_mem,
          Finset.mul_sum, Fintype.sum_prod_type]

lemma bdd (I : RideHailInstance ι n) : BddAbove (lpObjective I '' {x | LPFeasible I x}) := by
  refine ⟨∑ i, ∑ t, I.w i t, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  unfold lpObjective
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro t _
  have hle : y i t ≤ 1 := by
    calc y i t ≤ ∑ j, y j t :=
          Finset.single_le_sum (fun j _ => hy.nonneg j t) (Finset.mem_univ i)
      _ ≤ I.p t := hy.ball_le_p t
      _ ≤ 1 := I.p_le_one t
  calc I.w i t * y i t ≤ I.w i t * 1 := mul_le_mul_of_nonneg_left hle (I.w_nonneg i t)
    _ = I.w i t := mul_one _

end LPM41

open OnlineMaxWeightMatch.Approx in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n) :
    optOn I ≤ lpValue I := by
  have : Nonempty (OnlinePolicy ι n) := ⟨fun _ _ => none⟩
  apply ciSup_le
  intro π
  rw [← LPM41.objective I π]
  exact le_csSup (LPM41.bdd I) ⟨_, LPM41.feasible I π, rfl⟩
