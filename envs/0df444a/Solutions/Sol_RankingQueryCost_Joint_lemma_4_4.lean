-- Prove2me | solution 1 for RankingQueryCost.Joint.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:16:16.857574+00:00
-- url     : https://prove2.me/submissions/fbd4b950-a5d9-4fed-b641-07a9682d29c9

import Definitions.Def_RankingQueryCost_Joint_Reference

set_option autoImplicit false
set_option maxHeartbeats 400000


noncomputable section

namespace RQCRef
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def pairOf (x y : Fin n) (h : x ≠ y) : Pair n :=
  if hxy : x < y then ⟨(x, y), hxy⟩ else ⟨(y, x), lt_of_le_of_ne (not_lt.1 hxy) h.symm⟩

theorem pairOf_mem (x y : Fin n) (h : x ≠ y) :
    ((pairOf x y h).1.1 = x ∧ (pairOf x y h).1.2 = y) ∨ ((pairOf x y h).1.1 = y ∧ (pairOf x y h).1.2 = x) := by
  unfold pairOf; split_ifs <;> simp

theorem recordedForward_iff (T : Transcript n) (x y : Fin n) (hxy : x < y) :
    (RecordedForward T x y ↔ T ⟨(x, y), hxy⟩ = some true) ∧
      (RecordedForward T y x ↔ T ⟨(x, y), hxy⟩ = some false) := by
  constructor
  · constructor
    · rintro ⟨e, (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)⟩
      · have : e = ⟨(x, y), hxy⟩ := Subtype.ext (Prod.ext h1 h2)
        rw [← this]; exact h3
      · have he := e.2; rw [h1, h2] at he; exact absurd (lt_trans he hxy) (lt_irrefl _)
    · intro h; exact ⟨⟨(x, y), hxy⟩, Or.inl ⟨rfl, rfl, h⟩⟩
  · constructor
    · rintro ⟨e, (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)⟩
      · have he := e.2; rw [h1, h2] at he; exact absurd (lt_trans he hxy) (lt_irrefl _)
      · have : e = ⟨(x, y), hxy⟩ := Subtype.ext (Prod.ext h1 h2)
        rw [← this]; exact h3
    · intro h; exact ⟨⟨(x, y), hxy⟩, Or.inr ⟨rfl, rfl, h⟩⟩

theorem not_recordedForward_self (T : Transcript n) (x : Fin n) : ¬ RecordedForward T x x := by
  rintro ⟨e, (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)⟩ <;>
    (have he := e.2; rw [h1, h2] at he; exact lt_irrefl _ he)

/-- If the pair is answered truthfully for `r`, the recorded relation is the true one. -/
theorem recorded_truthful (T : Transcript n) (r : Rank n) (x y : Fin n) (hxy : x ≠ y)
    (hT : T (pairOf x y hxy) = some (truthful r (pairOf x y hxy))) :
    (RecordedForward T x y ↔ r x < r y) := by
  unfold pairOf at hT
  split_ifs at hT with hlt
  · rw [(recordedForward_iff T x y hlt).1, hT]; simp [truthful]
  · have hlt' : y < x := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hxy)
    rw [(recordedForward_iff T y x hlt').2, hT]
    simp only [truthful, Option.some.injEq, decide_eq_false_iff_not, not_lt]
    have hne : r x ≠ r y := fun h' => hxy (r.injective h')
    constructor
    · intro h; exact lt_of_le_of_ne h hne
    · intro h; exact h.le

/-- The disagreeing acquired pairs. -/
def disSet (T : Transcript n) (r : Rank n) : Finset (Pair n) :=
  (acquired T).filter fun e => T e ≠ some (truthful r e)

theorem disSet_card (T : Transcript n) (r : Rank n) : (disSet T r).card = disagreements T r := rfl

/-- A recorded relation differs from `r` only on a disagreeing pair (when the pair is acquired). -/
theorem rec_ne_imp_dis (T : Transcript n) (r : Rank n) (x y : Fin n) (hxy : x ≠ y)
    (hacq : (T (pairOf x y hxy)).isSome = true) (hne : ¬ (RecordedForward T x y ↔ r x < r y)) :
    pairOf x y hxy ∈ disSet T r := by
  rw [disSet, Finset.mem_filter]
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hacq⟩, fun h => hne (recorded_truthful T r x y hxy h)⟩

/-- Number of pairs of a set containing a given label. -/
theorem sum_incident_le (D : Finset (Pair n)) :
    ∑ x : Fin n, (D.filter fun e => e.1.1 = x ∨ e.1.2 = x).card ≤ 2 * D.card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ e : Pair n, (∑ x : Fin n, if e.1.1 = x ∨ e.1.2 = x then 1 else 0) = 2 := by
    intro e
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun x => e.1.1 = x ∨ e.1.2 = x) = {e.1.1, e.1.2} := by
      ext x; simp [eq_comm]
    rw [this, Finset.card_pair e.2.ne]
  rw [Finset.sum_congr rfl (fun e _ => this e)]
  simp; ring_nf; rfl

/-- `|{a ∈ A : P a} | - |{a ∈ A : Q a}| ≤ |{a ∈ A : P a ≠ Q a}|` in absolute value. -/
theorem card_filter_sub_le {α : Type} (A : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    |((A.filter P).card : ℝ) - (A.filter Q).card| ≤ (A.filter fun a => ¬ (P a ↔ Q a)).card := by
  have h1 : A.filter P ⊆ (A.filter Q) ∪ (A.filter fun a => ¬ (P a ↔ Q a)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    by_cases hq : Q a
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha.1, hq⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha.1, fun h => hq (h.1 ha.2)⟩)
  have h2 : A.filter Q ⊆ (A.filter P) ∪ (A.filter fun a => ¬ (P a ↔ Q a)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    by_cases hp : P a
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha.1, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha.1, fun h => hp (h.2 ha.2)⟩)
  have c1 := le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _)
  have c2 := le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)
  rw [abs_le]; constructor
  · have : ((A.filter Q).card : ℝ) ≤ (A.filter P).card + (A.filter fun a => ¬ (P a ↔ Q a)).card := by
      exact_mod_cast c2
    linarith
  · have : ((A.filter P).card : ℝ) ≤ (A.filter Q).card + (A.filter fun a => ¬ (P a ↔ Q a)).card := by
      exact_mod_cast c1
    linarith

/-- Mismatched partners of `i` inject into disagreeing pairs at `i`. -/
theorem mismatch_le (T : Transcript n) (r : Rank n) (A : Finset (Fin n)) (i : Fin n)
    (hacq : ∀ a ∈ A, ∀ hai : a ≠ i, (T (pairOf a i hai)).isSome = true) :
    (A.filter fun a => ¬ (RecordedForward T a i ↔ r a < r i)).card ≤
      ((disSet T r).filter fun e => e.1.1 = i ∨ e.1.2 = i).card := by
  classical
  set M := A.filter fun a => ¬ (RecordedForward T a i ↔ r a < r i)
  have hne : ∀ a ∈ M, a ≠ i := by
    intro a ha h; subst h
    apply (Finset.mem_filter.1 ha).2
    exact ⟨fun h => absurd h (not_recordedForward_self T a), fun h => absurd h (lt_irrefl _)⟩
  rcases M.eq_empty_or_nonempty with he | ⟨a0, ha0⟩
  · rw [he]; simp
  let e0 := pairOf a0 i (hne a0 ha0)
  apply Finset.card_le_card_of_injOn (fun a => if h : a ≠ i then pairOf a i h else e0)
  · intro a ha
    have hai := hne a ha
    simp only [dif_pos hai]
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨rec_ne_imp_dis T r a i hai (hacq a (Finset.mem_filter.1 ha).1 hai) (Finset.mem_filter.1 ha).2, ?_⟩
    rcases pairOf_mem a i hai with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Or.inr h2
    · exact Or.inl h1
  · intro a ha a' ha' h
    have hai := hne a ha
    have hai' := hne a' ha'
    simp only [dif_pos hai, dif_pos hai'] at h
    rcases pairOf_mem a i hai with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases pairOf_mem a' i hai' with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · rw [← a1, ← b1, h]
    · rw [h] at a1; exact absurd (a1.symm.trans b1) hai
    · rw [h] at a1; exact absurd (b1.symm.trans a1) hai'
    · rw [← a2, ← b2, h]

/-- Rank identity: the number of labels below `i` in `r` is `r i`. -/
theorem rank_count (r : Rank n) (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter fun j => r j < r i).card = (r i : ℕ) := by
  have h2 : ((Finset.univ : Finset (Fin n)).filter fun j => r j < r i).card =
      ((Finset.univ : Finset (Fin n)).filter fun k => k < r i).card := by
    refine Finset.card_bij (fun j _ => r j) ?_ ?_ ?_
    · intro j hj; simpa using hj
    · intro j _ j' _ h; exact r.injective h
    · intro k hk; exact ⟨r.symm k, by simpa using hk, by simp⟩
  rw [h2]
  have : ((Finset.univ : Finset (Fin n)).filter fun k => k < r i) = Finset.Iio (r i) := by
    ext k; simp
  rw [this, Fin.card_Iio]

theorem cnt_l1 (T : Transcript n) (S : Finset (Fin n)) (r : Rank n) (hst : StarsPresent T S) :
    ∑ i, |((referenceCount T S i : ℕ) : ℝ) - ((S.filter fun a => r a < r i).card : ℝ)| ≤
      2 * (disagreements T r : ℝ) := by
  have h1 : ∀ i, |((referenceCount T S i : ℕ) : ℝ) - ((S.filter fun a => r a < r i).card : ℝ)| ≤
      (((disSet T r).filter fun e => e.1.1 = i ∨ e.1.2 = i).card : ℝ) := by
    intro i
    have hrc : referenceCount T S i = (S.filter fun a => RecordedForward T a i).card := rfl
    rw [hrc]
    refine le_trans (card_filter_sub_le S (fun a => RecordedForward T a i) (fun a => r a < r i)) ?_
    have hacq : ∀ a ∈ S, ∀ hai : a ≠ i, (T (pairOf a i hai)).isSome = true := by
      intro a ha hai
      apply hst
      rcases pairOf_mem a i hai with ⟨h1, _⟩ | ⟨_, h2⟩
      · left; rw [h1]; exact ha
      · right; rw [h2]; exact ha
    have := mismatch_le T r S i hacq
    have h' : (((S.filter fun a => ¬ (RecordedForward T a i ↔ r a < r i)).card : ℕ) : ℝ) ≤
      (((disSet T r).filter fun e => e.1.1 = i ∨ e.1.2 = i).card : ℝ) := Nat.cast_le.2 this
    exact h'
  refine le_trans (Finset.sum_le_sum fun i _ => h1 i) ?_
  have := sum_incident_le (disSet T r)
  rw [← disSet_card]
  exact_mod_cast this

theorem score_l1 (T : Transcript n) (S : Finset (Fin n)) (r : Rank n) (hst : StarsPresent T S) :
    ∑ a ∈ S, |((observedScore T a : ℕ) : ℝ) - ((r a : ℕ) : ℝ)| ≤ 2 * (disagreements T r : ℝ) := by
  have h1 : ∀ a ∈ S, |((observedScore T a : ℕ) : ℝ) - ((r a : ℕ) : ℝ)| ≤
      (((disSet T r).filter fun e => e.1.1 = a ∨ e.1.2 = a).card : ℝ) := by
    intro a ha
    rw [← rank_count r a]
    have hos : observedScore T a = (Finset.univ.filter fun b => RecordedForward T b a).card := rfl
    rw [hos]
    refine le_trans (card_filter_sub_le Finset.univ (fun b => RecordedForward T b a) (fun b => r b < r a)) ?_
    have hacq : ∀ b ∈ (Finset.univ : Finset (Fin n)), ∀ hba : b ≠ a, (T (pairOf b a hba)).isSome = true := by
      intro b _ hba
      apply hst
      rcases pairOf_mem b a hba with ⟨_, h2⟩ | ⟨h1, _⟩
      · right; rw [h2]; exact ha
      · left; rw [h1]; exact ha
    have := mismatch_le T r Finset.univ a hacq
    exact Nat.cast_le.2 this
  refine le_trans (Finset.sum_le_sum h1) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => by positivity)) ?_
  have := sum_incident_le (disSet T r)
  rw [← disSet_card]
  exact_mod_cast this

end RQCRef



noncomputable section

namespace RQCRef
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The sorted list behind `referenceOrder` with the identity prior. -/
def refList (T : Transcript n) (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).mergeSort fun i j =>
    decide (referenceCount T S i < referenceCount T S j ∨
      (referenceCount T S i = referenceCount T S j ∧ (List.finRange n).idxOf i ≤ (List.finRange n).idxOf j))

theorem referenceOrder_eq (T : Transcript n) (S : Finset (Fin n)) (i : Fin n) :
    referenceOrder T S (List.finRange n) i = ((refList T S).idxOf i : ℝ) := rfl

theorem refList_perm (T : Transcript n) (S : Finset (Fin n)) : (refList T S).Perm (List.finRange n) :=
  List.mergeSort_perm _ _

theorem refList_mem (T : Transcript n) (S : Finset (Fin n)) (i : Fin n) : i ∈ refList T S :=
  (refList_perm T S).mem_iff.2 (List.mem_finRange i)

theorem refList_nodup (T : Transcript n) (S : Finset (Fin n)) : (refList T S).Nodup :=
  (refList_perm T S).nodup_iff.2 (List.nodup_finRange n)

theorem refList_length (T : Transcript n) (S : Finset (Fin n)) : (refList T S).length = n := by
  rw [(refList_perm T S).length_eq, List.length_finRange]

theorem refList_sorted (T : Transcript n) (S : Finset (Fin n)) :
    (refList T S).Pairwise fun i j => referenceCount T S i ≤ referenceCount T S j := by
  have h := List.pairwise_mergeSort (l := List.finRange n) (le := fun i j =>
    decide (referenceCount T S i < referenceCount T S j ∨
      (referenceCount T S i = referenceCount T S j ∧ (List.finRange n).idxOf i ≤ (List.finRange n).idxOf j)))
    (by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hbc with h3 | ⟨h3, h4⟩
      · exact Or.inl (lt_trans h1 h3)
      · exact Or.inl (h3 ▸ h1)
      · exact Or.inl (h1 ▸ h3)
      · exact Or.inr ⟨h1.trans h3, le_trans h2 h4⟩)
    (by
      intro a b
      rcases lt_trichotomy (referenceCount T S a) (referenceCount T S b) with h | h | h
      · simp [h]
      · simp only [h, lt_irrefl, false_or, true_and, Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _
      · simp [h])
  apply List.Pairwise.imp _ h
  intro a b hab
  simp only [decide_eq_true_eq] at hab
  rcases hab with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- The permutation of positions. -/
def refPos (T : Transcript n) (S : Finset (Fin n)) (i : Fin n) : Fin n :=
  ⟨(refList T S).idxOf i, by
    have := List.idxOf_lt_length_iff.2 (refList_mem T S i)
    rwa [refList_length] at this⟩

theorem refPos_injective (T : Transcript n) (S : Finset (Fin n)) : Function.Injective (refPos T S) := by
  intro i j h
  have h' : (refList T S).idxOf i = (refList T S).idxOf j := congrArg Fin.val h
  have := congrArg (fun t => (refList T S)[t]?) h'
  rwa [List.getElem?_idxOf (refList_mem T S i), List.getElem?_idxOf (refList_mem T S j),
    Option.some.injEq] at this

def refPerm (T : Transcript n) (S : Finset (Fin n)) : Rank n :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (refPos_injective T S))

theorem refPerm_apply (T : Transcript n) (S : Finset (Fin n)) (i : Fin n) :
    ((refPerm T S i : Fin n) : ℕ) = (refList T S).idxOf i := rfl

/-- Positions are monotone in the observed counts. -/
theorem refPos_mono (T : Transcript n) (S : Finset (Fin n)) (i j : Fin n)
    (h : (refList T S).idxOf i < (refList T S).idxOf j) : referenceCount T S i ≤ referenceCount T S j := by
  have hs := refList_sorted T S
  rw [List.pairwise_iff_getElem] at hs
  have hi := List.idxOf_lt_length_iff.2 (refList_mem T S i)
  have hj := List.idxOf_lt_length_iff.2 (refList_mem T S j)
  have := hs _ _ hi hj h
  rwa [List.getElem_idxOf, List.getElem_idxOf] at this

theorem sum_perm_sq (σ : Rank n) : ∑ i, ((σ i : ℕ) : ℝ) ^ 2 = ∑ i : Fin n, ((i : ℕ) : ℝ) ^ 2 :=
  Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- Rearrangement: sorting by the observed counts gives the nearest permutation vector. -/
theorem ref_nearest (T : Transcript n) (S : Finset (Fin n)) (c : ℝ) (hc : 0 ≤ c) (r : Rank n) :
    ∑ i, (referenceOrder T S (List.finRange n) i - c * referenceCount T S i) ^ 2 ≤
      ∑ i, (rankVector r i - c * referenceCount T S i) ^ 2 := by
  set x : Fin n → ℝ := fun i => c * referenceCount T S i
  set g : Fin n → ℝ := fun i => ((refPerm T S i : Fin n) : ℕ)
  have hg : ∀ i, referenceOrder T S (List.finRange n) i = g i := by
    intro i; rw [referenceOrder_eq]; simp [g, refPerm_apply]
  have hmono : Monovary x g := by
    intro i j hij
    simp only [g, refPerm_apply, Nat.cast_lt] at hij
    have := refPos_mono T S i j hij
    simp only [x]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) hc
  set τ : Equiv.Perm (Fin n) := r.trans (refPerm T S).symm
  have hτ : ∀ i, g (τ i) = rankVector r i := by
    intro i; simp [g, τ, rankVector]
  have hre := hmono.sum_mul_comp_perm_le_sum_mul (σ := τ)
  simp only [hτ] at hre
  have hsq1 : ∑ i, g i ^ 2 = ∑ i : Fin n, ((i : ℕ) : ℝ) ^ 2 := sum_perm_sq (refPerm T S)
  have hsq2 : ∑ i, rankVector r i ^ 2 = ∑ i : Fin n, ((i : ℕ) : ℝ) ^ 2 := sum_perm_sq r
  have e1 : ∑ i, (g i - x i) ^ 2 = ∑ i, g i ^ 2 - 2 * ∑ i, x i * g i + ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have e2 : ∑ i, (rankVector r i - x i) ^ 2 =
      ∑ i, rankVector r i ^ 2 - 2 * ∑ i, x i * rankVector r i + ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  simp only [hg]
  rw [e1, e2, hsq1, hsq2]
  linarith

end RQCRef



noncomputable section

namespace RQCRef
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem sq_add_weighted {ι : Type} [Fintype ι] (u v : ι → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∑ i, (u i + v i) ^ 2 ≤ (1 + ε) * ∑ i, u i ^ 2 + (1 + 1 / ε) * ∑ i, v i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h : 2 * u i * v i ≤ ε * u i ^ 2 + v i ^ 2 / ε := by
    have := sq_nonneg (ε * u i - v i)
    rw [div_eq_mul_inv]
    have hinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    nlinarith [inv_pos.2 hε]
  have : (1 + 1 / ε) * v i ^ 2 = v i ^ 2 + v i ^ 2 / ε := by ring
  nlinarith

/-- `∑ w² ≤ M ∑ |w|` when every `|w| ≤ M`. -/
theorem sum_sq_le {ι : Type} [Fintype ι] (w : ι → ℝ) (M : ℝ) (hw : ∀ i, |w i| ≤ M) :
    ∑ i, w i ^ 2 ≤ M * ∑ i, |w i| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← sq_abs]
  have := abs_nonneg (w i)
  nlinarith [hw i]

/-- Number of thresholds separating two naturals. -/
theorem threshold_count (u v : ℕ) :
    ((Finset.univ.filter fun l : Fin n => ¬ (u < l.val ↔ v < l.val)).card : ℝ) ≤ |(u : ℝ) - v| := by
  have h : (Finset.univ.filter fun l : Fin n => ¬ (u < l.val ↔ v < l.val)).card ≤
      (Finset.Ioc (min u v) (max u v)).card := by
    apply Finset.card_le_card_of_injOn (fun l => l.val)
    · intro l hl
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl
      simp only [Finset.coe_Ioc, Set.mem_Ioc]
      rcases le_total u v with h | h
      · rw [min_eq_left h, max_eq_right h]; constructor <;> by_contra hc <;> push Not at hc <;>
          (apply hl; constructor <;> intro _ <;> omega)
      · rw [min_eq_right h, max_eq_left h]; constructor <;> by_contra hc <;> push Not at hc <;>
          (apply hl; constructor <;> intro _ <;> omega)
    · intro l _ l' _ h; exact Fin.ext h
  rw [Nat.card_Ioc] at h
  have : ((max u v - min u v : ℕ) : ℝ) = |(u : ℝ) - v| := by
    rcases le_total u v with h' | h'
    · rw [max_eq_right h', min_eq_left h', Nat.cast_sub h', abs_sub_comm, abs_of_nonneg (by
        have : (u : ℝ) ≤ v := by exact_mod_cast h'
        linarith)]
    · rw [max_eq_left h', min_eq_right h', Nat.cast_sub h', abs_of_nonneg (by
        have : (v : ℝ) ≤ u := by exact_mod_cast h'
        linarith)]
  rw [← this]; exact_mod_cast h

theorem ref_sound (s k : ℕ) (hk : 1 ≤ k) (T : Transcript n) (S : Finset (Fin n)) (hS : S.card = k)
    (hst : StarsPresent T S) (r : Rank n) (hr : r ∈ compatible s T) :
    squaredError (referenceOrder T S (List.finRange n)) (rankVector r) ≤ denseCertificate s k T S := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := (n : ℝ) / k with hc
  have hc0 : 0 ≤ c := by positivity
  have hck : c * k = n := by rw [hc]; field_simp
  have hdis : (disagreements T r : ℝ) ≤ s := by exact_mod_cast hr
  set H : ℝ := 2 * (n : ℝ) ^ 2 * s / k
  have hH : (n : ℝ) * c * (2 * s) = H := by rw [hc]; simp only [H]; field_simp
  set x : Fin n → ℝ := fun i => c * referenceCount T S i
  set y : Fin n → ℝ := fun i => c * (S.filter fun a => r a < r i).card
  -- Step 1
  have step1 : ∑ i, (x i - y i) ^ 2 ≤ H := by
    have hw : ∀ i, |x i - y i| ≤ n := by
      intro i
      have h1 : (referenceCount T S i : ℝ) ≤ k := by
        rw [← hS]; exact_mod_cast Finset.card_filter_le _ _
      have h2 : ((S.filter fun a => r a < r i).card : ℝ) ≤ k := by
        rw [← hS]; exact_mod_cast Finset.card_filter_le _ _
      have : x i - y i = c * ((referenceCount T S i : ℝ) - (S.filter fun a => r a < r i).card) := by ring
      rw [this, abs_mul, abs_of_nonneg hc0, ← hck]
      apply mul_le_mul_of_nonneg_left _ hc0
      rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (referenceCount T S i),
        Nat.cast_nonneg (α := ℝ) (S.filter fun a => r a < r i).card]
    refine le_trans (sum_sq_le _ _ hw) ?_
    have hl1 := cnt_l1 T S r hst
    have : ∑ i, |x i - y i| = c * ∑ i, |((referenceCount T S i : ℕ) : ℝ) - ((S.filter fun a => r a < r i).card : ℝ)| := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      rw [show x i - y i = c * (((referenceCount T S i : ℕ) : ℝ) - ((S.filter fun a => r a < r i).card : ℝ)) by ring,
        abs_mul, abs_of_nonneg hc0]
    rw [this, ← hH]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have : c * ∑ i, |((referenceCount T S i : ℕ) : ℝ) - ((S.filter fun a => r a < r i).card : ℝ)| ≤ c * (2 * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    nlinarith
  -- Step 2
  set cv : Fin n → ℝ := fun l => c * (S.filter fun a => (r a : ℕ) < l.val).card
  set dv : Fin n → ℝ := fun l => c * (S.filter fun a => observedScore T a < l.val).card
  have step2 : ∑ l, (dv l - cv l) ^ 2 ≤ H := by
    have hmis : ∀ l : Fin n, |dv l - cv l| ≤ c * (S.filter fun a =>
        ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card := by
      intro l
      have : dv l - cv l = c * (((S.filter fun a => observedScore T a < l.val).card : ℝ) -
          (S.filter fun a => (r a : ℕ) < l.val).card) := by simp only [dv, cv]; ring
      rw [this, abs_mul, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left (card_filter_sub_le S _ _) hc0
    have hw : ∀ l, |dv l - cv l| ≤ n := by
      intro l
      refine le_trans (hmis l) ?_
      rw [← hck]
      apply mul_le_mul_of_nonneg_left _ hc0
      rw [← hS]; exact_mod_cast Finset.card_filter_le _ _
    refine le_trans (sum_sq_le _ _ hw) ?_
    have hsum : ∑ l : Fin n, ((S.filter fun a => ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card : ℝ) ≤
        2 * s := by
      have : ∑ l : Fin n, ((S.filter fun a => ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card : ℝ) =
          ∑ a ∈ S, ((Finset.univ.filter fun l : Fin n => ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card : ℝ) := by
        simp only [Finset.card_filter, Nat.cast_sum]
        rw [Finset.sum_comm]
      rw [this]
      refine le_trans (Finset.sum_le_sum fun a _ => threshold_count (n := n) (observedScore T a) (r a)) ?_
      have := score_l1 T S r hst
      linarith
    have : ∑ l, |dv l - cv l| ≤ c * (2 * s) := by
      refine le_trans (Finset.sum_le_sum fun l _ => hmis l) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum hc0
    rw [← hH]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  -- Step 3
  have step3 : ∑ i, (rankVector r i - y i) ^ 2 = ∑ l : Fin n, (((l : ℕ) : ℝ) - cv l) ^ 2 := by
    refine Fintype.sum_equiv r _ _ (fun i => ?_)
    simp only [rankVector, y, cv]
    congr 2
  -- Step 4
  set Q := quadraticStatistic k T S
  have hQ : Q = ∑ l : Fin n, (((l : ℕ) : ℝ) - dv l) ^ 2 := rfl
  have step4 : ∑ l : Fin n, (((l : ℕ) : ℝ) - cv l) ^ 2 ≤ 2 * Q + 2 * H := by
    have := sq_add_weighted (fun l : Fin n => ((l : ℕ) : ℝ) - dv l) (fun l => dv l - cv l) 1 one_pos
    simp only [sub_add_sub_cancel] at this
    rw [hQ]; norm_num at this; linarith
  -- Step 5
  have step5 : ∑ i, (x i - rankVector r i) ^ 2 ≤ 3 / 2 * (2 * Q + 2 * H) + 3 * H := by
    have := sq_add_weighted (fun i => y i - rankVector r i) (fun i => x i - y i) (1 / 2) (by norm_num)
    simp only [sub_add_sub_cancel'] at this
    have e : ∑ i, (y i - rankVector r i) ^ 2 = ∑ i, (rankVector r i - y i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i, (x i - rankVector r i) ^ 2 = ∑ i, ((y i - rankVector r i) + (x i - y i)) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e2]
    rw [e, step3] at this
    norm_num at this
    linarith
  -- Step 6
  have hnear := ref_nearest T S c hc0 r
  have step6 : squaredError (referenceOrder T S (List.finRange n)) (rankVector r) ≤
      4 * ∑ i, (x i - rankVector r i) ^ 2 := by
    unfold squaredError
    have := sq_add_weighted (fun i => referenceOrder T S (List.finRange n) i - x i)
      (fun i => x i - rankVector r i) 1 one_pos
    simp only [sub_add_sub_cancel] at this
    have e : ∑ i, (rankVector r i - c * referenceCount T S i) ^ 2 = ∑ i, (x i - rankVector r i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; simp only [x]; ring
    rw [e] at hnear
    norm_num at this
    linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
  unfold denseCertificate
  have : (24 : ℝ) * (2 * (n : ℝ) ^ 2 * s / k) = 24 * H := rfl
  rw [this]
  linarith

end RQCRef



noncomputable section

namespace RQCRef
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem card_subsets_mem (k : ℕ) (hk : 1 ≤ k) (a : Fin n) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => a ∈ S).card = (n - 1).choose (k - 1) := by
  have hc : (((Finset.univ : Finset (Fin n)).erase a).powersetCard (k - 1)).card = (n - 1).choose (k - 1) := by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  rw [← hc]
  apply Finset.card_bij (fun S _ => S.erase a)
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    rw [Finset.mem_powersetCard, Finset.card_erase_of_mem hS.2, hS.1.2]
    exact ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), rfl⟩
  · intro S hS S' hS' h
    rw [Finset.mem_filter] at hS hS'
    rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hS'.2, h]
  · intro R hR
    rw [Finset.mem_powersetCard] at hR
    have haR : a ∉ R := fun h => by have := hR.1 h; simp at this
    refine ⟨insert a R, ?_, by simp [haR]⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.card_insert_of_notMem haR, hR.2]
    exact ⟨⟨Finset.subset_univ _, by omega⟩, Finset.mem_insert_self _ _⟩

theorem card_subsets_mem2 (k : ℕ) (hk : 2 ≤ k) (a b : Fin n) (hab : a ≠ b) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => a ∈ S ∧ b ∈ S).card =
      (n - 2).choose (k - 2) := by
  have hb : b ∈ (Finset.univ : Finset (Fin n)).erase a := Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ _⟩
  have hc : ((((Finset.univ : Finset (Fin n)).erase a).erase b).powersetCard (k - 2)).card =
      (n - 2).choose (k - 2) := by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    congr 1
  rw [← hc]
  apply Finset.card_bij (fun S _ => (S.erase a).erase b)
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    have hbS : b ∈ S.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hS.2.2⟩
    rw [Finset.mem_powersetCard, Finset.card_erase_of_mem hbS, Finset.card_erase_of_mem hS.2.1, hS.1.2]
    refine ⟨Finset.erase_subset_erase _ (Finset.erase_subset_erase _ (Finset.subset_univ _)), by omega⟩
  · intro S hS S' hS' h
    rw [Finset.mem_filter] at hS hS'
    have hbS : b ∈ S.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hS.2.2⟩
    have hbS' : b ∈ S'.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hS'.2.2⟩
    rw [← Finset.insert_erase hS.2.1, ← Finset.insert_erase hS'.2.1, ← Finset.insert_erase hbS,
      ← Finset.insert_erase hbS', h]
  · intro R hR
    rw [Finset.mem_powersetCard] at hR
    have haR : a ∉ R := fun h => by have := hR.1 h; simp at this
    have hbR : b ∉ R := fun h => by have := hR.1 h; simp at this
    refine ⟨insert a (insert b R), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.card_insert_of_notMem (by
        simp [hab, haR]), Finset.card_insert_of_notMem hbR, hR.2]
      exact ⟨⟨Finset.subset_univ _, by omega⟩, Finset.mem_insert_self _ _,
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    · rw [Finset.erase_insert (by simp [hab, haR]), Finset.erase_insert hbR]

theorem card_subsets_mem2_lt (k : ℕ) (hk : k < 2) (a b : Fin n) (hab : a ≠ b) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => a ∈ S ∧ b ∈ S).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS hab'
  rw [Finset.mem_powersetCard] at hS
  have : 2 ≤ S.card := by
    rw [← Finset.card_pair hab]
    exact Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hab'.1, hab'.2])
  omega

end RQCRef



noncomputable section

namespace RQCRef
open RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem choose_id1 (n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((n - 1).choose (k - 1) : ℝ) * n = (n.choose k : ℝ) * k := by
  have := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hk] at this
  rw [mul_comm]; exact_mod_cast this

theorem choose_id2 (n k : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n) :
    ((n - 2).choose (k - 2) : ℝ) * (n * (n - 1)) = (n.choose k : ℝ) * (k * (k - 1)) := by
  have h1 := choose_id1 n k (by omega) (by omega)
  have h2 := choose_id1 (n - 1) (k - 1) (by omega) (by omega)
  rw [show n - 1 - 1 = n - 2 by omega, show k - 1 - 1 = k - 2 by omega] at h2
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ k)] at h2
  push_cast at h2 ⊢
  have : ((n - 2).choose (k - 2) : ℝ) * (n * (n - 1)) = (((n - 2).choose (k - 2) : ℝ) * ((n : ℝ) - 1)) * n := by ring
  rw [this, h2]
  have : ((n - 1).choose (k - 1) : ℝ) * ((k : ℝ) - 1) * n = (((n - 1).choose (k - 1) : ℝ) * n) * ((k : ℝ) - 1) := by ring
  rw [this, h1]; ring

theorem hyper_sum (k : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) (A : Finset (Fin n)) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ((A.card : ℝ) - ((n : ℝ) / k) * (S ∩ A).card) ^ 2 =
      (n.choose k : ℝ) * (A.card * ((n : ℝ) - A.card) * ((n : ℝ) - k) / (k * ((n : ℝ) - 1))) := by
  set 𝒮 := (Finset.univ : Finset (Fin n)).powersetCard k
  set m := A.card
  have hX : ∀ S, ((S ∩ A).card : ℝ) = ∑ a ∈ A, (if a ∈ S then 1 else 0) := by
    intro S
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]; push_cast; rfl
  have hP1 : ∀ a : Fin n, ∑ S ∈ 𝒮, (if a ∈ S then (1 : ℝ) else 0) = (n - 1).choose (k - 1) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_subsets_mem k hk a]
  set P2 : ℝ := if 2 ≤ k then ((n - 2).choose (k - 2) : ℝ) else 0
  have hP2 : ∀ a b : Fin n, a ≠ b → ∑ S ∈ 𝒮, (if a ∈ S then (1 : ℝ) else 0) * (if b ∈ S then 1 else 0) = P2 := by
    intro a b hab
    have : ∀ S : Finset (Fin n), (if a ∈ S then (1 : ℝ) else 0) * (if b ∈ S then 1 else 0) = if a ∈ S ∧ b ∈ S then 1 else 0 := by
      intro S; by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases hk2 : 2 ≤ k
    · simp only [P2, if_pos hk2]; rw [card_subsets_mem2 k hk2 a b hab]
    · simp only [P2, if_neg hk2]; rw [card_subsets_mem2_lt k (by omega) a b hab]; simp
  have hS1 : ∑ S ∈ 𝒮, ((S ∩ A).card : ℝ) = m * (n - 1).choose (k - 1) := by
    simp only [hX]; rw [Finset.sum_comm]; simp only [hP1]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hS2 : ∑ S ∈ 𝒮, ((S ∩ A).card : ℝ) ^ 2 = m * (n - 1).choose (k - 1) + (m * ((m : ℝ) - 1)) * P2 := by
    have : ∀ S, ((S ∩ A).card : ℝ) ^ 2 = ∑ a ∈ A, ∑ b ∈ A, (if a ∈ S then (1 : ℝ) else 0) * (if b ∈ S then 1 else 0) := by
      intro S; rw [hX, sq, Finset.sum_mul_sum]
    simp only [this]
    rw [Finset.sum_comm]
    have h2 : ∀ a ∈ A, ∑ S ∈ 𝒮, ∑ b ∈ A, (if a ∈ S then (1 : ℝ) else 0) * (if b ∈ S then 1 else 0) =
        (n - 1).choose (k - 1) + ((m : ℝ) - 1) * P2 := by
      intro a ha
      rw [Finset.sum_comm, ← Finset.add_sum_erase A _ ha]
      have e1 : ∑ S ∈ 𝒮, (if a ∈ S then (1 : ℝ) else 0) * (if a ∈ S then 1 else 0) = (n - 1).choose (k - 1) := by
        rw [← hP1 a]; apply Finset.sum_congr rfl; intro S _; split_ifs <;> simp
      rw [e1, Finset.sum_congr rfl (fun b hb => hP2 a b (Finset.ne_of_mem_erase hb).symm),
        Finset.sum_const, Finset.card_erase_of_mem ha, nsmul_eq_mul, Nat.cast_sub (Finset.card_pos.2 ⟨a, ha⟩)]
      push_cast; ring
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : (𝒮.card : ℝ) = n.choose k := by
    simp [𝒮, Finset.card_powersetCard]
  have hexp : ∑ S ∈ 𝒮, ((m : ℝ) - ((n : ℝ) / k) * (S ∩ A).card) ^ 2 =
      𝒮.card * (m : ℝ) ^ 2 - 2 * m * ((n : ℝ) / k) * ∑ S ∈ 𝒮, ((S ∩ A).card : ℝ) +
        ((n : ℝ) / k) ^ 2 * ∑ S ∈ 𝒮, ((S ∩ A).card : ℝ) ^ 2 := by
    have : ∀ S : Finset (Fin n), ((m : ℝ) - ((n : ℝ) / k) * (S ∩ A).card) ^ 2 =
        (m : ℝ) ^ 2 - 2 * m * ((n : ℝ) / k) * (S ∩ A).card + ((n : ℝ) / k) ^ 2 * ((S ∩ A).card : ℝ) ^ 2 := by
      intro S; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [hexp, hcard, hS1, hS2]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 := choose_id1 n k hk (by omega)
  by_cases hk2 : 2 ≤ k
  · have h2 := choose_id2 n k hk2 hn
    simp only [P2, if_pos hk2]
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have e1 : ((n - 1).choose (k - 1) : ℝ) = (n.choose k : ℝ) * k / n := by
      field_simp; linarith
    have e2 : ((n - 2).choose (k - 2) : ℝ) = (n.choose k : ℝ) * (k * (k - 1)) / (n * (n - 1)) := by
      field_simp; linarith
    rw [e1, e2]
    field_simp
    ring
  · have hk1 : k = 1 := by omega
    subst hk1
    simp only [P2, if_neg hk2]
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have e1 : ((n - 1).choose (1 - 1) : ℝ) = (n.choose 1 : ℝ) * 1 / n := by
      field_simp; push_cast at h1 ⊢; linarith
    rw [e1]
    field_simp
    ring

theorem sum_l_nl (n : ℕ) : ∑ l ∈ Finset.range n, (l : ℝ) * ((n : ℝ) - l) = ((n : ℝ) - 1) * n * (n + 1) / 6 := by
  have h1 : ∀ m : ℕ, 6 * ∑ l ∈ Finset.range m, (l : ℝ) * ((n : ℝ) - l) =
      3 * n * ((m : ℝ) - 1) * m - ((m : ℝ) - 1) * m * (2 * m - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring
  have := h1 n
  linarith

/-- The pathwise bound `T2 ≤ 2 T2_r + 2 H` for a compatible order `r`. -/
theorem qstat_le (s k : ℕ) (hk : 1 ≤ k) (T : Transcript n) (S : Finset (Fin n)) (hS : S.card = k)
    (hst : StarsPresent T S) (r : Rank n) (hr : r ∈ compatible s T) :
    quadraticStatistic k T S ≤ 2 * ∑ l : Fin n, (((l : ℕ) : ℝ) - ((n : ℝ) / k) *
      (S.filter fun a => (r a : ℕ) < l.val).card) ^ 2 + 2 * (2 * (n : ℝ) ^ 2 * s / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := (n : ℝ) / k with hc
  have hc0 : 0 ≤ c := by positivity
  have hck : c * k = n := by rw [hc]; field_simp
  have hdis : (disagreements T r : ℝ) ≤ s := by exact_mod_cast hr
  set H : ℝ := 2 * (n : ℝ) ^ 2 * s / k
  have hH : (n : ℝ) * c * (2 * s) = H := by rw [hc]; simp only [H]; field_simp
  set cv : Fin n → ℝ := fun l => c * (S.filter fun a => (r a : ℕ) < l.val).card
  set dv : Fin n → ℝ := fun l => c * (S.filter fun a => observedScore T a < l.val).card
  have step2 : ∑ l, (dv l - cv l) ^ 2 ≤ H := by
    have hmis : ∀ l : Fin n, |dv l - cv l| ≤ c * (S.filter fun a =>
        ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card := by
      intro l
      have : dv l - cv l = c * (((S.filter fun a => observedScore T a < l.val).card : ℝ) -
          (S.filter fun a => (r a : ℕ) < l.val).card) := by simp only [dv, cv]; ring
      rw [this, abs_mul, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left (card_filter_sub_le S _ _) hc0
    have hw : ∀ l, |dv l - cv l| ≤ n := by
      intro l
      refine le_trans (hmis l) ?_
      rw [← hck]
      apply mul_le_mul_of_nonneg_left _ hc0
      rw [← hS]; exact_mod_cast Finset.card_filter_le _ _
    refine le_trans (sum_sq_le _ _ hw) ?_
    have hsum : ∑ l : Fin n, ((S.filter fun a => ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card : ℝ) ≤
        2 * s := by
      have : ∑ l : Fin n, ((S.filter fun a => ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card : ℝ) =
          ∑ a ∈ S, ((Finset.univ.filter fun l : Fin n => ¬ (observedScore T a < l.val ↔ (r a : ℕ) < l.val)).card : ℝ) := by
        simp only [Finset.card_filter, Nat.cast_sum]
        rw [Finset.sum_comm]
      rw [this]
      refine le_trans (Finset.sum_le_sum fun a _ => threshold_count (n := n) (observedScore T a) (r a)) ?_
      have := score_l1 T S r hst
      linarith
    have : ∑ l, |dv l - cv l| ≤ c * (2 * s) := by
      refine le_trans (Finset.sum_le_sum fun l _ => hmis l) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum hc0
    rw [← hH]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hQ : quadraticStatistic k T S = ∑ l : Fin n, (((l : ℕ) : ℝ) - dv l) ^ 2 := rfl
  have := sq_add_weighted (fun l : Fin n => ((l : ℕ) : ℝ) - cv l) (fun l => cv l - dv l) 1 one_pos
  simp only [sub_add_sub_cancel] at this
  have e : ∑ l, (cv l - dv l) ^ 2 = ∑ l, (dv l - cv l) ^ 2 := by
    apply Finset.sum_congr rfl; intro l _; ring
  rw [e] at this
  rw [hQ]; norm_num at this
  linarith

end RQCRef



namespace RQCEnergy
open RankingQueryCost.Joint

variable {n : ℕ}

theorem card_pair (n : ℕ) : Fintype.card (Pair n) = n.choose 2 := by
  have : (Finset.univ : Finset (Pair n)).card =
      ((Finset.univ : Finset (Fin n)).powersetCard 2).card := by
    refine Finset.card_bij (fun e _ => {e.1.1, e.1.2}) ?_ ?_ ?_
    · intro e _
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair e.2.ne⟩
    · intro e _ f _ h
      have h1 : e.1.1 ∈ ({f.1.1, f.1.2} : Finset (Fin n)) := h ▸ (by simp)
      have h2 : e.1.2 ∈ ({f.1.1, f.1.2} : Finset (Fin n)) := h ▸ (by simp)
      have he : e.1.1.val < e.1.2.val := e.2
      have hf : f.1.1.val < f.1.2.val := f.2
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h1 h2
      apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> omega
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs.2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨⟨(a, b), h⟩, Finset.mem_univ _, rfl⟩
      · exact ⟨⟨(b, a), h⟩, Finset.mem_univ _, Finset.pair_comm _ _⟩
  rw [← Finset.card_univ, this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Incidence vector `e_{e.1} - e_{e.2}` (as in the Flow definitions). -/
def inc (e : Pair n) (i : Fin n) : ℝ := (if i = e.1.1 then 1 else 0) - (if i = e.1.2 then 1 else 0)

theorem abs_inc_le (e : Pair n) (i : Fin n) :
    |inc e i| ≤ if e.1.1 = i ∨ e.1.2 = i then 1 else 0 := by
  have hne : e.1.1 ≠ e.1.2 := e.2.ne
  unfold inc
  by_cases h1 : i = e.1.1 <;> by_cases h2 : i = e.1.2
  · exact absurd (h1.symm.trans h2) hne
  · simp [h1, h2, hne]
  · simp [h1, h2, hne.symm]
  · have : ¬ (e.1.1 = i ∨ e.1.2 = i) := by
      rintro (h | h)
      · exact h1 h.symm
      · exact h2 h.symm
    simp [h1, h2, this]

theorem inner_inc_self (e : Pair n) : ∑ i, inc e i * inc e i = 2 := by
  have hne : e.1.1 ≠ e.1.2 := e.2.ne
  unfold inc
  have : ∀ i : Fin n, ((if i = e.1.1 then (1 : ℝ) else 0) - (if i = e.1.2 then 1 else 0)) *
      ((if i = e.1.1 then 1 else 0) - (if i = e.1.2 then 1 else 0)) =
      (if i = e.1.1 then 1 else 0) + (if i = e.1.2 then 1 else 0) := by
    intro i
    by_cases h1 : i = e.1.1 <;> by_cases h2 : i = e.1.2
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp [h1, h2, hne, hne.symm]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

theorem inner_inc_ne (e f : Pair n) (hef : e ≠ f) : |∑ i, inc e i * inc f i| ≤ 1 := by
  have he : e.1.1.val < e.1.2.val := e.2
  have hf : f.1.1.val < f.1.2.val := f.2
  have key : ∀ a b : Fin n, ∑ i : Fin n, (if i = a then (1 : ℝ) else 0) * (if i = b then 1 else 0) =
      if a = b then 1 else 0 := by
    intro a b
    rw [Finset.sum_eq_single a]
    · by_cases hab : a = b <;> simp [hab]
    · intro i _ hia; simp [hia]
    · simp
  have hval : ∑ i, inc e i * inc f i =
      (if e.1.1 = f.1.1 then 1 else 0) - (if e.1.1 = f.1.2 then 1 else 0) -
        (if e.1.2 = f.1.1 then 1 else 0) + (if e.1.2 = f.1.2 then 1 else 0) := by
    unfold inc
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, key]
    ring
  rw [hval]
  have hne : ¬ (e.1.1 = f.1.1 ∧ e.1.2 = f.1.2) := by
    rintro ⟨h1, h2⟩; exact hef (Subtype.ext (Prod.ext h1 h2))
  simp only [Fin.ext_iff] at hne ⊢
  split_ifs <;> norm_num <;> omega

/-- The signed incidence flow with coefficients `c`. -/
def flowVec (D : Finset (Pair n)) (c : Pair n → ℝ) (i : Fin n) : ℝ := ∑ e ∈ D, c e * inc e i

theorem energy_le_degree (D : Finset (Pair n)) (c : Pair n → ℝ) (hc : ∀ e ∈ D, |c e| ≤ 1) :
    ∑ i, flowVec D c i ^ 2 ≤ (degreeSquareSum D : ℝ) := by
  unfold degreeSquareSum
  push_cast
  apply Finset.sum_le_sum
  intro i _
  have h : |flowVec D c i| ≤ (supportDegree D i : ℝ) := by
    unfold flowVec supportDegree
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [abs_mul]
    refine le_trans (mul_le_of_le_one_left (abs_nonneg _) (hc e he)) ?_
    refine le_trans (abs_inc_le e i) ?_
    split_ifs <;> simp
  have := sq_abs (flowVec D c i)
  nlinarith [abs_nonneg (flowVec D c i)]

theorem energy_le_quad (D : Finset (Pair n)) (c : Pair n → ℝ) (hc : ∀ e ∈ D, |c e| ≤ 1) :
    ∑ i, flowVec D c i ^ 2 ≤ (D.card : ℝ) * (D.card + 1) := by
  have hexp : ∑ i, flowVec D c i ^ 2 = ∑ e ∈ D, ∑ f ∈ D, c e * c f * ∑ i, inc e i * inc f i := by
    unfold flowVec
    calc ∑ i, (∑ e ∈ D, c e * inc e i) ^ 2
        = ∑ i, ∑ e ∈ D, ∑ f ∈ D, (c e * inc e i) * (c f * inc f i) := by
          apply Finset.sum_congr rfl; intro i _; rw [sq, Finset.sum_mul_sum]
      _ = ∑ e ∈ D, ∑ i, ∑ f ∈ D, (c e * inc e i) * (c f * inc f i) := Finset.sum_comm
      _ = ∑ e ∈ D, ∑ f ∈ D, ∑ i, (c e * inc e i) * (c f * inc f i) := by
          apply Finset.sum_congr rfl; intro e _; exact Finset.sum_comm
      _ = ∑ e ∈ D, ∑ f ∈ D, c e * c f * ∑ i, inc e i * inc f i := by
          apply Finset.sum_congr rfl; intro e _; apply Finset.sum_congr rfl; intro f _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hexp]
  have hb : ∀ e ∈ D, ∀ f ∈ D, c e * c f * ∑ i, inc e i * inc f i ≤ if e = f then 2 else 1 := by
    intro e he f hf
    have hce := hc e he; have hcf := hc f hf
    have hcc : |c e * c f| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg (c e), abs_nonneg (c f)]
    split_ifs with hef
    · subst hef
      rw [inner_inc_self]
      have : c e * c e ≤ 1 := by nlinarith [abs_nonneg (c e), sq_abs (c e)]
      linarith
    · have hi := inner_inc_ne e f hef
      have := abs_mul (c e * c f) (∑ i, inc e i * inc f i)
      have h2 : |c e * c f * ∑ i, inc e i * inc f i| ≤ 1 := by
        rw [this]; nlinarith [abs_nonneg (c e * c f), abs_nonneg (∑ i, inc e i * inc f i)]
      exact le_trans (le_abs_self _) h2
  calc ∑ e ∈ D, ∑ f ∈ D, c e * c f * ∑ i, inc e i * inc f i
      ≤ ∑ e ∈ D, ∑ f ∈ D, (if e = f then (2 : ℝ) else 1) :=
        Finset.sum_le_sum fun e he => Finset.sum_le_sum fun f hf => hb e he f hf
    _ = ∑ e ∈ D, ((D.card : ℝ) + 1) := by
        apply Finset.sum_congr rfl; intro e he
        have : ∑ f ∈ D, (if e = f then (2 : ℝ) else 1) = ∑ f ∈ D, (1 + if e = f then 1 else 0) := by
          apply Finset.sum_congr rfl; intro f _; split_ifs <;> norm_num
        rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos he]; simp
    _ = (D.card : ℝ) * (D.card + 1) := by simp; ring

theorem pair_sum_le (z : Fin n → ℝ) :
    ∑ e : Pair n, (z e.1.1 - z e.1.2) ^ 2 ≤ n * ∑ i, z i ^ 2 := by
  classical
  set h : Fin n × Fin n → ℝ := fun p => (z p.1 - z p.2) ^ 2
  have hsub : ∑ e : Pair n, (z e.1.1 - z e.1.2) ^ 2 =
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), h p := by
    rw [Finset.sum_subtype ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2))
      (p := fun p => p.1 < p.2) (by simp)]
  have hswap : ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), h p =
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), h p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p hp; simpa using hp
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp only [h, Prod.fst_swap, Prod.snd_swap]; ring
  have hdisj : Disjoint ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2))
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_filter]; intro p _ h1 h2; exact lt_asymm h1 h2
  have hle : ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), h p +
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), h p ≤
      ∑ p : Fin n × Fin n, h p := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => sq_nonneg _)
  have hall : ∑ p : Fin n × Fin n, h p = 2 * n * ∑ i, z i ^ 2 - 2 * (∑ i, z i) ^ 2 := by
    simp only [h, Fintype.sum_prod_type]
    have : ∀ i j : Fin n, (z i - z j) ^ 2 = z i ^ 2 - 2 * (z i * z j) + z j ^ 2 := fun i j => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, sq, Finset.sum_mul_sum]
    ring
  have hsq : 0 ≤ (∑ i, z i) ^ 2 := sq_nonneg _
  rw [hsub]
  linarith

theorem energy_le_nD (D : Finset (Pair n)) (c : Pair n → ℝ) (hc : ∀ e ∈ D, |c e| ≤ 1) :
    ∑ i, flowVec D c i ^ 2 ≤ (n : ℝ) * D.card := by
  set z := flowVec D c
  set S2 := ∑ i, z i ^ 2
  have h1 : S2 = ∑ e ∈ D, c e * (z e.1.1 - z e.1.2) := by
    calc S2 = ∑ i, z i * ∑ e ∈ D, c e * inc e i := by
          apply Finset.sum_congr rfl; intro i _; rw [sq]; rfl
      _ = ∑ e ∈ D, c e * ∑ i, z i * inc e i := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro e _; apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ e ∈ D, c e * (z e.1.1 - z e.1.2) := by
          apply Finset.sum_congr rfl; intro e _
          congr 1
          unfold inc
          simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
  have h2 : S2 ≤ ∑ e ∈ D, |z e.1.1 - z e.1.2| := by
    rw [h1]
    apply Finset.sum_le_sum
    intro e he
    calc c e * (z e.1.1 - z e.1.2) ≤ |c e * (z e.1.1 - z e.1.2)| := le_abs_self _
      _ = |c e| * |z e.1.1 - z e.1.2| := abs_mul _ _
      _ ≤ 1 * |z e.1.1 - z e.1.2| := mul_le_mul_of_nonneg_right (hc e he) (abs_nonneg _)
      _ = |z e.1.1 - z e.1.2| := one_mul _
  have h3 : (∑ e ∈ D, |z e.1.1 - z e.1.2|) ^ 2 ≤ D.card * ∑ e ∈ D, |z e.1.1 - z e.1.2| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h4 : ∑ e ∈ D, |z e.1.1 - z e.1.2| ^ 2 ≤ n * S2 := by
    simp only [sq_abs]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
      (fun _ _ _ => sq_nonneg _)) (pair_sum_le z)
  have hS0 : 0 ≤ S2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hT0 : 0 ≤ ∑ e ∈ D, |z e.1.1 - z e.1.2| := Finset.sum_nonneg fun e _ => abs_nonneg _
  have h5 : S2 ^ 2 ≤ D.card * (n * S2) := by
    have := pow_le_pow_left₀ hS0 h2 2
    have hD : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
    nlinarith
  rcases hS0.lt_or_eq with hpos | hzero
  · have : S2 * S2 ≤ (D.card * n) * S2 := by nlinarith
    have := le_of_mul_le_mul_right this hpos
    linarith
  · rw [← hzero]; positivity

def winner (t : Tournament n) (e : Pair n) : Fin n := if t e then e.1.2 else e.1.1

theorem score_eq (t : Tournament n) (i : Fin n) :
    score t i = (((Finset.univ : Finset (Pair n)).filter fun e => winner t e = i).card : ℝ) := by
  unfold score winner
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp

/-- The pair formed by two distinct labels. -/
def mkPair (i j : Fin n) (h : i ≠ j) : Pair n :=
  if hij : i < j then ⟨(i, j), hij⟩ else ⟨(j, i), lt_of_le_of_ne (not_lt.1 hij) h.symm⟩

theorem score_truthful (r : Rank n) : score (truthful r) = rankVector r := by
  classical
  funext i
  rw [score_eq]
  unfold rankVector
  have h1 : ((Finset.univ : Finset (Pair n)).filter fun e => winner (truthful r) e = i).card =
      ((Finset.univ : Finset (Fin n)).filter fun j => r j < r i).card := by
    symm
    refine Finset.card_bij (fun j hj => mkPair i j (by
        rintro rfl; exact lt_irrefl _ (Finset.mem_filter.1 hj).2)) ?_ ?_ ?_
    · intro j hj
      have hj' := (Finset.mem_filter.1 hj).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold mkPair winner truthful
      split_ifs with h1 h2 h2
      · exact absurd hj' (lt_asymm (by simpa using h2))
      · rfl
      · rfl
      · simp at h2; exact absurd hj' (not_lt.2 h2)
    · intro j hj j' hj' h
      unfold mkPair at h
      split_ifs at h with h1 h2 h2 <;> simp [Subtype.ext_iff, Prod.ext_iff] at h <;> omega
    · intro e he
      have he' := (Finset.mem_filter.1 he).2
      unfold winner truthful at he'
      split_ifs at he' with hw
      · refine ⟨e.1.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, by subst he'; simpa using hw⟩, ?_⟩
        unfold mkPair
        have : ¬ i < e.1.1 := by subst he'; exact not_lt.2 e.2.le
        rw [dif_neg this]; subst he'; rfl
      · refine ⟨e.1.2, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · subst he'
          have hne : r e.1.2 ≠ r e.1.1 := fun h => e.2.ne (r.injective h).symm
          simp at hw
          exact lt_of_le_of_ne hw hne
        · unfold mkPair; subst he'; rw [dif_pos e.2]
  rw [h1]
  have h2 : ((Finset.univ : Finset (Fin n)).filter fun j => r j < r i).card =
      ((Finset.univ : Finset (Fin n)).filter fun k => k < r i).card := by
    refine Finset.card_bij (fun j _ => r j) ?_ ?_ ?_
    · intro j hj; simpa using hj
    · intro j _ j' _ h; exact r.injective h
    · intro k hk; exact ⟨r.symm k, by simpa using hk, by simp⟩
  rw [h2]
  have : ((Finset.univ : Finset (Fin n)).filter fun k => k < r i) = Finset.Iio (r i) := by
    ext k; simp
  rw [this, Fin.card_Iio]

theorem score_aux (b b' : Bool) (x y i : Fin n) (hne : x ≠ y) :
    ((if (if b then y else x) = i then (1:ℝ) else 0) - (if (if b' then y else x) = i then 1 else 0)) =
      if b ≠ b' then (if b then -1 else 1) * ((if i = x then 1 else 0) - (if i = y then 1 else 0))
      else 0 := by
  by_cases h1 : x = i <;> by_cases h2 : y = i
  · exact absurd (h1.trans h2.symm) hne
  all_goals (cases b <;> cases b' <;> simp [h1, h2, eq_comm])

/-- Difference of two score vectors is the signed flow on the pairs where they differ. -/
theorem score_sub (t t' : Tournament n) (i : Fin n) :
    score t i - score t' i = flowVec ((Finset.univ : Finset (Pair n)).filter fun e => t e ≠ t' e)
      (fun e => if t e then -1 else 1) i := by
  unfold score flowVec inc
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  exact score_aux (t e) (t' e) e.1.1 e.1.2 i e.2.ne

end RQCEnergy



noncomputable section

namespace RQCRef
open RankingQueryCost.Joint RQCEnergy

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The tournament read off a complete record. -/
def tourOf (T : Transcript n) : Tournament n := fun e => (T e).getD false

theorem refcount_eq_score (T : Transcript n) (hT : ∀ e, (T e).isSome = true) (i : Fin n) :
    (referenceCount T Finset.univ i : ℝ) = score (tourOf T) i := by
  rw [score_eq]
  congr 1
  symm
  unfold referenceCount
  refine Finset.card_bij (fun e _ => if e.1.1 = i then e.1.2 else e.1.1) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hw := he.2
    unfold winner tourOf at hw
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hT e)
    rw [hb] at hw
    simp only [Option.getD_some] at hw
    cases b
    · simp only [Bool.false_eq_true, if_false] at hw
      rw [if_pos hw]
      exact ⟨e, Or.inr ⟨hw, rfl, hb⟩⟩
    · simp only [if_true] at hw
      have hne : e.1.1 ≠ i := fun h => e.2.ne (h.trans hw.symm)
      rw [if_neg hne]
      exact ⟨e, Or.inl ⟨rfl, hw, hb⟩⟩
  · intro e he f hf hef
    rw [Finset.mem_filter] at he hf
    have he' := he.2; have hf' := hf.2
    unfold winner at he' hf'
    have h1 : e.1.1.val < e.1.2.val := e.2
    have h2 : f.1.1.val < f.1.2.val := f.2
    apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;>
      (split_ifs at hef he' hf' with ha hb hc hd <;> simp only [Fin.ext_iff] at * <;> omega)
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨e, he⟩ := ha.2
    refine ⟨e, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold winner tourOf
      rcases he with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [h3]; simp [h2]
      · rw [h3]; simp [h1]
    · rcases he with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · have : e.1.1 ≠ i := fun h => e.2.ne (h.trans h2.symm)
        rw [if_neg this, h1]
      · rw [if_pos h1, h2]

end RQCRef



noncomputable section

namespace RQCRef
open RankingQueryCost.Joint RQCEnergy

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem clause3 (s : ℕ) (hn : 2 ≤ n) (T : Transcript n) (hst : StarsPresent T Finset.univ) (r : Rank n)
    (hr : r ∈ compatible s T) :
    squaredError (referenceOrder T Finset.univ (List.finRange n)) (rankVector r) ≤ 8 * crudeScale n s := by
  have hcomp : ∀ e, (T e).isSome = true := fun e => hst e (Or.inl (Finset.mem_univ _))
  set t := tourOf T
  set D := (Finset.univ : Finset (Pair n)).filter fun e => t e ≠ truthful r e
  have hD : D.card ≤ s := by
    have hsub : D ⊆ disSet T r := by
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hcomp e)
      rw [disSet, Finset.mem_filter]
      refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hcomp e⟩, ?_⟩
      rw [hb]; intro h
      apply he.2
      simp only [Option.some.injEq] at h
      simp [t, tourOf, hb, h]
    exact le_trans (Finset.card_le_card hsub) hr
  have hc : ∀ e ∈ D, |(fun e => if t e then (-1 : ℝ) else 1) e| ≤ 1 := by
    intro e _; simp only; split_ifs <;> simp
  have hflow : ∀ i, (referenceCount T Finset.univ i : ℝ) - rankVector r i =
      flowVec D (fun e => if t e then -1 else 1) i := by
    intro i
    rw [refcount_eq_score T hcomp i, ← score_truthful r, score_sub]
  have hE : ∑ i, ((referenceCount T Finset.univ i : ℝ) - rankVector r i) ^ 2 ≤ s * min (s + 1) n := by
    simp only [hflow]
    have hq := energy_le_quad D _ hc
    have hl := energy_le_nD D _ hc
    have hDs : (D.card : ℝ) ≤ s := by exact_mod_cast hD
    have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
    rcases le_total (s + 1) n with h | h
    · rw [min_eq_left h]; push_cast; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hnear := ref_nearest T Finset.univ 1 zero_le_one r
  have hD2 : squaredError (referenceOrder T Finset.univ (List.finRange n)) (rankVector r) ≤
      4 * ∑ i, ((referenceCount T Finset.univ i : ℝ) - rankVector r i) ^ 2 := by
    unfold squaredError
    have := sq_add_weighted (fun i => referenceOrder T Finset.univ (List.finRange n) i - 1 * referenceCount T Finset.univ i)
      (fun i => 1 * (referenceCount T Finset.univ i : ℝ) - rankVector r i) 1 one_pos
    simp only [sub_add_sub_cancel] at this
    have e : ∑ i, (rankVector r i - 1 * (referenceCount T Finset.univ i : ℝ)) ^ 2 =
        ∑ i, ((referenceCount T Finset.univ i : ℝ) - rankVector r i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i, (1 * (referenceCount T Finset.univ i : ℝ) - rankVector r i) ^ 2 =
        ∑ i, ((referenceCount T Finset.univ i : ℝ) - rankVector r i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e] at hnear
    rw [e2] at this
    norm_num at this hnear
    linarith
  refine le_trans hD2 ?_
  unfold crudeScale
  have key : (s : ℝ) * min ((s : ℝ) + 1) (n : ℝ) ≤ 2 * ((s * min s (n - 1) : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; simp
    · have hc : ((s * min s (n - 1) : ℕ) : ℝ) = (s : ℝ) * min (s : ℝ) ((n : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_min, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [hc]
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      rcases le_total (s : ℝ) ((n : ℝ) - 1) with h | h
      · rw [min_eq_left h]
        have : min ((s : ℝ) + 1) (n : ℝ) ≤ s + 1 := min_le_left _ _
        nlinarith
      · rw [min_eq_right h]
        have : min ((s : ℝ) + 1) (n : ℝ) ≤ n := min_le_right _ _
        nlinarith
  have hmin : ((min (s + 1) n : ℕ) : ℝ) = min ((s : ℝ) + 1) (n : ℝ) := by rw [Nat.cast_min]; push_cast; rfl
  rw [hmin] at hE
  linarith

theorem ref_expect (s k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) (r : Rank n)
    (T : Finset (Fin n) → Transcript n)
    (hT : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, StarsPresent (T S) S ∧ r ∈ compatible s (T S)) :
    (1 / (n.choose k : ℝ)) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, denseCertificate s k (T S) S ≤
      (8 * (n : ℝ) ^ 3 + 112 * (n : ℝ) ^ 2 * s) / k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hCk : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  set H : ℝ := 2 * (n : ℝ) ^ 2 * s / k
  set T2r : Finset (Fin n) → ℝ := fun S => ∑ l : Fin n, (((l : ℕ) : ℝ) - ((n : ℝ) / k) *
    (S.filter fun a => (r a : ℕ) < l.val).card) ^ 2
  have hper : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, denseCertificate s k (T S) S ≤ 32 * T2r S + 56 * H := by
    intro S hS
    have hS' := Finset.mem_powersetCard.1 hS
    have := qstat_le s k hk (T S) S hS'.2 (hT S hS).1 r (hT S hS).2
    unfold denseCertificate
    have : (24 : ℝ) * (2 * (n : ℝ) ^ 2 * s / k) = 24 * H := rfl
    linarith
  -- the cardinality of the threshold sets
  have hAl : ∀ l : Fin n, ((Finset.univ.filter fun a : Fin n => (r a : ℕ) < l.val).card) = l.val := by
    intro l
    have : (Finset.univ.filter fun a : Fin n => (r a : ℕ) < l.val).card =
        (Finset.univ.filter fun x : Fin n => x.val < l.val).card := by
      refine Finset.card_bij (fun a _ => r a) ?_ ?_ ?_
      · intro a ha; simpa using ha
      · intro a _ a' _ h; exact r.injective h
      · intro x hx; exact ⟨r.symm x, by simpa using hx, by simp⟩
    rw [this, Fin.card_filter_val_lt]; omega
  have hsumT : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, T2r S =
      (n.choose k : ℝ) * ((n : ℝ) * (n + 1) * (n - k) / (6 * k)) := by
    simp only [T2r]
    rw [Finset.sum_comm]
    have : ∀ l : Fin n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (((l : ℕ) : ℝ) - ((n : ℝ) / k) * (S.filter fun a => (r a : ℕ) < l.val).card) ^ 2 =
        (n.choose k : ℝ) * ((l.val : ℝ) * ((n : ℝ) - l.val) * ((n : ℝ) - k) / (k * ((n : ℝ) - 1))) := by
      intro l
      have h := hyper_sum k hk hn (Finset.univ.filter fun a : Fin n => (r a : ℕ) < l.val)
      rw [hAl l] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro S _
      congr 3
      rw [Finset.inter_filter, Finset.inter_univ]
    rw [Finset.sum_congr rfl (fun l _ => this l)]
    rw [← Finset.mul_sum]
    have hs : ∑ l : Fin n, ((l.val : ℝ) * ((n : ℝ) - l.val) * ((n : ℝ) - k) / (k * ((n : ℝ) - 1))) =
        ((n : ℝ) - k) / (k * ((n : ℝ) - 1)) * ∑ l ∈ Finset.range n, (l : ℝ) * ((n : ℝ) - l) := by
      rw [← Fin.sum_univ_eq_sum_range (fun l => (l : ℝ) * ((n : ℝ) - l)) n, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _; ring
    rw [hs, sum_l_nl]
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    field_simp
  have hsum : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, denseCertificate s k (T S) S ≤
      32 * ((n.choose k : ℝ) * ((n : ℝ) * (n + 1) * (n - k) / (6 * k))) + 56 * H * (n.choose k : ℝ) := by
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumT, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  rw [one_div, inv_mul_le_iff₀ hCk]
  refine le_trans hsum ?_
  have hb : 32 * ((n : ℝ) * (n + 1) * (n - k) / (6 * k)) ≤ 8 * (n : ℝ) ^ 3 / k := by
    rw [show 32 * ((n : ℝ) * (n + 1) * (n - k) / (6 * k)) = (32 * ((n : ℝ) * (n + 1) * (n - k))) / (6 * k) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((n : ℝ) + 1) * (n - k) ≤ (n : ℝ) ^ 2 := by
      have : ((n : ℝ) + 1) * (n - k) ≤ ((n : ℝ) + 1) * (n - 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have h2 : 32 * (n : ℝ) * k * (((n : ℝ) + 1) * (n - k)) ≤ 32 * (n : ℝ) * k * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 * k := by positivity
    nlinarith
  have hH : 56 * H = 112 * (n : ℝ) ^ 2 * s / k := by simp only [H]; ring
  have : (8 * (n : ℝ) ^ 3 + 112 * (n : ℝ) ^ 2 * s) / k = 8 * (n : ℝ) ^ 3 / k + 112 * (n : ℝ) ^ 2 * s / k := by ring
  rw [this]
  nlinarith

end RQCRef



open RankingQueryCost.Joint RQCRef

theorem solution (n s k : ℕ) (hadm : Admissible n s) (hk : 1 ≤ k ∧ k ≤ n)
    (r : Rank n) (T : Finset (Fin n) → Transcript n)
    (hT : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      StarsPresent (T S) S ∧ r ∈ compatible s (T S)) :
    (∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∀ r' ∈ compatible s (T S),
        squaredError (referenceOrder (T S) S (List.finRange n)) (rankVector r') ≤
          denseCertificate s k (T S) S) ∧
    ((1 / (n.choose k : ℝ)) *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        denseCertificate s k (T S) S) ≤
      (8 * (n : ℝ) ^ 3 + 112 * (n : ℝ) ^ 2 * s) / k ∧
    (k = n → ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∀ r' ∈ compatible s (T S),
        squaredError (referenceOrder (T S) S (List.finRange n)) (rankVector r') ≤
          8 * (crudeScale n s : ℝ)) := by
  have hn : 2 ≤ n := by have := hadm.1; omega
  refine ⟨?_, ref_expect s k hn hk.1 hk.2 r T hT, ?_⟩
  · intro S hS r' hr'
    exact ref_sound s k hk.1 (T S) S (Finset.mem_powersetCard.1 hS).2 (hT S hS).1 r' hr'
  · intro hkn S hS r' hr'
    have hSu : S = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [(Finset.mem_powersetCard.1 hS).2, hkn, Fintype.card_fin]
    have hst := (hT S hS).1
    subst hSu
    exact clause3 s hn (T Finset.univ) hst r' hr'
