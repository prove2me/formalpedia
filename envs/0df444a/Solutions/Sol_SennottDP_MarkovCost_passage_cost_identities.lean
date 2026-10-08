-- Prove2me | solution 1 for SennottDP.MarkovCost.passage_cost_identities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:25:40.886086+00:00
-- url     : https://prove2.me/submissions/db923f21-aa6f-4dab-a384-0c8ddde72fa5

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology


namespace SennottDP.MarkovCost

set_option linter.unusedSectionVars false
variable {S : Type} [Countable S]

lemma tsum_snoc {t : ℕ} (f : (Fin (t+2) → S) → ℝ≥0∞) :
    ∑' y, f y = ∑' x : Fin (t+1) → S, ∑' k : S, f (Fin.snoc x k) := by
  calc ∑' y, f y = ∑' c : S × (Fin (t+1) → S), f (Fin.snoc c.2 c.1) :=
        ((Fin.snocEquiv (fun _ => S)).tsum_eq f).symm
    _ = ∑' k : S, ∑' x : Fin (t+1) → S, f (Fin.snoc x k) :=
        ENNReal.tsum_prod (f := fun a b => f (Fin.snoc b a))
    _ = _ := ENNReal.tsum_comm

lemma tsum_cons {t : ℕ} (f : (Fin (t+2) → S) → ℝ≥0∞) :
    ∑' y, f y = ∑' j : S, ∑' x : Fin (t+1) → S, f (Fin.cons j x) := by
  calc ∑' y, f y = ∑' c : S × (Fin (t+1) → S), f (Fin.cons c.1 c.2) :=
        ((Fin.consEquiv (fun _ => S)).tsum_eq f).symm
    _ = _ := ENNReal.tsum_prod (f := fun a b => f (Fin.cons a b))

lemma pathProb_snoc (M : MC S) {t : ℕ} (x : Fin (t+1) → S) (k : S) :
    pathProb M (Fin.snoc x k : Fin (t+2) → S) = pathProb M x * M.P (x (Fin.last t)) k := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl; intro s _
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

lemma pathProb_cons (M : MC S) {t : ℕ} (x : Fin (t+1) → S) (i : S) :
    pathProb M (Fin.cons i x : Fin (t+2) → S) = M.P i (x 0) * pathProb M x := by
  unfold pathProb
  rw [Fin.prod_univ_succ]
  simp


lemma snoc_zero' {t : ℕ} (x : Fin (t+1) → S) (k : S) :
    (Fin.snoc x k : Fin (t+2) → S) 0 = x 0 := by
  have : (0 : Fin (t+2)) = Fin.castSucc 0 := rfl
  rw [this, Fin.snoc_castSucc]

lemma forall_snoc_iff {t : ℕ} (x : Fin (t+1) → S) (k : S) (Q : S → Prop) (lo : ℕ) :
    (∀ s : Fin (t+2), lo < s.val → s.val < t + 1 → Q ((Fin.snoc x k : Fin (t+2) → S) s)) ↔
    (∀ s : Fin (t+1), lo < s.val → Q (x s)) := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last, lt_irrefl]
  constructor
  · intro h s h1; exact h.1 s h1 s.isLt
  · intro h; exact ⟨fun s h1 _ => h s h1, fun _ h => h.elim⟩

lemma forall_snoc_iff' {t : ℕ} (x : Fin (t+1) → S) (k : S) (Q : S → Prop) (lo : ℕ) (hlo : lo < t + 1) :
    (∀ s : Fin (t+2), lo < s.val → Q ((Fin.snoc x k : Fin (t+2) → S) s)) ↔
    (∀ s : Fin (t+1), lo < s.val → Q (x s)) ∧ Q k := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last, Fin.snoc_last]
  constructor
  · intro h; exact ⟨h.1, h.2 hlo⟩
  · intro h; exact ⟨h.1, fun _ => h.2⟩

open Classical in
lemma avoid_succ_last (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G (t+1) i k = if k ∈ G then 0 else ∑' l, avoidProb M G t i l * M.P l k := by
  unfold avoidProb
  rw [tsum_snoc]
  have hL : ∀ x : Fin (t+1) → S, (∑' k' : S,
      (if (Fin.snoc x k' : Fin (t+2) → S) 0 = i ∧ (Fin.snoc x k' : Fin (t+2) → S) (Fin.last (t+1)) = k ∧
        ∀ s : Fin (t + 1 + 1), 0 < s.val → (Fin.snoc x k' : Fin (t+2) → S) s ∉ G
      then pathProb M (Fin.snoc x k' : Fin (t+2) → S) else 0)) =
      if k ∈ G then 0 else (if x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G then
        pathProb M x * M.P (x (Fin.last t)) k else 0) := by
    intro x
    rw [tsum_eq_single k]
    · simp only [snoc_zero', Fin.snoc_last, forall_snoc_iff' x k (· ∉ G) 0 (by omega), pathProb_snoc]
      by_cases hk : k ∈ G <;> simp [hk]
    · intro k' hk'
      rw [Fin.snoc_last]; simp [hk']
  simp_rw [hL]
  by_cases hk : k ∈ G
  · simp [hk]
  simp only [hk, if_false]
  simp_rw [← ENNReal.tsum_mul_right, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [tsum_eq_single (x (Fin.last t))]
  · by_cases h : x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G
    · simp [h]
    · simp only [h, if_false]; rw [if_neg]; tauto
  · intro l hl; rw [if_neg]; intro h; exact hl h.2.1.symm

open Classical in
lemma avoid_zero (M : MC S) (G : Set S) (i k : S) :
    avoidProb M G 0 i k = if i = k then 1 else 0 := by
  unfold avoidProb
  rw [tsum_eq_single (fun _ => i)]
  · by_cases h : i = k
    · subst h; simp [pathProb]
    · simp [h]
  · intro x hx
    rw [if_neg]
    rintro ⟨h0, -, -⟩
    apply hx; funext s; rw [show s = 0 from Fin.ext (by have := s.isLt; omega), h0]

open Classical in
lemma taboo_succ_last (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    taboo M G (t+1) i k = ∑' l, avoidProb M G t i l * M.P l k := by
  unfold taboo avoidProb
  rw [tsum_snoc]
  have hL : ∀ x : Fin (t+1) → S, (∑' k' : S,
      (if (Fin.snoc x k' : Fin (t+2) → S) 0 = i ∧ (Fin.snoc x k' : Fin (t+2) → S) (Fin.last (t+1)) = k ∧
        ∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 → (Fin.snoc x k' : Fin (t+2) → S) s ∉ G
      then pathProb M (Fin.snoc x k' : Fin (t+2) → S) else 0)) =
      (if x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G then
        pathProb M x * M.P (x (Fin.last t)) k else 0) := by
    intro x
    rw [tsum_eq_single k]
    · simp only [snoc_zero', Fin.snoc_last, forall_snoc_iff x k (· ∉ G) 0, pathProb_snoc]
      simp
    · intro k' hk'
      rw [Fin.snoc_last]; simp [hk']
  simp_rw [hL]
  simp_rw [← ENNReal.tsum_mul_right, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [tsum_eq_single (x (Fin.last t))]
  · by_cases h : x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G
    · simp [h]
    · simp only [h, if_false]; rw [if_neg]; tauto
  · intro l hl; rw [if_neg]; intro h; exact hl h.2.1.symm

lemma cons_last' {t : ℕ} (x : Fin (t+1) → S) (j : S) :
    (Fin.cons j x : Fin (t+2) → S) (Fin.last (t+1)) = x (Fin.last t) := by
  rw [← Fin.succ_last, Fin.cons_succ]

lemma forall_cons_iff {t : ℕ} (x : Fin (t+1) → S) (j : S) (Q : S → Prop) :
    (∀ s : Fin (t+2), 0 < s.val → Q ((Fin.cons j x : Fin (t+2) → S) s)) ↔
    Q (x 0) ∧ (∀ s : Fin (t+1), 0 < s.val → Q (x s)) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.val_zero, lt_irrefl, Fin.val_succ, Fin.cons_succ, IsEmpty.forall_iff, true_and,
    Nat.succ_pos, forall_const]
  constructor
  · intro h; exact ⟨h 0, fun s _ => h s⟩
  · intro h s
    rcases Nat.eq_zero_or_pos s.val with hs | hs
    · have : s = 0 := Fin.ext hs
      subst this; exact h.1
    · exact h.2 s hs

open Classical in
lemma avoid_succ_first (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G (t+1) i k = ∑' j, if j ∈ G then 0 else M.P i j * avoidProb M G t j k := by
  unfold avoidProb
  rw [tsum_cons]
  rw [tsum_eq_single i]
  · have hL : ∀ x : Fin (t+1) → S,
        (if (Fin.cons i x : Fin (t+2) → S) 0 = i ∧ (Fin.cons i x : Fin (t+2) → S) (Fin.last (t+1)) = k ∧
          ∀ s : Fin (t + 1 + 1), 0 < s.val → (Fin.cons i x : Fin (t+2) → S) s ∉ G
        then pathProb M (Fin.cons i x : Fin (t+2) → S) else 0) =
        ∑' j, (if j ∈ G then 0 else (if x 0 = j ∧ x (Fin.last t) = k ∧
          ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G then M.P i j * pathProb M x else 0)) := by
      intro x
      rw [tsum_eq_single (x 0)]
      · simp only [Fin.cons_zero, cons_last', forall_cons_iff x i (· ∉ G), pathProb_cons, true_and]
        by_cases h0 : x 0 ∈ G
        · simp [h0]
        · simp [h0]
      · intro j hj; simp [Ne.symm hj]
    simp_rw [hL]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    by_cases hj : j ∈ G
    · simp [hj]
    · simp only [hj, if_false]
      rw [← ENNReal.tsum_mul_left]
      congr 1; ext x
      split_ifs <;> simp
  · intro j hj
    apply ENNReal.tsum_eq_zero.2
    intro x; rw [Fin.cons_zero, if_neg]; tauto

open Classical in
lemma taboo_zero (M : MC S) (G : Set S) (i k : S) :
    taboo M G 0 i k = if i = k then 1 else 0 := by
  unfold taboo
  rw [tsum_eq_single (fun _ => i)]
  · by_cases h : i = k
    · subst h; simp [pathProb]
    · simp [h]
  · intro x hx
    rw [if_neg]
    rintro ⟨h0, -, -⟩
    apply hx; funext s; rw [show s = 0 from Fin.ext (by have := s.isLt; omega), h0]

lemma avoid_le_nStep (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G t i k ≤ nStep M t i k := by
  induction t generalizing k with
  | zero => rw [avoid_zero]; simp [nStep]
  | succ t ih =>
    rw [avoid_succ_last]
    split_ifs
    · simp
    · simp only [nStep]
      exact ENNReal.tsum_le_tsum fun l => by gcongr; exact ih l

lemma taboo_le_nStep (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    taboo M G t i k ≤ nStep M t i k := by
  cases t with
  | zero => rw [taboo_zero]; simp [nStep]
  | succ t =>
    rw [taboo_succ_last]; simp only [nStep]
    exact ENNReal.tsum_le_tsum fun l => by gcongr; exact avoid_le_nStep M G t i l

open Classical in
/-- probability of jumping into `G` in one step -/
noncomputable def toG (M : MC S) (G : Set S) (l : S) : ℝ≥0∞ :=
  ∑' k, if k ∈ G then M.P l k else 0

open Classical in
lemma fp_succ (M : MC S) (G : Set S) (i : S) (t : ℕ) :
    firstPassProb M G i (t+1) = ∑' l, avoidProb M G t i l * toG M G l := by
  unfold firstPassProb toG
  simp only [Nat.add_one_ne_zero, if_false, taboo_succ_last]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; ext k
  split_ifs <;> simp

lemma fp_zero (M : MC S) (G : Set S) (i : S) : firstPassProb M G i 0 = 0 := by
  simp [firstPassProb]

/-- `P(T > t)` -/
noncomputable def survive (M : MC S) (G : Set S) (t : ℕ) (i : S) : ℝ≥0∞ :=
  ∑' k, avoidProb M G t i k

lemma survive_zero (M : MC S) (G : Set S) (i : S) : survive M G 0 i = 1 := by
  unfold survive
  simp_rw [avoid_zero]
  rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp

open Classical in
lemma survive_succ (M : MC S) (G : Set S) (t : ℕ) (i : S) :
    survive M G (t+1) i + firstPassProb M G i (t+1) = survive M G t i := by
  unfold survive
  rw [fp_succ]
  unfold toG
  simp_rw [avoid_succ_last]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm (f := fun l k => avoidProb M G t i l * if k ∈ G then M.P l k else 0),
    ← ENNReal.tsum_add]
  have : ∀ k, ((if k ∈ G then 0 else ∑' l, avoidProb M G t i l * M.P l k) +
      ∑' l, avoidProb M G t i l * if k ∈ G then M.P l k else 0) =
      ∑' l, avoidProb M G t i l * M.P l k := by
    intro k; split_ifs <;> simp
  simp_rw [this]
  rw [ENNReal.tsum_comm]
  congr 1; ext l
  rw [ENNReal.tsum_mul_left, M.P_sum, mul_one]

lemma survive_add_sum (M : MC S) (G : Set S) (i : S) (n : ℕ) :
    survive M G n i + ∑ t ∈ Finset.range (n+1), firstPassProb M G i t = 1 := by
  induction n with
  | zero => simp [survive_zero, fp_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (firstPassProb M G i (n+1)), ← add_assoc,
      add_comm (firstPassProb M G i (n+1)), survive_succ, ih]

lemma hitProb_le_one (M : MC S) (G : Set S) (i : S) : hitProb M G i ≤ 1 := by
  unfold hitProb
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  calc ∑ t ∈ Finset.range n, firstPassProb M G i t
      ≤ ∑ t ∈ Finset.range (n+1), firstPassProb M G i t :=
        Finset.sum_le_sum_of_subset (by simp)
    _ ≤ survive M G n i + ∑ t ∈ Finset.range (n+1), firstPassProb M G i t := le_add_self
    _ = 1 := survive_add_sum M G i n

lemma hit_eq_one_of_summable (M : MC S) (G : Set S) (i : S)
    (h : ∑' t, survive M G t i ≠ ⊤) : hitProb M G i = 1 := by
  apply le_antisymm (hitProb_le_one M G i)
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h
  have key : ∀ n, 1 ≤ survive M G n i + hitProb M G i := by
    intro n
    rw [← survive_add_sum M G i n]
    gcongr
    exact ENNReal.sum_le_tsum _
  have hlim : Tendsto (fun n => survive M G n i + hitProb M G i) atTop (𝓝 (0 + hitProb M G i)) :=
    ht.add tendsto_const_nhds
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim key

lemma survive_eq_tail (M : MC S) (G : Set S) (i : S) (h : hitProb M G i = 1) (s : ℕ) :
    survive M G s i = ∑' t, firstPassProb M G i (t + (s+1)) := by
  have h1 := survive_add_sum M G i s
  have h2 : ∑ t ∈ Finset.range (s+1), firstPassProb M G i t +
      ∑' t, firstPassProb M G i (t + (s+1)) = 1 := by
    rw [ENNReal.summable.sum_add_tsum_nat_add']
    exact h
  have hfin : ∑ t ∈ Finset.range (s+1), firstPassProb M G i t ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    rw [← h1]; exact le_add_self
  rw [add_comm] at h1
  rw [← h2] at h1
  exact (ENNReal.add_right_inj hfin).1 h1

lemma meanPassage_eq_survive (M : MC S) (G : Set S) (i : S) :
    meanPassage M G i = ∑' t, survive M G t i := by
  unfold meanPassage
  split_ifs with h
  · have e1 : ∀ t : ℕ, (t : ℝ≥0∞) * firstPassProb M G i t =
        ∑' s : ℕ, if s < t then firstPassProb M G i t else 0 := by
      intro t
      rw [tsum_eq_sum (s := Finset.range t)]
      · rw [Finset.sum_ite_of_true (fun s hs => Finset.mem_range.1 hs)]
        simp
      · intro s hs; rw [if_neg]; simpa using hs
    simp_rw [e1]
    rw [ENNReal.tsum_comm]
    congr 1; ext s
    rw [survive_eq_tail M G i h s]
    rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := s+1)]
    · rw [Finset.sum_eq_zero]
      · simp only [zero_add]
        congr 1; ext t; rw [if_pos (by omega)]
      · intro x hx; rw [if_neg]; simp at hx; omega
  · by_contra hne
    exact h (hit_eq_one_of_summable M G i (Ne.symm hne))

lemma visits_sum (M : MC S) (G : Set S) (i : S) :
    ∑' k, visits M G i k = meanPassage M G i := by
  rw [meanPassage_eq_survive]
  unfold visits survive
  exact ENNReal.tsum_comm

lemma hitProb_succ (M : MC S) (G : Set S) (i : S) :
    hitProb M G i = ∑' t, firstPassProb M G i (t+1) := by
  unfold hitProb
  rw [tsum_eq_zero_add' ENNReal.summable, fp_zero, zero_add]

open Classical in
lemma hit_first_step (M : MC S) (G : Set S) (i : S) :
    hitProb M G i = ∑' j, M.P i j * (if j ∈ G then 1 else hitProb M G j) := by
  rw [hitProb_succ, tsum_eq_zero_add' ENNReal.summable]
  have h0 : firstPassProb M G i (0+1) = ∑' j, if j ∈ G then M.P i j else 0 := by
    rw [fp_succ]; simp_rw [avoid_zero]
    rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp [toG]
  have h1 : ∀ t, firstPassProb M G i (t+1+1) =
      ∑' j, if j ∈ G then 0 else M.P i j * firstPassProb M G j (t+1) := by
    intro t
    rw [fp_succ]; simp_rw [avoid_succ_first, fp_succ]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · simp_rw [← ENNReal.tsum_mul_left, mul_assoc]
  rw [h0]
  simp_rw [h1]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
  congr 1; ext j
  split_ifs
  · simp
  · simp only [zero_add]
    rw [ENNReal.tsum_mul_left, hitProb_succ]

open Classical in
lemma hit_zero_of_not_leads (M : MC S) (G : Set S) (k : S)
    (h : ∀ g ∈ G, ¬ LeadsTo M k g) : hitProb M G k = 0 := by
  unfold hitProb
  apply ENNReal.tsum_eq_zero.2
  intro t
  unfold firstPassProb
  split_ifs
  · rfl
  apply ENNReal.tsum_eq_zero.2
  intro g
  split_ifs with hg
  · apply le_antisymm _ (zero_le)
    have := taboo_le_nStep M G t k g
    have h2 : nStep M t k g = 0 := by
      by_contra hne; exact h g hg ⟨t, pos_iff_ne_zero.2 hne⟩
    rw [h2] at this; exact this
  · rfl

lemma leadsTo_refl (M : MC S) (i : S) : LeadsTo M i i := ⟨0, by simp [nStep]⟩

lemma exists_pos_of_tsum_pos {α : Type} {f : α → ℝ≥0∞} (h : 0 < ∑' l, f l) : ∃ l, 0 < f l := by
  by_contra hn
  push_neg at hn
  have : ∑' l, f l = 0 := ENNReal.tsum_eq_zero.2 fun l => le_antisymm (hn l) (zero_le)
  rw [this] at h; exact lt_irrefl _ h

lemma nStep_succ_pos (M : MC S) {t : ℕ} {a b c : S} (h1 : 0 < nStep M t a b) (h2 : 0 < M.P b c) :
    0 < nStep M (t+1) a c := by
  simp only [nStep]
  exact lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne') (ENNReal.le_tsum b)

lemma leadsTo_trans (M : MC S) {a b c : S} (h1 : LeadsTo M a b) (h2 : LeadsTo M b c) :
    LeadsTo M a c := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  induction t generalizing c with
  | zero =>
    simp only [nStep] at ht
    split_ifs at ht with h
    · subst h; exact ⟨s, hs⟩
    · exact absurd ht (lt_irrefl _)
  | succ t ih =>
    simp only [nStep] at ht
    obtain ⟨m, hm⟩ := exists_pos_of_tsum_pos ht
    have hm1 : 0 < nStep M t b m := pos_iff_ne_zero.2 (left_ne_zero_of_mul hm.ne')
    have hm2 : 0 < M.P m c := pos_iff_ne_zero.2 (right_ne_zero_of_mul hm.ne')
    obtain ⟨u, hu⟩ := ih hm1
    exact ⟨u+1, nStep_succ_pos M hu hm2⟩

lemma leadsTo_of_P (M : MC S) {a b : S} (h : 0 < M.P a b) : LeadsTo M a b :=
  ⟨1, nStep_succ_pos (t := 0) M (by simp [nStep]) h⟩

open Classical in
lemma close_step (M : MC S) (i k : S) (hi : hitProb M {i} i = 1) (hk : 0 < M.P i k) :
    LeadsTo M k i := by
  by_contra hn
  have hki : k ≠ i := by rintro rfl; exact hn (leadsTo_refl M k)
  have h0 : hitProb M {i} k = 0 :=
    hit_zero_of_not_leads M {i} k (by intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg; exact hn)
  have hfs := hit_first_step M {i} i
  rw [hi] at hfs
  have key : (1 : ℝ≥0∞) + M.P i k ≤ 1 + 0 := by
    rw [add_zero]
    nth_rewrite 2 [← M.P_sum i]
    nth_rewrite 1 [hfs]
    have : M.P i k = ∑' j, M.P i j * (if j = k then 1 else 0) := by
      rw [tsum_eq_single k (by intro b hb; simp [hb])]; simp
    rw [this, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [← mul_add]
    apply mul_le_of_le_one_right (zero_le)
    by_cases hj : j = k
    · subst hj; simp [hki, h0]
    · simp only [hj, if_false, add_zero]
      split_ifs
      · exact le_rfl
      · exact hitProb_le_one M {i} j
  have := (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 key
  exact absurd (le_antisymm this (zero_le)) hk.ne'

lemma avoid_succ_self (M : MC S) (i : S) (t : ℕ) : avoidProb M {i} (t+1) i i = 0 := by
  rw [avoid_succ_last]; simp

lemma visits_eq_succ (M : MC S) (G : Set S) (i k : S) :
    visits M G i k = avoidProb M G 0 i k + ∑' t, avoidProb M G (t+1) i k := by
  unfold visits; rw [tsum_eq_zero_add' ENNReal.summable]

lemma visits_self (M : MC S) (i : S) : visits M {i} i i = 1 := by
  rw [visits_eq_succ]; simp [avoid_succ_self, avoid_zero]

lemma visits_ne (M : MC S) (G : Set S) {i k : S} (h : i ≠ k) :
    visits M G i k = ∑' t, avoidProb M G (t+1) i k := by
  rw [visits_eq_succ, avoid_zero]; simp [h]

lemma u_invariant (M : MC S) (i : S) (hi : hitProb M {i} i = 1) (k : S) :
    visits M {i} i k = ∑' l, visits M {i} i l * M.P l k := by
  unfold visits
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [← taboo_succ_last]
  by_cases hk : k = i
  · subst hk
    rw [← visits.eq_def, visits_self, ← hi, hitProb_succ]
    congr 1; ext t
    unfold firstPassProb
    simp only [Nat.add_one_ne_zero, if_false, Set.mem_singleton_iff]
    rw [tsum_eq_single k (by intro b hb; simp [hb])]; simp
  · rw [← visits.eq_def, visits_ne M _ (Ne.symm hk)]
    congr 1; ext t
    rw [taboo_succ_last, avoid_succ_last]; simp [hk]

lemma iterate_inv (M : MC S) (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k) (t : ℕ) (k : S) :
    ∑' l, x l * nStep M t l k = x k := by
  induction t generalizing k with
  | zero =>
    simp only [nStep]
    rw [tsum_eq_single k (by intro b hb; simp [hb])]; simp
  | succ t ih =>
    simp only [nStep]
    simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right, ih]
    exact (hx k).symm

lemma inv_le_of_lead (M : MC S) (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k) {j i : S}
    (h : LeadsTo M j i) (hz : x i = 0) : x j = 0 := by
  obtain ⟨t, ht⟩ := h
  have := iterate_inv M x hx t i
  rw [hz] at this
  have h2 : x j * nStep M t j i = 0 := le_antisymm (this ▸ ENNReal.le_tsum j) zero_le
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 ht.ne'

lemma U_ge (M : MC S) (i : S) (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k)
    (hxi : x i = 1) (k : S) : visits M {i} i k ≤ x k := by
  by_cases hk : k = i
  · subst hk; rw [visits_self, hxi]
  rw [visits_ne M _ (Ne.symm hk)]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    by_cases hk' : k = i
    · subst hk'; simp [avoid_succ_self]
    have e : ∀ t, avoidProb M {i} (t+1) i k = ∑' l, avoidProb M {i} t i l * M.P l k := by
      intro t; rw [avoid_succ_last]; simp [hk']
    simp_rw [e]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    rw [hx k]
    apply ENNReal.tsum_le_tsum
    intro l
    rw [← Finset.sum_mul]
    gcongr
    rw [Finset.sum_range_succ']
    by_cases hl : l = i
    · subst hl; simp [avoid_succ_self, avoid_zero, hxi]
    · rw [avoid_zero, if_neg (Ne.symm hl), add_zero]
      exact ih l hl

lemma U_eq (M : MC S) (i : S) (hi : hitProb M {i} i = 1) (hm : meanPassage M {i} i < ⊤)
    (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k)
    (hxi : x i = 1) (hfin : ∀ k, x k ≠ ⊤) (j : S) (hj : LeadsTo M j i) :
    x j = visits M {i} i j := by
  set u := visits M {i} i with hu
  have hle := U_ge M i x hx hxi
  have ufin : ∀ k, u k ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hm.ne (by rw [← visits_sum]; exact ENNReal.le_tsum k)
  set μ := fun k => x k - u k with hμ
  have hxμ : ∀ k, x k = μ k + u k := fun k => (tsub_add_cancel_of_le (hle k)).symm
  have hinv : ∀ k, μ k = ∑' l, μ l * M.P l k := by
    intro k
    have h1 := hx k
    rw [hxμ k] at h1
    simp_rw [hxμ, add_mul] at h1
    rw [ENNReal.tsum_add, ← u_invariant M i hi k] at h1
    exact (ENNReal.add_left_inj (ufin k)).1 h1
  have hμi : μ i = 0 := by simp [hμ, hxi, hu, visits_self]
  have := inv_le_of_lead M μ hinv hj hμi
  rw [hxμ j, this, zero_add]

lemma pr_mem_lead (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R)
    (hj : j ∈ R) : LeadsTo M j i := by
  obtain ⟨x0, rfl⟩ := hR.1
  exact leadsTo_trans M hj.2 hi.1

lemma pr_nonempty (M : MC S) {R : Set S} (hR : IsPosRecClass M R) : ∃ i, i ∈ R := by
  obtain ⟨x0, rfl⟩ := hR.1
  exact ⟨x0, leadsTo_refl M x0, leadsTo_refl M x0⟩

lemma pr_closed (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i : S} (hi : i ∈ R)
    {t : ℕ} {l : S} (h : 0 < nStep M t i l) : l ∈ R := by
  have hR2 := hR.2
  obtain ⟨x0, rfl⟩ := hR.1
  have key : ∀ t l, 0 < nStep M t i l → LeadsTo M l i := by
    intro t
    induction t with
    | zero =>
      intro l hl
      simp only [nStep] at hl
      split_ifs at hl with h
      · subst h; exact leadsTo_refl M i
      · exact absurd hl (lt_irrefl _)
    | succ t ih =>
      intro l hl
      simp only [nStep] at hl
      obtain ⟨m, hm⟩ := exists_pos_of_tsum_pos hl
      have hm1 : 0 < nStep M t i m := pos_iff_ne_zero.2 (left_ne_zero_of_mul hm.ne')
      have hm2 : 0 < M.P m l := pos_iff_ne_zero.2 (right_ne_zero_of_mul hm.ne')
      have hmi := ih m hm1
      have hmR : m ∈ commClass M x0 :=
        ⟨leadsTo_trans M hi.1 ⟨t, hm1⟩, leadsTo_trans M hmi hi.2⟩
      exact leadsTo_trans M (close_step M m l (hR2 m hmR).1 hm2) hmi
  have hl := key t l h
  exact ⟨leadsTo_trans M hi.1 ⟨t, h⟩, leadsTo_trans M hl hi.2⟩

lemma pr_visits_out (M : MC S) {R : Set S} (hR : IsPosRecClass M R) (G : Set S) {i l : S}
    (hi : i ∈ R) (hl : l ∉ R) : visits M G i l = 0 := by
  unfold visits
  apply ENNReal.tsum_eq_zero.2
  intro t
  have h1 := avoid_le_nStep M G t i l
  have h2 : nStep M t i l = 0 := by
    by_contra hne; exact hl (pr_closed M hR hi (pos_iff_ne_zero.2 hne))
  rw [h2] at h1; exact le_antisymm h1 zero_le

lemma pr_P_out (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {l k : S}
    (hl : l ∈ R) (hk : k ∉ R) : M.P l k = 0 := by
  by_contra hne
  exact hk (pr_closed M hR hl (nStep_succ_pos (t := 0) M (by simp [nStep]) (pos_iff_ne_zero.2 hne)))

lemma u_le_m (M : MC S) (i k : S) : visits M {i} i k ≤ meanPassage M {i} i := by
  rw [← visits_sum]; exact ENNReal.le_tsum k

lemma m_ne_zero (M : MC S) (i : S) : meanPassage M {i} i ≠ 0 := by
  intro h
  have := u_le_m M i i
  rw [visits_self, h] at this
  exact absurd this (by simp)

lemma pr_key (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R) (hj : j ∈ R) :
    meanPassage M {i} i = meanPassage M {j} j * visits M {i} i j := by
  obtain ⟨hjh, hjm⟩ := hR.2 j hj
  obtain ⟨hih, him⟩ := hR.2 i hi
  set c := visits M {j} j i with hc
  have cfin : c ≠ ⊤ := ne_top_of_le_ne_top hjm.ne (u_le_m M j i)
  have c0 : c ≠ 0 := by
    intro h0
    have := inv_le_of_lead M (visits M {j} j) (u_invariant M j hjh) (pr_mem_lead M hR hi hj) h0
    rw [visits_self] at this; exact one_ne_zero this
  set x := fun k => visits M {j} j k / c with hxdef
  have hx : ∀ k, x k = ∑' l, x l * M.P l k := by
    intro k
    simp only [hxdef, div_eq_mul_inv]
    rw [u_invariant M j hjh k, ← ENNReal.tsum_mul_right]
    congr 1; ext l; ring
  have hxi : x i = 1 := ENNReal.div_self c0 cfin
  have hfin : ∀ k, x k ≠ ⊤ := fun k =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top hjm.ne (u_le_m M j k)) c0
  have hxe : ∀ k, x k = visits M {i} i k := by
    intro k
    by_cases hk : k ∈ R
    · exact U_eq M i hih him x hx hxi hfin k (pr_mem_lead M hR hi hk)
    · simp only [hxdef]
      rw [pr_visits_out M hR {j} hj hk, pr_visits_out M hR {i} hi hk, ENNReal.zero_div]
  have hsum : ∑' k, x k = meanPassage M {j} j / c := by
    simp only [hxdef, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, visits_sum]
  simp_rw [hxe] at hsum
  rw [visits_sum] at hsum
  rw [hsum, ← hxe j]
  simp only [hxdef, visits_self, div_eq_mul_inv, one_mul]

lemma pr_formula (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R) (hj : j ∈ R) :
    steadyState M j = (meanPassage M {i} i)⁻¹ * visits M {i} i j := by
  have hk := pr_key M hR hi hj
  have him := (hR.2 i hi).2
  set v := visits M {i} i j
  have vfin : v ≠ ⊤ := ne_top_of_le_ne_top him.ne (u_le_m M i j)
  have v0 : v ≠ 0 := by
    intro h; apply m_ne_zero M i; rw [hk, h, mul_zero]
  unfold steadyState
  rw [hk, ENNReal.mul_inv (Or.inr vfin) (Or.inr v0), mul_assoc, ENNReal.inv_mul_cancel v0 vfin,
    mul_one]

theorem steady_state_core (M : MC S) (R : Set S)
    (hR : IsPosRecClass M R) :
    ((∀ j ∈ R, steadyState M j = ∑' i : R, M.P i j * steadyState M i) ∧
      ∑' j : R, steadyState M j = 1 ∧
      ∀ x : S → ℝ≥0∞, (∀ j ∈ R, x j = ∑' i : R, M.P i j * x i) → ∑' j : R, x j = 1 →
        ∀ j ∈ R, x j = steadyState M j) ∧
    (∀ i ∈ R, ∀ j ∈ R,
      steadyState M j = visits M {i} i j / meanPassage M {i} i ∧
      steadyState M j = steadyState M i * visits M {i} i j) := by
  obtain ⟨i0, hi0⟩ := pr_nonempty M hR
  have hm0 := (hR.2 i0 hi0).2
  have hsupp : ∀ (i : S), i ∈ R → ∀ f : S → ℝ≥0∞,
      ∑' l : R, visits M {i} i l * f l = ∑' l, visits M {i} i l * f l := by
    intro i hi f
    refine tsum_subtype_eq_of_support_subset (f := fun l => visits M {i} i l * f l) (s := R) ?_
    intro l hl
    by_contra hlR
    apply hl
    simp [pr_visits_out M hR {i} hi hlR]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    have e : ∀ l : R, M.P l j * steadyState M l =
        (meanPassage M {j} j)⁻¹ * (visits M {j} j l * M.P l j) := by
      intro l; rw [pr_formula M hR hj l.2]; ring
    rw [tsum_congr e, ENNReal.tsum_mul_left, hsupp j hj (fun l => M.P l j),
      ← u_invariant M j (hR.2 j hj).1 j, visits_self, mul_one]
    rfl
  · have e : ∀ l : R, steadyState M l = (meanPassage M {i0} i0)⁻¹ * (visits M {i0} i0 l * 1) := by
      intro l; rw [pr_formula M hR hi0 l.2, mul_one]
    rw [tsum_congr e, ENNReal.tsum_mul_left, hsupp i0 hi0 (fun _ => 1)]
    simp only [mul_one]
    rw [visits_sum, ENNReal.inv_mul_cancel (m_ne_zero M i0) hm0.ne]
  · intro x hxinv hxs
    classical
    set xt : S → ℝ≥0∞ := fun k => if k ∈ R then x k else 0 with hxt
    have hsub : ∀ k, ∑' l, xt l * M.P l k = ∑' l : R, M.P l k * x l := by
      intro k
      rw [← tsum_subtype_eq_of_support_subset (f := fun l => xt l * M.P l k) (s := R)]
      · apply tsum_congr; intro l; simp [hxt, l.2, mul_comm]
      · intro l hl; by_contra hlR; apply hl; simp [hxt, hlR]
    have hinv : ∀ k, xt k = ∑' l, xt l * M.P l k := by
      intro k
      rw [hsub k]
      by_cases hk : k ∈ R
      · simp only [hxt, hk, if_true]; exact hxinv k hk
      · simp only [hxt, hk, if_false]
        symm; apply ENNReal.tsum_eq_zero.2; intro l
        rw [pr_P_out M hR l.2 hk, zero_mul]
    have hxle : ∀ k ∈ R, x k ≤ 1 := by
      intro k hk; rw [← hxs]; exact ENNReal.le_tsum (⟨k, hk⟩ : R)
    have xtfin : ∀ k, xt k ≠ ⊤ := by
      intro k; simp only [hxt]; split_ifs with hk
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (hxle k hk)
      · exact ENNReal.zero_ne_top
    have hsumxt : ∑' k, xt k = 1 := by
      rw [← hxs, ← tsum_subtype_eq_of_support_subset (f := xt) (s := R)]
      · apply tsum_congr; intro l; simp [hxt, l.2]
      · intro l hl; by_contra hlR; apply hl; simp [hxt, hlR]
    set c := xt i0 with hc
    have c0 : c ≠ 0 := by
      intro h0
      have : ∀ k, xt k = 0 := by
        intro k
        by_cases hk : k ∈ R
        · exact inv_le_of_lead M xt hinv (pr_mem_lead M hR hi0 hk) h0
        · simp [hxt, hk]
      rw [ENNReal.tsum_eq_zero.2 this] at hsumxt
      exact zero_ne_one hsumxt
    have cfin : c ≠ ⊤ := xtfin i0
    set y := fun k => xt k / c with hy
    have hyinv : ∀ k, y k = ∑' l, y l * M.P l k := by
      intro k
      simp only [hy, div_eq_mul_inv]
      rw [hinv k, ← ENNReal.tsum_mul_right]
      congr 1; ext l; ring
    have hye : ∀ k, y k = visits M {i0} i0 k := by
      intro k
      by_cases hk : k ∈ R
      · exact U_eq M i0 (hR.2 i0 hi0).1 hm0 y hyinv (ENNReal.div_self c0 cfin)
          (fun k => ENNReal.div_ne_top (xtfin k) c0) k (pr_mem_lead M hR hi0 hk)
      · simp only [hy, hxt, hk, if_false, ENNReal.zero_div]
        rw [pr_visits_out M hR {i0} hi0 hk]
    have hxty : ∀ k, xt k = c * y k := fun k => (ENNReal.mul_div_cancel c0 cfin).symm
    have hcm : c * meanPassage M {i0} i0 = 1 := by
      rw [← hsumxt, ← visits_sum, ← ENNReal.tsum_mul_left]
      apply tsum_congr; intro k; rw [hxty k, hye k]
    have hc' := ENNReal.eq_inv_of_mul_eq_one_left hcm
    intro j hj
    have : x j = xt j := by simp [hxt, hj]
    rw [this, hxty j, hye j, hc', pr_formula M hR hi0 hj]
  · intro i hi j hj
    rw [pr_formula M hR hi hj]
    refine ⟨by rw [div_eq_mul_inv, mul_comm], rfl⟩

open Classical in
lemma survive_succ_first (M : MC S) (G : Set S) (t : ℕ) (i : S) :
    survive M G (t+1) i = ∑' j, if j ∈ G then 0 else M.P i j * survive M G t j := by
  unfold survive
  simp_rw [avoid_succ_first]
  rw [ENNReal.tsum_comm]
  congr 1; ext j
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left]

open Classical in
lemma mean_bound (M : MC S) (G : Set S) (V : S → ℝ≥0∞)
    (hV : ∀ i, 1 + ∑' j, (if j ∈ G then 0 else M.P i j * V j) ≤ V i) (i : S) :
    meanPassage M G i ≤ V i := by
  rw [meanPassage_eq_survive]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', survive_zero]
    simp_rw [survive_succ_first]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), add_comm]
    refine le_trans ?_ (hV i)
    gcongr with j
    split_ifs
    · simp
    · rw [← Finset.mul_sum]; gcongr; exact ih j

open Classical in
lemma visits_first (M : MC S) (G : Set S) (i k : S) :
    visits M G i k = (if i = k then 1 else 0) +
      ∑' j, if j ∈ G then 0 else M.P i j * visits M G j k := by
  rw [visits_eq_succ, avoid_zero]
  congr 1
  simp_rw [avoid_succ_first]
  rw [ENNReal.tsum_comm]
  congr 1; ext j
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left]; rfl

open Classical in
lemma wvisits_first (M : MC S) (G : Set S) (w : S → ℝ≥0∞) (i : S) :
    ∑' k, w k * visits M G i k = w i +
      ∑' j, if j ∈ G then 0 else M.P i j * ∑' k, w k * visits M G j k := by
  simp_rw [visits_first M G i, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp
  · simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · congr 1; ext k; ring

open Classical in
lemma propagate (M : MC S) (z : S) (f : S → ℝ≥0∞)
    (hf : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * f j) ≤ f i)
    (hz : f z < ⊤) : ∀ t l, 0 < nStep M t z l → f l < ⊤ := by
  intro t
  induction t with
  | zero =>
    intro l hl; simp only [nStep] at hl
    split_ifs at hl with h
    · subst h; exact hz
    · exact absurd hl (lt_irrefl _)
  | succ t ih =>
    intro l hl
    simp only [nStep] at hl
    obtain ⟨m, hm⟩ := exists_pos_of_tsum_pos hl
    have hm1 : 0 < nStep M t z m := pos_iff_ne_zero.2 (left_ne_zero_of_mul hm.ne')
    have hm2 : 0 < M.P m l := pos_iff_ne_zero.2 (right_ne_zero_of_mul hm.ne')
    have hmf := ih m hm1
    by_cases hlz : l = z
    · subst hlz; exact hz
    have : M.P m l * f l ≤ f m := by
      refine le_trans ?_ (hf m)
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum l)
      simp [hlz]
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top hm2.ne'] at this
    exact absurd (lt_of_lt_of_le hmf this) (lt_irrefl _)

open Classical in
noncomputable def pcT (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) : ℝ≥0∞ :=
  ∑' x : Fin (t + 1) → S,
    if t ≠ 0 ∧ x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G) ∧
        x (Fin.last t) ∈ G
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

lemma passageCost_eq (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) :
    passageCost M C G i = ∑' t, pcT M C G t i := rfl

lemma pcT_zero (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) : pcT M C G 0 i = 0 := by
  simp [pcT]

open Classical in
lemma fp_path (M : MC S) (G : Set S) (j : S) (t : ℕ) :
    firstPassProb M G j (t+1) = ∑' x : Fin (t+2) → S,
      if x 0 = j ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧ x (Fin.last (t+1)) ∈ G
      then pathProb M x else 0 := by
  unfold firstPassProb taboo
  simp only [Nat.add_one_ne_zero, if_false]
  have : ∀ k, (if k ∈ G then ∑' x : Fin (t+1+1) → S, (if x 0 = j ∧ x (Fin.last (t+1)) = k ∧
      (∀ s : Fin (t+1+1), 0 < s.val → s.val < t+1 → x s ∉ G) then pathProb M x else 0) else 0) =
      ∑' x : Fin (t+1+1) → S, (if k ∈ G ∧ x 0 = j ∧ x (Fin.last (t+1)) = k ∧
      (∀ s : Fin (t+1+1), 0 < s.val → s.val < t+1 → x s ∉ G) then pathProb M x else 0) := by
    intro k; split_ifs with hk
    · congr 1; ext x; simp [hk]
    · symm; apply ENNReal.tsum_eq_zero.2; intro x; simp [hk]
  simp_rw [this]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [tsum_eq_single (x (Fin.last (t+1)))]
  · apply if_congr _ rfl rfl; tauto
  · intro k hk; rw [if_neg]; intro h; exact hk h.2.2.1.symm

lemma forall_cons_iff2 {t : ℕ} (x : Fin (t+2) → S) (j : S) (Q : S → Prop) :
    (∀ s : Fin (t+3), 0 < s.val → s.val < t + 2 → Q ((Fin.cons j x : Fin (t+3) → S) s)) ↔
    Q (x 0) ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t + 1 → Q (x s)) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.val_zero, lt_irrefl, Fin.val_succ, Fin.cons_succ, IsEmpty.forall_iff, true_and,
    Nat.succ_pos, forall_const, add_lt_add_iff_right]
  constructor
  · intro h; exact ⟨h 0 (by simp), fun s _ hs => h s hs⟩
  · intro h s hs
    rcases Nat.eq_zero_or_pos s.val with h0 | h0
    · have : s = 0 := Fin.ext h0
      subst this; exact h.1
    · exact h.2 s h0 hs

open Classical in
lemma pcT_succ (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) :
    pcT M C G (t+1) i = (C i : ℝ≥0∞) * firstPassProb M G i (t+1) +
      ∑' j, if j ∈ G then 0 else M.P i j * pcT M C G t j := by
  have e1 : pcT M C G (t+1) i = ∑' x : Fin (t+2) → S,
      ((if x 0 = i ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧
        x (Fin.last (t+1)) ∈ G then (C i : ℝ≥0∞) * pathProb M x else 0) +
      (if x 0 = i ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧
        x (Fin.last (t+1)) ∈ G then pathProb M x * ∑ s : Fin t, (C (x s.succ.castSucc) : ℝ≥0∞)
        else 0)) := by
    unfold pcT
    congr 1; ext x
    have hiff : ∀ P : Prop, (t + 1 ≠ 0 ∧ P) ↔ P := fun P => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    simp only [hiff]
    split_ifs with h
    · rw [Fin.sum_univ_succ]
      simp only [Fin.castSucc_zero, h.1]
      ring
    · simp
  rw [e1, ENNReal.tsum_add, fp_path]
  congr 1
  · rw [← ENNReal.tsum_mul_left]; congr 1; ext x; split_ifs <;> simp
  · cases t with
    | zero =>
      simp [pcT_zero]
    | succ t =>
      rw [tsum_cons, tsum_eq_single i]
      · have hL : ∀ x : Fin (t+2) → S,
            (if (Fin.cons i x : Fin (t+3) → S) 0 = i ∧
              (∀ s : Fin (t+1+2), 0 < s.val → s.val < t+1+1 → (Fin.cons i x : Fin (t+3) → S) s ∉ G) ∧
              (Fin.cons i x : Fin (t+3) → S) (Fin.last (t+1+1)) ∈ G
            then pathProb M (Fin.cons i x : Fin (t+3) → S) *
              ∑ s : Fin (t+1), (C ((Fin.cons i x : Fin (t+3) → S) s.succ.castSucc) : ℝ≥0∞) else 0) =
            ∑' j, if j ∈ G then 0 else
              (if x 0 = j ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧
                x (Fin.last (t+1)) ∈ G then
                M.P i j * (pathProb M x * ∑ s : Fin (t+1), (C (x s.castSucc) : ℝ≥0∞)) else 0) := by
          intro x
          rw [tsum_eq_single (x 0)]
          · have hc : ∀ s : Fin (t+1), (Fin.cons i x : Fin (t+3) → S) s.succ.castSucc = x s.castSucc := by
              intro s; rw [← Fin.succ_castSucc, Fin.cons_succ]
            simp only [Fin.cons_zero, cons_last', forall_cons_iff2 x i (· ∉ G), pathProb_cons,
              true_and, hc]
            by_cases h0 : x 0 ∈ G
            · simp [h0]
            · simp only [h0, if_false, not_false_eq_true, true_and]
              split_ifs <;> ring
          · intro j hj; simp [Ne.symm hj]
        simp_rw [hL]
        rw [ENNReal.tsum_comm]
        congr 1; ext j
        by_cases hj : j ∈ G
        · simp [hj]
        · simp only [hj, if_false]
          unfold pcT
          rw [← ENNReal.tsum_mul_left]
          congr 1; ext x
          have hiff : ∀ P : Prop, (t + 1 ≠ 0 ∧ P) ↔ P := fun P => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
          simp only [hiff]
          split_ifs <;> simp
      · intro j hj
        apply ENNReal.tsum_eq_zero.2
        intro x; rw [Fin.cons_zero, if_neg]; tauto

open Classical in
lemma pc_bound (M : MC S) (C : S → ℝ≥0) (G : Set S) (V : S → ℝ≥0∞)
    (hV : ∀ i, (C i : ℝ≥0∞) + ∑' j, (if j ∈ G then 0 else M.P i j * V j) ≤ V i) (i : S) :
    passageCost M C G i ≤ V i := by
  rw [passageCost_eq]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', pcT_zero, add_zero]
    simp_rw [pcT_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine le_trans (add_le_add ?_ ?_) (hV i)
    · apply mul_le_of_le_one_right zero_le
      refine le_trans ?_ (hitProb_le_one M G i)
      unfold hitProb
      rw [tsum_eq_zero_add' ENNReal.summable, fp_zero, zero_add]
      exact ENNReal.sum_le_tsum _
    · apply ENNReal.tsum_le_tsum; intro j
      split_ifs
      · simp
      · rw [← Finset.mul_sum]; gcongr; exact ih j

lemma univ_posrec (M : MC S) (hirr : Irreducible M) (hpr : ∀ i, PositiveRecurrent M i) (z : S) :
    IsPosRecClass M Set.univ :=
  ⟨⟨z, by ext j; simp only [Set.mem_univ, true_iff]; exact hirr z j⟩, fun j _ => hpr j⟩

open Classical in
theorem lyap_part2 (M : MC S) (C : S → ℝ≥0) (hirr : Irreducible M)
    (hpr : ∀ i, PositiveRecurrent M i) (hJ : classAvgCost M C Set.univ < ⊤) (z : S) :
    IsZStandard M C z := by
  have hR := univ_posrec M hirr hpr z
  have hmz := (hpr z).2
  intro i
  obtain ⟨t, ht⟩ := (hirr z i).1
  constructor
  · have e : ∀ i, meanPassage M {z} i = ∑' k, (1 : ℝ≥0∞) * visits M {z} i k := by
      intro i; simp [visits_sum]
    have hf : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * meanPassage M {z} j) ≤
        meanPassage M {z} i := by
      intro i
      rw [e i, wvisits_first]
      simp_rw [← e]
      exact le_add_self
    exact propagate M z _ hf hmz t i ht
  · set g := fun i => ∑' k, (C k : ℝ≥0∞) * visits M {z} i k with hg
    have hgi : ∀ i, g i = (C i : ℝ≥0∞) + ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * g j) := by
      intro i; exact wvisits_first M {z} (fun k => (C k : ℝ≥0∞)) i
    have hgz : g z < ⊤ := by
      have hu : ∀ k, visits M {z} z k = meanPassage M {z} z * steadyState M k := by
        intro k
        rw [pr_formula M hR (Set.mem_univ z) (Set.mem_univ k), ← mul_assoc,
          ENNReal.mul_inv_cancel (m_ne_zero M z) hmz.ne, one_mul]
      have : g z = meanPassage M {z} z * classAvgCost M C Set.univ := by
        simp only [hg, classAvgCost, hu]
        rw [tsum_univ (f := fun j => steadyState M j * (C j : ℝ≥0∞)), ← ENNReal.tsum_mul_left]
        congr 1; ext k; ring
      rw [this]; exact ENNReal.mul_lt_top hmz hJ
    have hf : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * g j) ≤ g i := by
      intro i; rw [hgi i]; exact le_add_self
    have hgfin := propagate M z g hf hgz t i ht
    exact lt_of_le_of_lt (pc_bound M C {z} g (fun i => (hgi i).symm.le) i) hgfin

open Classical in
lemma tsum_ite_drop (M : MC S) (z i : S) (f : S → ℝ≥0∞) :
    ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * f j) ≤ ∑' j, M.P i j * f j :=
  ENNReal.tsum_le_tsum fun j => by split_ifs <;> simp

open Classical in
lemma tsum_ite_congr_z (M : MC S) (z i : S) (f g : S → ℝ≥0∞) (h : ∀ j, j ≠ z → f j = g j) :
    ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * f j) =
    ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * g j) := by
  apply tsum_congr; intro j
  by_cases hj : j = z
  · simp [hj]
  · simp [hj, h j hj]

open Classical in
theorem lyap_part1 (M : MC S) (C : S → ℝ≥0) (z : S) (y : S → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (hzy : ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i)
    (r : S → ℝ≥0) (Hs : Finset S) (hzH : z ∈ Hs)
    (hHr : ∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤)
    (hrd : ∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) :
    IsZStandard M C z := by
  set e : ℝ≥0∞ := (ε : ℝ≥0∞) with he
  have e0 : e ≠ 0 := by simp [he, hε.ne']
  have et : e ≠ ⊤ := ENNReal.coe_ne_top
  set Py : S → ℝ≥0∞ := fun i => ∑' j, M.P i j * (y j : ℝ≥0∞) with hPy
  set Pr : S → ℝ≥0∞ := fun i => ∑' j, M.P i j * (r j : ℝ≥0∞) with hPr
  intro i
  constructor
  · set Q : S → ℝ≥0∞ := fun i =>
      ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * ((y j : ℝ≥0∞) * e⁻¹)) with hQ
    set V : S → ℝ≥0∞ := fun i => if i = z then 1 + Q z else (y i : ℝ≥0∞) * e⁻¹ with hV
    have hQle : ∀ i, Q i ≤ Py i * e⁻¹ := by
      intro i
      refine le_trans (tsum_ite_drop M z i _) (le_of_eq ?_)
      simp only [hPy]; rw [← ENNReal.tsum_mul_right]; congr 1; ext j; ring
    have hVQ : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) = Q i := by
      intro i
      apply tsum_ite_congr_z; intro j hj; simp [hV, hj]
    have hVb : ∀ i, 1 + ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) ≤ V i := by
      intro i
      rw [hVQ]
      by_cases hi : i = z
      · subst hi; simp [hV]
      · simp only [hV, hi, if_false]
        calc 1 + Q i ≤ 1 + Py i * e⁻¹ := by gcongr; exact hQle i
          _ = (Py i + e) * e⁻¹ := by rw [add_mul, ENNReal.mul_inv_cancel e0 et, add_comm]
          _ ≤ (y i : ℝ≥0∞) * e⁻¹ := by gcongr; exact hdrift i hi
    refine lt_of_le_of_lt (mean_bound M {z} V hVb i) ?_
    by_cases hi : i = z
    · simp only [hV, hi, if_true]
      refine lt_of_le_of_lt (add_le_add le_rfl (hQle z)) ?_
      exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
        ENNReal.mul_lt_top hzy (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 e0))⟩
    · simp only [hV, hi, if_false]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 e0))
  · set b : ℝ≥0∞ := ∑ h ∈ Hs, ((C h : ℝ≥0∞) + Pr h) with hb
    have bfin : b < ⊤ := by
      rw [hb, ENNReal.sum_lt_top]
      intro h hh
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, hHr h hh⟩
    set K : ℝ≥0∞ := b / e with hK
    have Kfin : K < ⊤ := ENNReal.div_lt_top bfin.ne e0
    have hKe : K * e = b := ENNReal.div_mul_cancel e0 et
    set W : S → ℝ≥0∞ := fun i => (r i : ℝ≥0∞) + K * (y i : ℝ≥0∞) with hW
    have hPW : ∀ i, ∑' j, M.P i j * W j = Pr i + K * Py i := by
      intro i
      simp only [hW, hPr, hPy, mul_add]
      rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      congr 1; congr 1; ext j; ring
    have hWd : ∀ i, i ≠ z → (C i : ℝ≥0∞) + ∑' j, M.P i j * W j ≤ W i := by
      intro i hi
      rw [hPW]
      by_cases hiH : i ∈ Hs
      · have h1 : (C i : ℝ≥0∞) + Pr i ≤ b :=
          Finset.single_le_sum (f := fun h => (C h : ℝ≥0∞) + Pr h) (fun _ _ => zero_le) hiH
        have h2 : b + K * Py i ≤ K * (y i : ℝ≥0∞) := by
          rw [← hKe, ← mul_add, add_comm]; gcongr; exact hdrift i hi
        calc (C i : ℝ≥0∞) + (Pr i + K * Py i) = ((C i : ℝ≥0∞) + Pr i) + K * Py i := by ring
          _ ≤ b + K * Py i := by gcongr
          _ ≤ K * (y i : ℝ≥0∞) := h2
          _ ≤ W i := le_add_self
      · have h1 := hrd i hiH
        have h2 : K * Py i ≤ K * (y i : ℝ≥0∞) := by
          gcongr; exact le_trans le_self_add (hdrift i hi)
        calc (C i : ℝ≥0∞) + (Pr i + K * Py i) = (Pr i + (C i : ℝ≥0∞)) + K * Py i := by ring
          _ ≤ (r i : ℝ≥0∞) + K * (y i : ℝ≥0∞) := add_le_add h1 h2
    set QW : S → ℝ≥0∞ := fun i =>
      ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * W j) with hQW
    set V : S → ℝ≥0∞ := fun i => if i = z then (C z : ℝ≥0∞) + QW z else W i with hV
    have hVQ : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) = QW i := by
      intro i
      apply tsum_ite_congr_z; intro j hj; simp [hV, hj]
    have hVb : ∀ i, (C i : ℝ≥0∞) + ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) ≤ V i := by
      intro i
      rw [hVQ]
      by_cases hi : i = z
      · subst hi; simp [hV]
      · simp only [hV, hi, if_false]
        exact le_trans (add_le_add le_rfl (tsum_ite_drop M z i W)) (hWd i hi)
    refine lt_of_le_of_lt (pc_bound M C {z} V hVb i) ?_
    by_cases hi : i = z
    · simp only [hV, hi, if_true]
      refine lt_of_le_of_lt (add_le_add le_rfl (tsum_ite_drop M z z W)) ?_
      rw [hPW]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.add_lt_top.2 ⟨hHr z hzH,
        ENNReal.mul_lt_top Kfin hzy⟩⟩
    · simp only [hV, hi, if_false, hW]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top Kfin ENNReal.coe_lt_top⟩

theorem lyap_core (M : MC S) (C : S → ℝ≥0) :
    (∀ (z : S) (y : S → ℝ≥0) (ε : ℝ≥0), 0 < ε → ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤ →
      (∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) →
      ∀ (r : S → ℝ≥0) (Hs : Finset S), z ∈ Hs →
      (∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤) →
      (∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) →
      IsZStandard M C z) ∧
    (Irreducible M → (∀ i, PositiveRecurrent M i) → classAvgCost M C Set.univ < ⊤ →
      ∀ z, IsZStandard M C z) :=
  ⟨fun z y ε hε hzy hd r Hs hzH hHr hrd => lyap_part1 M C z y ε hε hzy hd r Hs hzH hHr hrd,
   fun hirr hpr hJ z => lyap_part2 M C hirr hpr hJ z⟩

open Classical in
lemma tsum_compl_eq (G : Set S) (f : S → ℝ≥0∞) :
    ∑' j : ↥Gᶜ, f j = ∑' j, if j ∈ G then 0 else f j := by
  rw [tsum_subtype]; congr 1; ext j; simp [Set.indicator_apply]

lemma ennreal_dct {α : Type} (F : ℕ → α → ℝ≥0∞) (bound : α → ℝ≥0∞) (hb : ∀ n a, F n a ≤ bound a)
    (hfin : ∑' a, bound a ≠ ⊤) (hlim : ∀ a, Tendsto (fun n => F n a) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' a, F n a) atTop (𝓝 0) := by
  letI : MeasurableSpace α := ⊤
  have := MeasureTheory.tendsto_lintegral_of_dominated_convergence (μ := MeasureTheory.Measure.count)
    (f := fun _ => 0) bound (fun n => measurable_from_top)
    (fun n => Filter.Eventually.of_forall (hb n)) (by rwa [MeasureTheory.lintegral_count])
    (Filter.Eventually.of_forall hlim)
  simpa [MeasureTheory.lintegral_count] using this

lemma avoid_mono (M : MC S) {G : Set S} {g : S} (hg : g ∈ G) (t : ℕ) (i l : S) :
    avoidProb M G t i l ≤ avoidProb M {g} t i l := by
  induction t generalizing l with
  | zero => rw [avoid_zero, avoid_zero]
  | succ t ih =>
    rw [avoid_succ_last, avoid_succ_last]
    by_cases hl : l ∈ G
    · simp [hl]
    · have : l ∉ ({g} : Set S) := by
        rintro rfl; exact hl hg
      simp only [hl, this, if_false]
      exact ENNReal.tsum_le_tsum fun k => by gcongr; exact ih k

lemma mean_mono (M : MC S) {G : Set S} {g : S} (hg : g ∈ G) (i : S) :
    meanPassage M G i ≤ meanPassage M {g} i := by
  rw [meanPassage_eq_survive, meanPassage_eq_survive]
  exact ENNReal.tsum_le_tsum fun t => ENNReal.tsum_le_tsum fun l => avoid_mono M hg t i l

lemma survive_le_one (M : MC S) (G : Set S) (t : ℕ) (i : S) : survive M G t i ≤ 1 := by
  rw [← survive_add_sum M G i t]; exact le_self_add

open Classical in
lemma mean_eq_first (M : MC S) (G : Set S) (i : S) :
    meanPassage M G i = 1 + ∑' j, if j ∈ G then 0 else M.P i j * meanPassage M G j := by
  have e : ∀ i, meanPassage M G i = ∑' k, (1 : ℝ≥0∞) * visits M G i k := by
    intro i; simp [visits_sum]
  rw [e i, wvisits_first]
  simp_rw [← e]

open Classical in
lemma pr_mean_fin (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R)
    (hj : j ∈ R) : meanPassage M {j} i < ⊤ := by
  obtain ⟨t, ht⟩ := pr_mem_lead M hR hi hj
  have hf : ∀ i, ∑' l, (if l ∈ ({j} : Set S) then 0 else M.P i l * meanPassage M {j} l) ≤
      meanPassage M {j} i := by
    intro i; rw [mean_eq_first M {j} i]; exact le_add_self
  exact propagate M j _ hf (hR.2 j hj).2 t i ht

open Classical in
lemma piR_inv (M : MC S) {R : Set S} (hR : IsPosRecClass M R) (l : S) :
    ∑' k, (if k ∈ R then steadyState M k else 0) * M.P k l =
      if l ∈ R then steadyState M l else 0 := by
  have hss := (steady_state_core M R hR).1.1
  by_cases hl : l ∈ R
  · rw [if_pos hl, hss l hl, tsum_subtype (s := R) (f := fun k => M.P k l * steadyState M k)]
    congr 1; ext k; by_cases hk : k ∈ R <;> simp [hk, Set.indicator_apply, mul_comm]
  · rw [if_neg hl]
    apply ENNReal.tsum_eq_zero.2; intro k
    by_cases hk : k ∈ R
    · simp [hk, pr_P_out M hR hk hl]
    · simp [hk]

open Classical in
lemma visits_GG (M : MC S) (G : Set S) {i j : S} (hj : j ∈ G) :
    visits M G i j = if i = j then 1 else 0 := by
  rw [visits_eq_succ, avoid_zero]
  have : ∀ t, avoidProb M G (t+1) i j = 0 := fun t => by rw [avoid_succ_last]; simp [hj]
  simp [this]

open Classical in
theorem first_passage_core (M : MC S) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, ∀ k ∉ G,
      visits M G i k = (if i = k then 1 else 0) + ∑' t : ℕ, taboo M G (t + 1) i k) ∧
    (∀ i, meanPassage M G i = ∑' k, visits M G i k) ∧
    ((∀ i k, ∀ t : ℕ, 1 ≤ t →
        taboo M G (t + 1) i k = ∑' j : ↥Gᶜ, M.P i j * taboo M G t j k) ∧
      (∀ i k, visits M G i k = (if i = k then 1 else 0) + ∑' j : ↥Gᶜ, M.P i j * visits M G j k) ∧
      (∀ i, meanPassage M G i = 1 + ∑' j : ↥Gᶜ, M.P i j * meanPassage M G j)) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      (∀ j ∈ R, steadyState M j = ∑' i : G, steadyState M i * visits M G i j) ∧
      ∑' i : G, steadyState M i * meanPassage M G i = 1) ∧
    (∀ R : Set S, IsPosRecClass M R → ∀ i ∈ R, ∀ j ∈ R, meanPassage M {j} i < ⊤) := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i k hk
    rw [visits_eq_succ, avoid_zero]
    congr 1; congr 1; ext t
    rw [taboo_succ_last, avoid_succ_last, if_neg hk]
  · intro i; exact (visits_sum M G i).symm
  · intro i k t ht
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [tsum_compl_eq G (fun j => M.P i j * taboo M G (t+1) j k), taboo_succ_last]
    simp_rw [avoid_succ_first]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · rw [taboo_succ_last, ← ENNReal.tsum_mul_left]; congr 1; ext l; ring
  · intro i k
    rw [tsum_compl_eq G (fun j => M.P i j * visits M G j k)]; exact visits_first M G i k
  · intro i
    rw [tsum_compl_eq G (fun j => M.P i j * meanPassage M G j)]; exact mean_eq_first M G i
  · intro R hR hGR
    set πR : S → ℝ≥0∞ := fun k => if k ∈ R then steadyState M k else 0 with hπR
    have hinv : ∀ l, ∑' k, πR k * M.P k l = πR l := piR_inv M hR
    have hπsum : ∑' k, πR k = 1 := by
      rw [← (steady_state_core M R hR).1.2.1, tsum_subtype (s := R) (f := steadyState M)]
      congr 1
    have hfix : ∀ j ∈ R, steadyState M j = ∑' i : G, steadyState M i * visits M G i j := by
      intro j hj
      by_cases hjG : j ∈ G
      · rw [tsum_eq_single (⟨j, hjG⟩ : G)]
        · rw [visits_GG M G hjG]; simp
        · intro b hb
          rw [visits_GG M G hjG, if_neg, mul_zero]
          intro h; apply hb; exact Subtype.ext h
      -- j ∉ G
      set Rem : ℕ → ℝ≥0∞ := fun n =>
        ∑' k, πR k * (if k ∈ G then 0 else avoidProb M G n k j) with hRem
      set a : ℕ → ℝ≥0∞ := fun s =>
        ∑' k, πR k * (if k ∈ G then avoidProb M G (s+1) k j else 0) with ha
      have hstep : ∀ n, Rem (n+1) + a n = Rem n := by
        intro n
        simp only [hRem, ha]
        rw [← ENNReal.tsum_add]
        have : ∀ k, πR k * (if k ∈ G then 0 else avoidProb M G (n+1) k j) +
            πR k * (if k ∈ G then avoidProb M G (n+1) k j else 0) =
            πR k * avoidProb M G (n+1) k j := by
          intro k; split_ifs <;> simp
        simp_rw [this, avoid_succ_first]
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        congr 1; ext l
        split_ifs with hl
        · simp
        · rw [← hinv l, ← ENNReal.tsum_mul_right]
          congr 1; ext k; ring
      have hRem0 : Rem 0 = steadyState M j := by
        simp only [hRem]
        simp_rw [avoid_zero]
        rw [tsum_eq_single j]
        · simp [hjG, hπR, hj]
        · intro b hb; simp [Ne.symm hb, hb]
      have hsum : ∀ n, ∑ s ∈ Finset.range n, a s + Rem n = steadyState M j := by
        intro n
        induction n with
        | zero => simp [hRem0]
        | succ n ih => rw [Finset.sum_range_succ, ← ih, ← hstep n]; ring
      have hRemlim : Tendsto Rem atTop (𝓝 0) := by
        have hle : ∀ n, Rem n ≤ ∑' k, πR k * survive M G n k := by
          intro n
          apply ENNReal.tsum_le_tsum; intro k
          gcongr
          split_ifs
          · exact zero_le
          · exact ENNReal.le_tsum j
        have hd : Tendsto (fun n => ∑' k, πR k * survive M G n k) atTop (𝓝 0) := by
          apply ennreal_dct _ πR
          · intro n k; exact mul_le_of_le_one_right zero_le (survive_le_one M G n k)
          · rw [hπsum]; exact ENNReal.one_ne_top
          · intro k
            by_cases hk : k ∈ R
            · obtain ⟨g, hg⟩ := hG
              have hm : ∑' t, survive M G t k ≠ ⊤ := by
                rw [← meanPassage_eq_survive]
                exact (lt_of_le_of_lt (mean_mono M hg k) (pr_mean_fin M hR hk (hGR hg))).ne
              have := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hm
              simpa using ENNReal.Tendsto.const_mul this (Or.inr
                (ne_top_of_le_ne_top ENNReal.one_ne_top (hπsum ▸ ENNReal.le_tsum k)))
            · simp [hπR, hk]
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd (fun n => zero_le) hle
      have hlim1 : Tendsto (fun n => ∑ s ∈ Finset.range n, a s) atTop (𝓝 (∑' s, a s)) :=
        ENNReal.tendsto_nat_tsum a
      have hlim2 : Tendsto (fun n => ∑ s ∈ Finset.range n, a s + Rem n) atTop
          (𝓝 (∑' s, a s + 0)) := hlim1.add hRemlim
      simp_rw [hsum, add_zero] at hlim2
      have heq := tendsto_nhds_unique tendsto_const_nhds hlim2
      rw [heq]
      simp only [ha]
      rw [ENNReal.tsum_comm, tsum_subtype (s := G) (f := fun i => steadyState M i * visits M G i j)]
      congr 1; ext k
      by_cases hkG : k ∈ G
      · have hkR := hGR hkG
        have hkj : k ≠ j := fun h => hjG (h ▸ hkG)
        simp only [hπR, hkR, hkG, if_true, Set.indicator_apply]
        rw [ENNReal.tsum_mul_left, visits_ne M G hkj]
      · simp [hkG, Set.indicator_apply]
    refine ⟨hfix, ?_⟩
    simp_rw [← visits_sum]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    rw [← (steady_state_core M R hR).1.2.1]
    rw [← tsum_subtype_eq_of_support_subset (f := fun j => ∑' i : G, steadyState M i * visits M G i j)
      (s := R)]
    · exact tsum_congr fun j => (hfix j j.2).symm
    · intro j hj
      by_contra hjR
      apply hj
      apply ENNReal.tsum_eq_zero.2
      intro i
      simp [pr_visits_out M hR G (hGR i.2) hjR]
  · intro R hR i hi j hj
    exact pr_mean_fin M hR hi hj

open Classical in
lemma hit_split (M : MC S) (G : Set S) (i : S) :
    hitProb M G i = toG M G i + ∑' j, (if j ∈ G then 0 else M.P i j * hitProb M G j) := by
  rw [hit_first_step, toG, ← ENNReal.tsum_add]
  congr 1; ext j; split_ifs <;> simp

open Classical in
lemma pc_split (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) :
    passageCost M C G i = (C i : ℝ≥0∞) * hitProb M G i +
      ∑' j, (if j ∈ G then 0 else M.P i j * passageCost M C G j) := by
  rw [passageCost_eq, tsum_eq_zero_add' ENNReal.summable, pcT_zero, zero_add]
  simp_rw [pcT_succ]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← hitProb_succ, ENNReal.tsum_comm]
  congr 1
  congr 1; ext j
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left, passageCost_eq]

open Classical in
lemma iter_eq (M : MC S) (G : Set S) (f g : S → ℝ≥0∞)
    (hf : ∀ i, f i = g i + ∑' j, (if j ∈ G then 0 else M.P i j * f j)) (N : ℕ) (i : S) :
    f i = ∑ s ∈ Finset.range N, ∑' k, avoidProb M G s i k * g k +
      ∑' k, avoidProb M G N i k * f k := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    simp_rw [avoid_zero]
    rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    simp_rw [avoid_succ_last]
    conv_lhs => arg 1; ext k; rw [hf k]
    simp_rw [mul_add]
    rw [ENNReal.tsum_add]
    congr 1
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · rw [← ENNReal.tsum_mul_right]; congr 1; ext k; ring

lemma pointwise_of_tsum_eq {α : Type} (a b : α → ℝ≥0∞) (hle : ∀ k, b k ≤ a k)
    (heq : ∑' k, b k = ∑' k, a k) (hfin : ∑' k, a k ≠ ⊤) (k : α) : b k = a k := by
  classical
  by_contra hne
  have hlt : b k < a k := lt_of_le_of_ne (hle k) hne
  have h1 := ENNReal.tsum_eq_add_tsum_ite (f := b) k
  have h2 := ENNReal.tsum_eq_add_tsum_ite (f := a) k
  have hle2 : ∑' x, (if x = k then 0 else b x) ≤ ∑' x, (if x = k then 0 else a x) :=
    ENNReal.tsum_le_tsum fun x => by split_ifs <;> simp [hle x]
  have hfin2 : ∑' x, (if x = k then 0 else b x) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_trans hle2 (h2 ▸ le_add_self))
  have : ∑' x, b x < ∑' x, a x := by
    rw [h1, h2, add_comm (b k), add_comm (a k)]
    exact ENNReal.add_lt_add_of_le_of_lt hfin2 hle2 hlt
  rw [heq] at this; exact lt_irrefl _ this

lemma hit_support (M : MC S) (G : Set S) (i : S) (hi : hitProb M G i = 1) (N : ℕ) (k : S) :
    avoidProb M G N i k * hitProb M G k = avoidProb M G N i k := by
  have hit := iter_eq M G (hitProb M G) (toG M G) (hit_split M G) N i
  rw [hi] at hit
  have hs := survive_add_sum M G i N
  rw [Finset.sum_range_succ', fp_zero, add_zero] at hs
  simp_rw [fp_succ] at hs
  unfold survive at hs
  have hX : ∑ s ∈ Finset.range N, ∑' k, avoidProb M G s i k * toG M G k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hs ▸ le_add_self)
  rw [← hs, add_comm] at hit
  have heq := (ENNReal.add_right_inj hX).1 hit
  refine pointwise_of_tsum_eq (fun k => avoidProb M G N i k)
    (fun k => avoidProb M G N i k * hitProb M G k) ?_ heq.symm ?_ k
  · intro k; exact mul_le_of_le_one_right zero_le (hitProb_le_one M G k)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hs.le)

lemma hit_one_of_mean (M : MC S) (G : Set S) (i : S) (h : meanPassage M G i < ⊤) :
    hitProb M G i = 1 := by
  by_contra hne
  unfold meanPassage at h
  rw [if_neg hne] at h
  exact lt_irrefl _ h

lemma pc_eq_W (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) (hm : meanPassage M G i < ⊤) :
    passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k := by
  have hi := hit_one_of_mean M G i hm
  apply le_antisymm
  · exact pc_bound M C G _ (fun i => (wvisits_first M G (fun k => (C k : ℝ≥0∞)) i).symm.le) i
  · have hit := iter_eq M G (passageCost M C G) (fun k => (C k : ℝ≥0∞) * hitProb M G k)
      (pc_split M C G) 
    unfold visits
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply ENNReal.tsum_le_of_sum_range_le
    intro N
    rw [hit N i]
    refine le_trans ?_ le_self_add
    apply Finset.sum_le_sum
    intro s _
    apply le_of_eq
    congr 1; ext k
    rw [mul_comm (C k : ℝ≥0∞) (hitProb M G k), ← mul_assoc, hit_support M G i hi s k, mul_comm]

open Classical in
theorem passage_core (M : MC S) (C : S → ℝ≥0) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k) ∧
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = (C i : ℝ≥0∞) + ∑' j : ↥Gᶜ, M.P i j * passageCost M C G j) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      classAvgCost M C R = ∑' i : G, steadyState M i * passageCost M C G i) ∧
    (∀ R : Set S, IsPosRecClass M R → classAvgCost M C R < ⊤ →
      ∀ i ∈ R, ∀ j ∈ R, passageCost M C {j} i < ⊤) := by
  refine ⟨fun i hm => pc_eq_W M C G i hm, ?_, ?_, ?_⟩
  · intro i hm
    rw [tsum_compl_eq G (fun j => M.P i j * passageCost M C G j), pc_split,
      hit_one_of_mean M G i hm, mul_one]
  · intro R hR hGR
    have hfp := (first_passage_core M G hG).2.2.2.1 R hR hGR
    have e : ∀ i : G, steadyState M i * passageCost M C G i =
        ∑' k, steadyState M i * ((C k : ℝ≥0∞) * visits M G i k) := by
      intro i
      rw [pc_eq_W M C G i, ENNReal.tsum_mul_left]
      obtain ⟨i, hiG⟩ := i
      exact lt_of_le_of_lt (mean_mono M hiG i) (hR.2 i (hGR hiG)).2
    rw [tsum_congr e, ENNReal.tsum_comm, classAvgCost]
    rw [← tsum_subtype_eq_of_support_subset
      (f := fun k => ∑' i : G, steadyState M i * ((C k : ℝ≥0∞) * visits M G i k)) (s := R)]
    · apply tsum_congr; intro k
      rw [hfp.1 k k.2, ← ENNReal.tsum_mul_right]
      congr 1; ext i; ring
    · intro k hk
      by_contra hkR
      apply hk
      apply ENNReal.tsum_eq_zero.2
      intro i
      simp [pr_visits_out M hR G (hGR i.2) hkR]
  · intro R hR hJ i hi j hj
    obtain ⟨t, ht⟩ := pr_mem_lead M hR hi hj
    have hmj := (hR.2 j hj).2
    set g := fun i => ∑' k, (C k : ℝ≥0∞) * visits M {j} i k with hg
    have hgi : ∀ i, g i = (C i : ℝ≥0∞) + ∑' l, (if l ∈ ({j} : Set S) then 0 else M.P i l * g l) := by
      intro i; exact wvisits_first M {j} (fun k => (C k : ℝ≥0∞)) i
    have hgz : g j < ⊤ := by
      have : g j = meanPassage M {j} j * classAvgCost M C R := by
        simp only [hg, classAvgCost]
        rw [← ENNReal.tsum_mul_left]
        rw [← tsum_subtype_eq_of_support_subset
          (f := fun k => (C k : ℝ≥0∞) * visits M {j} j k) (s := R)]
        · apply tsum_congr; intro k
          rw [pr_formula M hR hj k.2, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (m_ne_zero M j) hmj.ne, one_mul, mul_comm]
        · intro k hk; by_contra hkR; apply hk
          simp [pr_visits_out M hR {j} hj hkR]
      rw [this]; exact ENNReal.mul_lt_top hmj hJ
    have hf : ∀ i, ∑' l, (if l ∈ ({j} : Set S) then 0 else M.P i l * g l) ≤ g i := by
      intro i; rw [hgi i]; exact le_add_self
    have hgfin := propagate M j g hf hgz t i ht
    exact lt_of_le_of_lt (pc_bound M C {j} g (fun i => (hgi i).symm.le) i) hgfin

end SennottDP.MarkovCost

open SennottDP.MarkovCost


theorem solution {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k) ∧
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = (C i : ℝ≥0∞) + ∑' j : ↥Gᶜ, M.P i j * passageCost M C G j) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      classAvgCost M C R = ∑' i : G, steadyState M i * passageCost M C G i) ∧
    (∀ R : Set S, IsPosRecClass M R → classAvgCost M C R < ⊤ →
      ∀ i ∈ R, ∀ j ∈ R, passageCost M C {j} i < ⊤) := by
  exact passage_core M C G hG
