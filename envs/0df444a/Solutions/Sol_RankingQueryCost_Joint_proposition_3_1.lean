-- Prove2me | solution 1 for RankingQueryCost.Joint.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:09:02.96729+00:00
-- url     : https://prove2.me/submissions/5b65b33a-16d0-4527-a238-d5227a73f1b5

import Definitions.Def_RankingQueryCost_Joint_Transcript
import Definitions.Def_RankingQueryCost_Joint_Scale

set_option autoImplicit false

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

open RankingQueryCost.Joint RQCEnergy

theorem solution (n s : ℕ) (hadm : Admissible n s) :
    (∀ (t : Tournament n) (r : Rank n),
      r ∈ compatible s (completeTranscript t) →
      squaredError (score t) (rankVector r) ≤ (errorScale n s : ℝ)) ∧
    (∀ (T : Transcript n) (t : Tournament n), SoundCompletion s T t →
      ∀ r ∈ compatible s T,
        squaredError (score t) (rankVector r) ≤ (errorScale n s : ℝ)) := by
  classical
  have hsN : s ≤ Fintype.card (Pair n) := by
    rw [card_pair]; have := hadm.2.2; unfold pairCount at this; omega
  have part1 : ∀ (t : Tournament n) (r : Rank n),
      r ∈ compatible s (completeTranscript t) →
      squaredError (score t) (rankVector r) ≤ (errorScale n s : ℝ) := by
    intro t r hr
    set D := (Finset.univ : Finset (Pair n)).filter fun e => t e ≠ truthful r e
    have hD : D.card ≤ s := by
      have : disagreements (completeTranscript t) r = D.card := by
        unfold disagreements
        congr 1
        ext e
        simp [acquired, completeTranscript, D]
      unfold compatible at hr; rw [Set.mem_setOf_eq] at hr; omega
    have hc : ∀ e ∈ D, |(fun e => if t e then (-1 : ℝ) else 1) e| ≤ 1 := by
      intro e _; simp only; split_ifs <;> simp
    have hz : squaredError (score t) (rankVector r) =
        ∑ i, flowVec D (fun e => if t e then -1 else 1) i ^ 2 := by
      unfold squaredError
      apply Finset.sum_congr rfl
      intro i _
      rw [← score_truthful r, score_sub]
    rw [hz]
    unfold errorScale incidenceCap
    rw [Nat.cast_min]
    apply le_min
    · have hq := energy_le_quad D _ hc
      have hl := energy_le_nD D _ hc
      have hDs : (D.card : ℝ) ≤ s := by exact_mod_cast hD
      rcases le_total (s + 1) n with hsn | hsn
      · rw [min_eq_left hsn]; push_cast
        have : (D.card : ℝ) * (D.card + 1) ≤ s * (s + 1) := by
          have : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
          nlinarith
        linarith
      · rw [min_eq_right hsn]; push_cast
        have : (n : ℝ) * D.card ≤ s * n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
    · refine le_trans (energy_le_degree D _ hc) ?_
      obtain ⟨D', hDD', hD'⟩ := Finset.exists_superset_card_eq (s := D) (n := s) hD
        (by simpa using hsN)
      have hmono : degreeSquareSum D ≤ degreeSquareSum D' := by
        unfold degreeSquareSum
        apply Finset.sum_le_sum
        intro i _
        apply Nat.pow_le_pow_left
        unfold supportDegree
        exact Finset.card_le_card (Finset.filter_subset_filter _ hDD')
      have hsup : degreeSquareSum D' ≤ extremalDegreeEnergy n s := by
        unfold extremalDegreeEnergy
        exact Finset.le_sup (f := degreeSquareSum)
          (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hD'⟩)
      exact_mod_cast le_trans hmono hsup
  refine ⟨part1, ?_⟩
  intro T t hT r hr
  apply part1 t r
  unfold compatible at hr ⊢
  rw [Set.mem_setOf_eq] at hr ⊢
  refine le_trans ?_ hr
  unfold disagreements
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  have he2 : t e ≠ truthful r e := by
    intro h; apply he.2; simp [completeTranscript, h]
  by_cases hTe : T e = none
  · exact absurd (hT.2 e hTe r hr) he2
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hTe
    have htb := hT.1 e b hb
    simp only [completeTranscript, Option.some.injEq] at htb
    refine ⟨by simp [acquired, hb], ?_⟩
    rw [hb]; intro h; apply he2; rw [htb]; simpa using h
