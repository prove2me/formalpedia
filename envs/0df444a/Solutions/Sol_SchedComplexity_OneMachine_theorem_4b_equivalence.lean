-- Prove2me | solution 1 for SchedComplexity.OneMachine.theorem_4b_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:16:37.475878+00:00
-- url     : https://prove2.me/submissions/88389b67-0cfd-4f5f-b9bf-5f7b60f87f69

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions



namespace SchedComplexity.OneMachine
open Finset

def spos {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) (j : Fin t) : ℕ :=
  ∑ k ∈ T.filter (· < j), p k

lemma spos_add_le {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) {j : Fin t} (hj : j ∈ T) :
    spos p T j + p j ≤ ∑ k ∈ T, p k := by
  unfold spos
  have : j ∉ T.filter (· < j) := by simp
  rw [add_comm, ← Finset.sum_insert this]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hj
  · exact (Finset.mem_filter.1 hx).1

lemma spos_step {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) {j k : Fin t} (hjk : j < k)
    (hj : j ∈ T) : spos p T j + p j ≤ spos p T k := by
  unfold spos
  have : j ∉ T.filter (· < j) := by simp
  rw [add_comm, ← Finset.sum_insert this]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · simp [hj, hjk]
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hjk⟩

lemma ico_fdisj {x p y q : ℕ} (h : x + p ≤ y ∨ y + q ≤ x) :
    Disjoint (Finset.Ico x (x+p)) (Finset.Ico y (y+q)) := by
  rw [Finset.disjoint_left]; intro z h1 h2
  simp only [Finset.mem_Ico] at h1 h2; omega

lemma ico_sdisj {x p y q : ℕ} (h : x + p ≤ y ∨ y + q ≤ x) :
    Disjoint (Set.Ico x (x+p)) (Set.Ico y (y+q)) := by
  rw [Set.disjoint_left]; intro z h1 h2
  simp only [Set.mem_Ico] at h1 h2; omega

lemma sep_of_sdisj {x p y q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : Disjoint (Set.Ico x (x+p)) (Set.Ico y (y+q))) : x + p ≤ y ∨ y + q ≤ x := by
  by_contra hc
  push Not at hc
  rw [Set.disjoint_left] at h
  rcases le_total x y with hxy | hxy
  · have h1 : y ∈ Set.Ico x (x+p) := by simp only [Set.mem_Ico]; omega
    have h2 : y ∈ Set.Ico y (y+q) := by simp only [Set.mem_Ico]; omega
    exact h h1 h2
  · have h1 : x ∈ Set.Ico x (x+p) := by simp only [Set.mem_Ico]; omega
    have h2 : x ∈ Set.Ico y (y+q) := by simp only [Set.mem_Ico]; omega
    exact h h1 h2

lemma sum_get_eq (a : List ℕ) : ∑ j : Fin a.length, a.get j = a.sum := by
  simpa using (List.sum_ofFn (f := a.get))

lemma sum_compl_get (a : List ℕ) (S : Finset (Fin a.length)) :
    ∑ j ∈ Sᶜ, a.get j + ∑ j ∈ S, a.get j = a.sum := by
  rw [Finset.sum_compl_add_sum]; exact sum_get_eq a

lemma sum_id_aux {t : ℕ} (p : Fin t → ℕ) (g : Fin t → ℕ) (hg : Function.Injective g) :
    2 * ∑ j, p j * ∑ k ∈ univ.filter (fun k => g k ≤ g j), p k =
      (∑ j, p j)^2 + ∑ j, p j * p j := by
  have e1 : ∀ j, p j * ∑ k ∈ univ.filter (fun k => g k ≤ g j), p k
      = ∑ k, (if g k ≤ g j then p j * p k else 0) := by
    intro j
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    split_ifs <;> simp
  simp only [e1]
  have key : ∀ j k : Fin t, (if g k ≤ g j then p j * p k else 0) + (if g j ≤ g k then p k * p j else 0)
      = p j * p k + (if j = k then p j * p k else 0) := by
    intro j k
    by_cases h : j = k
    · subst h; simp
    · have hne : g j ≠ g k := fun h' => h (hg h')
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have : ¬ g k ≤ g j := by omega
        simp [this, h1.le, h, mul_comm]
      · have : ¬ g j ≤ g k := by omega
        simp [this, h1.le, h, mul_comm]
  have hswap : ∑ j, ∑ k, (if g k ≤ g j then p j * p k else 0)
      = ∑ j, ∑ k, (if g j ≤ g k then p k * p j else 0) := by
    rw [Finset.sum_comm]
  rw [two_mul]
  nth_rewrite 2 [hswap]
  rw [← Finset.sum_add_distrib]
  have : ∀ j, ∑ k, (if g k ≤ g j then p j * p k else 0) + ∑ k, (if g j ≤ g k then p k * p j else 0)
      = ∑ k, (p j * p k + (if j = k then p j * p k else 0)) := by
    intro j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; exact key j k
  simp only [this]
  simp only [Finset.sum_add_distrib]
  rw [sq, Finset.sum_mul_sum]
  simp

lemma sum_id {t : ℕ} (p : Fin t → ℕ) (g : Fin t → ℕ) (hg : Function.Injective g) :
    ∑ j, p j * ∑ k ∈ univ.filter (fun k => g k ≤ g j), p k
      = ∑ k : Fin t, ∑ j ∈ Finset.Iic k, p j * p k := by
  have h1 := sum_id_aux p g hg
  have h2 := sum_id_aux p (fun j : Fin t => (j : ℕ)) Fin.val_injective
  have hf : ∀ j : Fin t, univ.filter (fun k : Fin t => (k : ℕ) ≤ (j : ℕ)) = Finset.Iic j := by
    intro j; refine Finset.ext (fun k => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    exact Fin.le_def.symm
  have h3 : ∑ j, p j * ∑ k ∈ univ.filter (fun k : Fin t => (k : ℕ) ≤ (j : ℕ)), p k
      = ∑ k : Fin t, ∑ j ∈ Finset.Iic k, p j * p k := by
    simp only [hf, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  omega

lemma prefix_le {n : ℕ} (p B : Fin n → ℕ) (hp : ∀ j, 0 < p j)
    (hsep : ∀ j k, j ≠ k → B j + p j ≤ B k ∨ B k + p k ≤ B j) (j : Fin n) :
    ∑ k ∈ univ.filter (fun k => B k ≤ B j), p k ≤ B j + p j := by
  let I : Fin n → Finset ℕ := fun k => Finset.Ico (B k) (B k + p k)
  have hdisj : ∀ x ∈ univ.filter (fun k => B k ≤ B j), ∀ y ∈ univ.filter (fun k => B k ≤ B j),
      x ≠ y → Disjoint (I x) (I y) := fun x _ y _ hxy => ico_fdisj (hsep x y hxy)
  have hcard := Finset.card_biUnion hdisj
  simp only [I, Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  have hsub : (univ.filter (fun k => B k ≤ B j)).biUnion I ⊆ Finset.range (B j + p j) := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨k, hk, hz⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [I, Finset.mem_Ico] at hz
    simp only [Finset.mem_range]
    by_cases hkj : k = j
    · subst hkj; omega
    · have := hsep k j hkj
      have := hp j
      omega
  have h2 := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at h2
  exact h2

lemma sum_range_le {n : ℕ} (p B : Fin n → ℕ) (T : Finset (Fin n)) (N : ℕ)
    (hsep : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → B j + p j ≤ B k ∨ B k + p k ≤ B j)
    (hN : ∀ j ∈ T, B j + p j ≤ N) : ∑ k ∈ T, p k ≤ N := by
  let I : Fin n → Finset ℕ := fun k => Finset.Ico (B k) (B k + p k)
  have hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (I x) (I y) :=
    fun x hx y hy hxy => ico_fdisj (hsep x hx y hy hxy)
  have hcard := Finset.card_biUnion hdisj
  simp only [I, Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  have hsub : T.biUnion I ⊆ Finset.range N := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨k, hk, hz⟩ := hz
    simp only [I, Finset.mem_Ico] at hz
    simp only [Finset.mem_range]
    have := hN k hk
    omega
  have h2 := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at h2
  exact h2

lemma b_backward (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hbA : b < a.sum)
    (B : Fin (a.length + 1) → ℕ) (hf : (instB a b).IsFeasible B)
    (hd : ∀ j, (instB a b).C B j ≤ (instB a b).d j)
    (hl : (instB a b).sumWC B ≤ yB a b) : KnapsackYes a b := by
  have hpos : ∀ j : Fin a.length, 0 < a.get j := fun j => ha _ (List.get_mem _ _)
  have hdl := hd (Fin.last _)
  simp only [Instance.C, instB, Fin.lastCases_last] at hdl
  -- separation of all pairs
  let pB : Fin (a.length + 1) → ℕ := fun i => Fin.lastCases (motive := fun _ => ℕ) 1 (fun j => a.get j) i
  have pB_last : pB (Fin.last _) = 1 := by simp [pB]
  have pB_cast : ∀ j : Fin a.length, pB j.castSucc = a.get j := by intro j; simp [pB]
  have hpos' : ∀ j : Fin (a.length + 1), 0 < pB j := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [pB_last]; norm_num
    | cast j => rw [pB_cast]; exact hpos j
  have hf2 : ∀ j k : Fin (a.length + 1), j ≠ k →
      Disjoint (Set.Ico (B j) (B j + pB j)) (Set.Ico (B k) (B k + pB k)) := hf.2
  have hsep' : ∀ j k : Fin (a.length + 1), j ≠ k →
      B j + pB j ≤ B k ∨ B k + pB k ≤ B j := fun j k hjk =>
    sep_of_sdisj (hpos' j) (hpos' k) (hf2 j k hjk)
  have hsep : ∀ j k : Fin a.length, j ≠ k →
      B j.castSucc + a.get j ≤ B k.castSucc ∨ B k.castSucc + a.get k ≤ B j.castSucc := by
    intro j k hjk
    have := hsep' j.castSucc k.castSucc (fun h => hjk (Fin.castSucc_injective _ h))
    rwa [pB_cast, pB_cast] at this
  have hsepl : ∀ j : Fin a.length, B j.castSucc + a.get j ≤ B (Fin.last _) ∨
      B (Fin.last _) + 1 ≤ B j.castSucc := by
    intro j
    have := hsep' j.castSucc (Fin.last _) (Fin.castSucc_lt_last j).ne
    rwa [pB_cast, pB_last] at this
  have hBl_le : B (Fin.last a.length) ≤ b := by omega
  let B' : Fin a.length → ℕ := fun j => B j.castSucc
  have hinj : Function.Injective B' := by
    intro j k h
    by_contra hjk
    have := hsep j k hjk
    have := hpos j; have := hpos k
    simp only [B'] at h
    omega
  -- prefix bound
  have hpre : ∀ j : Fin a.length, (∑ k ∈ univ.filter (fun k : Fin a.length => B' k ≤ B' j), a.get k)
      + (if B (Fin.last a.length) ≤ B' j then 1 else 0) ≤ B' j + a.get j := by
    intro j
    have h : ∑ k ∈ univ.filter (fun k : Fin (a.length + 1) => B k ≤ B j.castSucc), pB k
        ≤ B j.castSucc + pB j.castSucc :=
      prefix_le pB B hpos' hsep' j.castSucc
    rw [Finset.sum_filter, Fin.sum_univ_castSucc] at h
    simp only [pB_last, pB_cast] at h
    rw [← Finset.sum_filter] at h
    simp only [B'] 
    by_cases hle : B (Fin.last a.length) ≤ B j.castSucc
    · simp only [hle, if_true] at h ⊢; omega
    · simp only [hle, if_false] at h ⊢; omega
  have hsum : (instB a b).sumWC B = ∑ j : Fin a.length, a.get j * (B j.castSucc + a.get j) := by
    unfold Instance.sumWC
    show ∑ j : Fin (a.length + 1), (instB a b).w j * (instB a b).C B j = _
    rw [Fin.sum_univ_castSucc]
    simp [instB, Instance.C]
  have hlow : ∑ j : Fin a.length, a.get j *
      ((∑ k ∈ univ.filter (fun k : Fin a.length => B' k ≤ B' j), a.get k)
        + (if B (Fin.last a.length) ≤ B' j then 1 else 0)) ≤ (instB a b).sumWC B := by
    rw [hsum]
    apply Finset.sum_le_sum
    intro j _
    apply Nat.mul_le_mul_left
    have := hpre j
    simp only [B'] at this ⊢
    omega
  have hid := sum_id a.get B' hinj
  have hexp : ∑ j : Fin a.length, a.get j *
      ((∑ k ∈ univ.filter (fun k : Fin a.length => B' k ≤ B' j), a.get k)
        + (if B (Fin.last a.length) ≤ B' j then 1 else 0))
      = (∑ k : Fin a.length, ∑ j ∈ Finset.Iic k, a.get j * a.get k)
        + ∑ j ∈ univ.filter (fun j : Fin a.length => B (Fin.last a.length) ≤ B' j), a.get j := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hid, Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> simp
  obtain ⟨Q, hQd⟩ : ∃ Q : Finset (Fin a.length), Q = univ.filter (fun j => B (Fin.last a.length) ≤ B' j) := ⟨_, rfl⟩
  have hQ : ∑ j ∈ Q, a.get j ≤ a.sum - b := by
    have h1 := hlow
    rw [hexp, ← hQd] at h1
    unfold yB at hl
    omega
  have hR : ∑ j ∈ Qᶜ, a.get j ≤ B (Fin.last a.length) := by
    apply sum_range_le a.get B' Qᶜ
    · intro j _ k _ hjk; exact hsep j k hjk
    · intro j hj
      have h1 : ¬ B (Fin.last a.length) ≤ B' j := by simpa [hQd] using hj
      have h2 := hsepl j
      simp only [B'] at h1 h2 ⊢
      omega
  have hc := sum_compl_get a Q
  exact ⟨Qᶜ, by omega⟩
/-- start times of the forward schedule for (c) -/
def cfB (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) : Fin (a.length + 1) → ℕ :=
  fun i => Fin.lastCases (motive := fun _ => ℕ) b
    (fun j => if j ∈ S then spos a.get S j else b + 1 + spos a.get Sᶜ j) i

lemma cfB_last (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) : cfB a b S (Fin.last _) = b := by
  simp [cfB]

lemma cfB_cast (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (j : Fin a.length) :
    cfB a b S j.castSucc = if j ∈ S then spos a.get S j else b + 1 + spos a.get Sᶜ j := by
  simp [cfB]

lemma cfB_sep (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (j k : Fin a.length) (hjk : j < k) :
    cfB a b S j.castSucc + a.get j ≤ cfB a b S k.castSucc ∨
      cfB a b S k.castSucc + a.get k ≤ cfB a b S j.castSucc := by
  rw [cfB_cast, cfB_cast]
  by_cases hj : j ∈ S <;> by_cases hk : k ∈ S
  · simp only [hj, hk, if_true]; left; exact spos_step _ _ hjk hj
  · simp only [hj, hk, if_true, if_false]
    have := spos_add_le a.get S hj
    left; omega
  · simp only [hj, hk, if_true, if_false]
    have := spos_add_le a.get S hk
    right; omega
  · simp only [hj, hk, if_false]
    have := spos_step a.get Sᶜ hjk (by simpa using hj)
    left; omega

lemma cfB_le (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (j : Fin a.length) :
    cfB a b S j.castSucc + a.get j ≤ (if j ∈ S then b else a.sum + 1) := by
  rw [cfB_cast]
  have hc := sum_compl_get a S
  by_cases hj : j ∈ S
  · simp only [hj, if_true]; have := spos_add_le a.get S hj; omega
  · simp only [hj, if_false]
    have := spos_add_le a.get Sᶜ (by simpa using hj)
    omega

lemma cfB_side (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (k : Fin a.length) :
    cfB a b S k.castSucc + a.get k ≤ b ∨ b + 1 ≤ cfB a b S k.castSucc := by
  have h1 := cfB_le a b S hS k
  by_cases hk : k ∈ S
  · simp only [hk, if_true] at h1; left; exact h1
  · right; rw [cfB_cast]; simp only [hk, if_false]; omega


lemma cfB_mono (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (j k : Fin a.length) (hjk : j < k) (hsame : j ∈ S ↔ k ∈ S) :
    cfB a b S j.castSucc + a.get j ≤ cfB a b S k.castSucc := by
  rw [cfB_cast, cfB_cast]
  by_cases hj : j ∈ S
  · have hk : k ∈ S := hsame.1 hj
    simp only [hj, hk, if_true]; exact spos_step _ _ hjk hj
  · have hk : k ∉ S := fun h => hj (hsame.2 h)
    simp only [hj, hk, if_false]
    have := spos_step a.get Sᶜ hjk (by simpa using hj)
    omega

lemma sum_filter_le {t : ℕ} (p : Fin t → ℕ) (T : Finset (Fin t)) {j : Fin t} (hj : j ∈ T) :
    ∑ k ∈ T.filter (· ≤ j), p k = spos p T j + p j := by
  have h : T.filter (· ≤ j) = insert j (T.filter (· < j)) := by
    refine Finset.ext (fun x => ?_)
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxj⟩
      rcases hxj.lt_or_eq with h | h
      · right; exact ⟨hx, h⟩
      · left; exact h
    · rintro (rfl | ⟨hx, hxj⟩)
      · exact ⟨hj, le_rfl⟩
      · exact ⟨hx, hxj.le⟩
  rw [h, Finset.sum_insert (by simp), add_comm]
  rfl

lemma cfB_in (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    {j : Fin a.length} (hj : j ∈ S) : cfB a b S j.castSucc + a.get j ≤ b := by
  have := cfB_le a b S hS j
  simpa [hj] using this

lemma cfB_out (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length))
    {j : Fin a.length} (hj : j ∉ S) : b + 1 ≤ cfB a b S j.castSucc := by
  rw [cfB_cast]; simp only [hj, if_false]; omega

lemma cfB_same (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (ha : ∀ v ∈ a, 0 < v) (k j : Fin a.length) (hsame : k ∈ S ↔ j ∈ S) :
    cfB a b S k.castSucc ≤ cfB a b S j.castSucc ↔ k ≤ j := by
  have hpos : ∀ j : Fin a.length, 0 < a.get j := fun j => ha _ (List.get_mem _ _)
  constructor
  · intro h
    by_contra hc
    have hlt : j < k := lt_of_not_ge hc
    have := cfB_mono a b S hS j k hlt hsame.symm
    have := hpos j
    omega
  · intro h
    rcases h.lt_or_eq with h | h
    · have := cfB_mono a b S hS k j h hsame
      have := hpos k
      omega
    · rw [h]

lemma cfB_le_iff (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (ha : ∀ v ∈ a, 0 < v) (k j : Fin a.length) :
    cfB a b S k.castSucc ≤ cfB a b S j.castSucc ↔
      ((k ∈ S ∧ j ∉ S) ∨ ((k ∈ S ↔ j ∈ S) ∧ k ≤ j)) := by
  have hpos : ∀ j : Fin a.length, 0 < a.get j := fun j => ha _ (List.get_mem _ _)
  by_cases hk : k ∈ S <;> by_cases hj : j ∈ S
  · have hsame : k ∈ S ↔ j ∈ S := by simp [hk, hj]
    rw [cfB_same a b S hS ha k j hsame]
    constructor
    · intro h; exact Or.inr ⟨hsame, h⟩
    · rintro (⟨_, h2⟩ | ⟨_, h2⟩)
      · exact absurd hj h2
      · exact h2
  · have h1 := cfB_in a b S hS hk
    have h2 := cfB_out a b S hj
    constructor
    · intro _; exact Or.inl ⟨hk, hj⟩
    · intro _; omega
  · have h1 := cfB_in a b S hS hj
    have h2 := cfB_out a b S hk
    have := hpos j
    constructor
    · intro h; omega
    · rintro (⟨h3, _⟩ | ⟨h3, _⟩)
      · exact absurd h3 hk
      · exact absurd (h3.2 hj) hk
  · have hsame : k ∈ S ↔ j ∈ S := by simp [hk, hj]
    rw [cfB_same a b S hS ha k j hsame]
    constructor
    · intro h; exact Or.inr ⟨hsame, h⟩
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact absurd h1 hk
      · exact h2

lemma cfB_S0 (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b)
    (ha : ∀ v ∈ a, 0 < v) (j : Fin a.length) :
    cfB a b S j.castSucc + a.get j =
      (∑ k ∈ univ.filter (fun k : Fin a.length => cfB a b S k.castSucc ≤ cfB a b S j.castSucc),
        a.get k) + (if j ∈ Sᶜ then 1 else 0) := by
  rw [Finset.sum_filter, ← Finset.sum_compl_add_sum S]
  by_cases hj : j ∈ S
  · have hjc : j ∉ Sᶜ := by simpa using hj
    have h1 : ∑ k ∈ Sᶜ, (if cfB a b S k.castSucc ≤ cfB a b S j.castSucc then a.get k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k ∉ S := by simpa using hk
      rw [if_neg]
      rw [cfB_le_iff a b S hS ha]
      rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hk' h
      · exact hk' (h.2 hj)
    have h2 : ∑ k ∈ S, (if cfB a b S k.castSucc ≤ cfB a b S j.castSucc then a.get k else 0)
        = ∑ k ∈ S.filter (· ≤ j), a.get k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      have : cfB a b S k.castSucc ≤ cfB a b S j.castSucc ↔ k ≤ j :=
        cfB_same a b S hS ha k j (by simp [hk, hj])
      simp only [this]
    rw [h1, h2, sum_filter_le a.get S hj, cfB_cast]
    simp [hj, hjc]
  · have hjc : j ∈ Sᶜ := by simpa using hj
    have h2 : ∑ k ∈ S, (if cfB a b S k.castSucc ≤ cfB a b S j.castSucc then a.get k else 0)
        = ∑ k ∈ S, a.get k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos]
      rw [cfB_le_iff a b S hS ha]
      exact Or.inl ⟨hk, hj⟩
    have h1 : ∑ k ∈ Sᶜ, (if cfB a b S k.castSucc ≤ cfB a b S j.castSucc then a.get k else 0)
        = ∑ k ∈ Sᶜ.filter (· ≤ j), a.get k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ∉ S := by simpa using hk
      have : cfB a b S k.castSucc ≤ cfB a b S j.castSucc ↔ k ≤ j :=
        cfB_same a b S hS ha k j (by simp [hk', hj])
      simp only [this]
    rw [h1, h2, sum_filter_le a.get Sᶜ hjc, cfB_cast, hS]
    simp [hj, hjc]
    omega

lemma b_forward (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hbA : b < a.sum)
    (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b) :
    (instB a b).IsFeasible (cfB a b S) ∧ (∀ j, (instB a b).C (cfB a b S) j ≤ (instB a b).d j) ∧
      (instB a b).sumWC (cfB a b S) ≤ yB a b := by
  have hc := sum_compl_get a S
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro j; simp [instB]
  · intro j k hjk
    induction j using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => exact absurd rfl hjk
      | cast k =>
        simp only [instB, Fin.lastCases_last, Fin.lastCases_castSucc, cfB_last]
        apply ico_sdisj
        have := cfB_side a b S hS k
        omega
    | cast j =>
      induction k using Fin.lastCases with
      | last =>
        simp only [instB, Fin.lastCases_last, Fin.lastCases_castSucc, cfB_last]
        apply ico_sdisj
        have := cfB_side a b S hS j
        omega
      | cast k =>
        have hne : j ≠ k := fun h => hjk (by rw [h])
        simp only [instB, Fin.lastCases_castSucc]
        apply ico_sdisj
        rcases lt_or_gt_of_ne hne with h | h
        · exact cfB_sep a b S hS j k h
        · exact (cfB_sep a b S hS k j h).symm
  · intro j
    induction j using Fin.lastCases with
    | last => simp [Instance.C, instB, cfB_last]
    | cast j =>
      have h1 := cfB_le a b S hS j
      simp only [Instance.C, instB, Fin.lastCases_castSucc]
      have : (if j ∈ S then b else a.sum + 1) ≤ a.sum + 1 := by split_ifs <;> omega
      omega
  · have hsum : (instB a b).sumWC (cfB a b S)
        = ∑ j : Fin a.length, a.get j * (cfB a b S j.castSucc + a.get j) := by
      unfold Instance.sumWC
      show ∑ j : Fin (a.length + 1), (instB a b).w j * (instB a b).C (cfB a b S) j = _
      rw [Fin.sum_univ_castSucc]
      simp [instB, Instance.C]
    have hinj : Function.Injective (fun j : Fin a.length => cfB a b S j.castSucc) := by
      intro j k h
      by_contra hjk
      have h1 : cfB a b S j.castSucc ≤ cfB a b S k.castSucc := le_of_eq h
      have h2 : cfB a b S k.castSucc ≤ cfB a b S j.castSucc := le_of_eq h.symm
      rw [cfB_le_iff a b S hS ha] at h1 h2
      apply hjk
      rcases h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases h2 with ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exact absurd h5 h4
      · exact absurd (h5.2 h3) h4
      · exact absurd (h3.2 h5) h6
      · exact le_antisymm h4 h6
    have hid := sum_id a.get (fun j : Fin a.length => cfB a b S j.castSucc) hinj
    rw [hsum]
    have h1 : ∑ j : Fin a.length, a.get j * (cfB a b S j.castSucc + a.get j)
        = ∑ j : Fin a.length, a.get j *
          ((∑ k ∈ univ.filter (fun k : Fin a.length => cfB a b S k.castSucc ≤ cfB a b S j.castSucc),
            a.get k) + (if j ∈ Sᶜ then 1 else 0)) := by
      apply Finset.sum_congr rfl; intro j _
      rw [cfB_S0 a b S hS ha j]
    rw [h1]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hid]
    have h2 : ∑ j : Fin a.length, a.get j * (if j ∈ Sᶜ then 1 else 0) = ∑ j ∈ Sᶜ, a.get j := by
      have h3 : ∀ j : Fin a.length, a.get j * (if j ∈ Sᶜ then 1 else 0)
          = if j ∈ Sᶜ then a.get j else 0 := by intro j; split_ifs <;> simp
      simp only [h3]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      refine Finset.ext (fun x => ?_)
      simp
    rw [h2]
    unfold yB
    omega

theorem b_core (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
        (instB a b).sumWC B ≤ yB a b := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨_, b_forward a b ha hbA S hS⟩
  · rintro ⟨B, hf, hd, hl⟩
    exact b_backward a b ha hbA B hf hd hl

end SchedComplexity.OneMachine

open SchedComplexity.OneMachine


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
        (instB a b).sumWC B ≤ yB a b := by
  exact b_core a b ha hb hbA
