-- Prove2me | solution 1 for SchedComplexity.Shops.theorem_4i_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:59:10.588306+00:00
-- url     : https://prove2.me/submissions/ae58781a-e685-4420-b503-857d9f40bd6a

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions



namespace SchedComplexity.Shops
open Finset

lemma sh_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (st len : ι → ℕ) (lo hi : ℕ)
    (hsub : ∀ i ∈ s, lo ≤ st i ∧ st i + len i ≤ hi)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → st i + len i ≤ st j ∨ st j + len j ≤ st i) :
    ∑ i ∈ s, len i ≤ hi - lo := by
  have h1 : (s.biUnion fun i => Finset.Ico (st i) (st i + len i)).card = ∑ i ∈ s, len i := by
    rw [Finset.card_biUnion]
    · simp
    · intro i hi j hj hij
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Ico] at hx hx'
      rcases hdisj i hi j hj hij with h | h <;> omega
  have h2 : (s.biUnion fun i => Finset.Ico (st i) (st i + len i)) ⊆ Finset.Ico lo hi := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_Ico] at hx ⊢
    obtain ⟨i, hi, h1, h2⟩ := hx
    have := hsub i hi; omega
  have := Finset.card_le_card h2
  simp at this; omega

lemma sh_get_of_eq {α : Type*} {L1 L2 : List α} (h : L1 = L2) (r : Fin L1.length)
    (hr : r.val < L2.length) : L1.get r = L2[r.val] := by
  subst h; simp

lemma sh_sum_get (a : List ℕ) : ∑ j : Fin a.length, a.get j = a.sum := by
  simpa using Fin.sum_univ_getElem a

def shPre (a : List ℕ) (T : Finset (Fin a.length)) (j : Fin a.length) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∈ T), a.get i

lemma shPre_step (a : List ℕ) (T : Finset (Fin a.length)) (i j : Fin a.length) (hij : i < j)
    (hi : i ∈ T) : shPre a T i + a.get i ≤ shPre a T j := by
  unfold shPre
  have : insert i (Finset.univ.filter (fun k => k < i ∧ k ∈ T)) ⊆
      Finset.univ.filter (fun k => k < j ∧ k ∈ T) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | ⟨h1, h2⟩
    · exact ⟨hij, hi⟩
    · exact ⟨lt_trans h1 hij, h2⟩
  have h2 := Finset.sum_le_sum_of_subset (f := fun k => a.get k) this
  rw [Finset.sum_insert (by simp)] at h2
  linarith

lemma shPre_le (a : List ℕ) (T : Finset (Fin a.length)) (j : Fin a.length) (hj : j ∈ T) :
    shPre a T j + a.get j ≤ ∑ i ∈ T, a.get i := by
  unfold shPre
  have : insert j (Finset.univ.filter (fun k => k < j ∧ k ∈ T)) ⊆ T := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hk with rfl | ⟨h1, h2⟩
    · exact hj
    · exact h2
  have h2 := Finset.sum_le_sum_of_subset (f := fun k => a.get k) this
  rw [Finset.sum_insert (by simp)] at h2
  linarith

lemma sh_le_completion {n m : ℕ} (I : ShopInstance n m) (S : I.Op → ℕ) (o : I.Op) :
    S o + I.proc o ≤ I.completion S o.1 := by
  unfold ShopInstance.completion
  exact Finset.le_sup (f := fun r : Fin (I.ops o.1).length => S ⟨o.1, r⟩ + I.proc ⟨o.1, r⟩)
    (Finset.mem_univ o.2)

lemma sh_completion_le {n m : ℕ} (I : ShopInstance n m) (S : I.Op → ℕ) (j : Fin n) (y : ℕ)
    (h : ∀ r : Fin (I.ops j).length, S ⟨j, r⟩ + I.proc ⟨j, r⟩ ≤ y) : I.completion S j ≤ y := by
  unfold ShopInstance.completion
  exact Finset.sup_le (fun r _ => h r)

def Ilp (a : List ℕ) (b k : ℕ) : ℕ := if k = 0 then b else if k = 1 then 1 else a.sum - b
def Ilm (k : ℕ) : Fin 2 := if k = 1 then 0 else 1

lemma I_len_item (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) (hj : j.val < a.length) :
    ((constrI a b).ops j).length = 1 := by simp [constrI, hj]

lemma I_len_last (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) (hj : ¬ j.val < a.length) :
    ((constrI a b).ops j).length = 3 := by simp [constrI, hj]

lemma I_item_pm (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) (hj : j.val < a.length)
    (r : Fin ((constrI a b).ops j).length) :
    (constrI a b).proc ⟨j,r⟩ = a.get ⟨j.val,hj⟩ ∧ (constrI a b).mach ⟨j,r⟩ = 0 := by
  have hL : (constrI a b).ops j = [(0, a.get ⟨j.val,hj⟩)] := by simp [constrI, hj]
  have hr : r.val < 1 := by have := r.isLt; have hl := I_len_item a b j hj; omega
  have h1 := sh_get_of_eq hL r (by simpa using hr)
  have h0 : r.val = 0 := by omega
  simp only [ShopInstance.proc, ShopInstance.mach, h1, h0]; simp

lemma I_last_pm (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) (hj : ¬ j.val < a.length)
    (r : Fin ((constrI a b).ops j).length) :
    r.val < 3 ∧ (constrI a b).proc ⟨j,r⟩ = Ilp a b r.val ∧ (constrI a b).mach ⟨j,r⟩ = Ilm r.val := by
  have hL : (constrI a b).ops j = [(1, b), (0, 1), (1, a.sum - b)] := by simp [constrI, hj]
  have hr : r.val < 3 := by have := r.isLt; have hl := I_len_last a b j hj; omega
  have h1 := sh_get_of_eq hL r (by simp; omega)
  refine ⟨hr, ?_⟩
  have : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  rcases this with h | h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
    simp [Ilp, Ilm]

def Isched (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (j : Fin (a.length+1)) (r : ℕ) : ℕ :=
  if h : j.val < a.length then
    (if (⟨j.val, h⟩ : Fin a.length) ∈ S then shPre a S ⟨j.val, h⟩
     else b + 1 + shPre a Sᶜ ⟨j.val, h⟩)
  else (if r = 0 then 0 else if r = 1 then b else b + 1)

lemma I_rev (a : List ℕ) (b : ℕ) (hbA : b < a.sum) (S : Finset (Fin a.length))
    (hS : ∑ j ∈ S, a.get j = b) : (constrI a b).HasScheduleLE (yI a) := by
  classical
  have hA := sh_sum_get a
  have hSc : ∑ j ∈ Sᶜ, a.get j = a.sum - b := by
    have := Finset.sum_compl_add_sum S (fun j => a.get j)
    omega
  have hin : ∀ j : Fin a.length, j ∈ S → shPre a S j + a.get j ≤ b := by
    intro j hj; have := shPre_le a S j hj; omega
  have hout : ∀ j : Fin a.length, j ∉ S → shPre a Sᶜ j + a.get j ≤ a.sum - b := by
    intro j hj; have := shPre_le a Sᶜ j (by simpa using hj); omega
  refine ⟨fun o => Isched a b S o.1 o.2.val, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o; simp [constrI]
  · intro j r r' hrr
    by_cases hj : j.val < a.length
    · have := r'.isLt
      have hl := I_len_item a b j hj
      omega
    · obtain ⟨hr3, hp, -⟩ := I_last_pm a b j hj r
      simp only [hp, Isched, dif_neg hj, hrr]
      have h5 := r'.isLt
      have h6 := I_len_last a b j hj
      have : r.val = 0 ∨ r.val = 1 := by omega
      rcases this with h | h <;> simp [h, Ilp] <;> omega
  · intro o o' hne hm
    rcases o with ⟨j, r⟩
    rcases o' with ⟨j', r'⟩
    by_cases hj : j.val < a.length <;> by_cases hj' : j'.val < a.length
    · obtain ⟨hp, hmm⟩ := I_item_pm a b j hj r
      obtain ⟨hp', hmm'⟩ := I_item_pm a b j' hj' r'
      have hjj : j ≠ j' := by
        rintro rfl
        have h1 := r.isLt
        have h2 := r'.isLt
        have hl := I_len_item a b j hj
        have : r = r' := Fin.ext (by omega)
        subst this; exact hne rfl
      have hjj' : (⟨j.val, hj⟩ : Fin a.length) ≠ ⟨j'.val, hj'⟩ := by
        intro h; apply hjj; exact Fin.ext (by simpa using congrArg Fin.val h)
      simp only [hp, hp', Isched, dif_pos hj, dif_pos hj']
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
        by_cases h2 : (⟨j'.val, hj'⟩ : Fin a.length) ∈ S <;> simp only [h1, h2, if_true, if_false]
      · rcases lt_or_gt_of_ne hjj' with h | h
        · left; exact shPre_step a S _ _ h h1
        · right; exact shPre_step a S _ _ h h2
      · left; have := hin _ h1; omega
      · right; have := hin _ h2; omega
      · rcases lt_or_gt_of_ne hjj' with h | h
        · left; have := shPre_step a Sᶜ _ _ h (by simpa using h1); omega
        · right; have := shPre_step a Sᶜ _ _ h (by simpa using h2); omega
    · obtain ⟨hp, hmm⟩ := I_item_pm a b j hj r
      obtain ⟨hr3, hp', hmm'⟩ := I_last_pm a b j' hj' r'
      have : r'.val = 0 ∨ r'.val = 1 ∨ r'.val = 2 := by omega
      simp only [hp, hp', Isched, dif_pos hj, dif_neg hj']
      rw [hmm, hmm'] at hm
      rcases this with h | h | h <;> simp [h, Ilm, Ilp] at hm ⊢
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S
      · left; simp only [h1, if_true]; have := hin _ h1; omega
      · right; simp only [h1, if_false]; omega
    · obtain ⟨hp, hmm⟩ := I_item_pm a b j' hj' r'
      obtain ⟨hr3, hp', hmm'⟩ := I_last_pm a b j hj r
      have : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
      simp only [hp, hp', Isched, dif_pos hj', dif_neg hj]
      rw [hmm, hmm'] at hm
      rcases this with h | h | h <;> simp [h, Ilm, Ilp] at hm ⊢
      by_cases h1 : (⟨j'.val, hj'⟩ : Fin a.length) ∈ S
      · right; simp only [h1, if_true]; have := hin _ h1; omega
      · left; simp only [h1, if_false]; omega
    · obtain ⟨hr3, hp, hmm⟩ := I_last_pm a b j hj r
      obtain ⟨hr3', hp', hmm'⟩ := I_last_pm a b j' hj' r'
      have hjj : j = j' := by
        apply Fin.ext; have := j.isLt; have := j'.isLt; omega
      subst hjj
      have hrr : r.val ≠ r'.val := by
        intro h; have : r = r' := Fin.ext h
        subst this; exact hne rfl
      simp only [hp, hp', Isched, dif_neg hj]
      rw [hmm, hmm'] at hm
      have h3 : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
      have h3' : r'.val = 0 ∨ r'.val = 1 ∨ r'.val = 2 := by omega
      rcases h3 with h | h | h <;> rcases h3' with h' | h' | h' <;>
        simp [h, h', Ilm, Ilp] at hm hrr ⊢ <;> omega
  · intro j k hjk; simp [constrI] at hjk
  · intro j
    apply sh_completion_le
    intro r
    by_cases hj : j.val < a.length
    · obtain ⟨hp, -⟩ := I_item_pm a b j hj r
      simp only [hp, Isched, dif_pos hj, yI]
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S
      · simp only [h1, if_true]; have := hin _ h1; omega
      · simp only [h1, if_false]; have := hout _ h1; omega
    · obtain ⟨hr3, hp, -⟩ := I_last_pm a b j hj r
      simp only [hp, Isched, dif_neg hj, yI]
      have : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
      rcases this with h | h | h <;> simp [h, Ilp] <;> omega


def Ilast (a : List ℕ) (b : ℕ) (k : Fin 3) : (constrI a b).Op :=
  ⟨Fin.last a.length, ⟨k.val, by rw [I_len_last a b _ (by simp)]; exact k.isLt⟩⟩

def Iitem (a : List ℕ) (b : ℕ) (j : Fin a.length) : (constrI a b).Op :=
  ⟨⟨j.val, by omega⟩, ⟨0, by rw [I_len_item a b ⟨j.val, by omega⟩ j.isLt]; omega⟩⟩

lemma I_fwd (a : List ℕ) (b : ℕ) (hbA : b < a.sum)
    (h : (constrI a b).HasScheduleLE (yI a)) : SchedComplexity.OneMachine.KnapsackYes a b := by
  classical
  obtain ⟨S0, ⟨-, hchain, hmach, -⟩, hC⟩ := h
  have hA := sh_sum_get a
  have pL : ∀ k : Fin 3, (constrI a b).proc (Ilast a b k) = Ilp a b k.val ∧
      (constrI a b).mach (Ilast a b k) = Ilm k.val := fun k =>
    (I_last_pm a b (Fin.last a.length) (by simp) _).2
  have pI : ∀ j : Fin a.length, (constrI a b).proc (Iitem a b j) = a.get j ∧
      (constrI a b).mach (Iitem a b j) = 0 := fun j =>
    I_item_pm a b ⟨j.val, by omega⟩ j.isLt _
  have c1 : S0 (Ilast a b 0) + (constrI a b).proc (Ilast a b 0) ≤ S0 (Ilast a b 1) :=
    hchain (Fin.last a.length) (Ilast a b 0).2 (Ilast a b 1).2 (by simp [Ilast])
  have c2 : S0 (Ilast a b 1) + (constrI a b).proc (Ilast a b 1) ≤ S0 (Ilast a b 2) :=
    hchain (Fin.last a.length) (Ilast a b 1).2 (Ilast a b 2).2 (by simp [Ilast])
  have e2 := sh_le_completion _ S0 (Ilast a b 2)
  have e2' : (constrI a b).completion S0 (Ilast a b 2).1 ≤ yI a := hC (Fin.last a.length)
  have q0 : (constrI a b).proc (Ilast a b 0) = b := by simpa [Ilp] using (pL 0).1
  have q1 : (constrI a b).proc (Ilast a b 1) = 1 := by simpa [Ilp] using (pL 1).1
  have q2 : (constrI a b).proc (Ilast a b 2) = a.sum - b := by simpa [Ilp] using (pL 2).1
  rw [q0] at c1
  rw [q1] at c2
  rw [q2] at e2
  have hs : S0 (Ilast a b 1) = b := by
    unfold yI at e2'
    omega
  have hItem : ∀ j : Fin a.length, S0 (Iitem a b j) + a.get j ≤ yI a := by
    intro j
    have := sh_le_completion _ S0 (Iitem a b j)
    have h2 := hC (Iitem a b j).1
    rw [(pI j).1] at this
    exact le_trans this h2
  have hL1 : ∀ j : Fin a.length, S0 (Iitem a b j) + a.get j ≤ b ∨ b + 1 ≤ S0 (Iitem a b j) := by
    intro j
    have hne : Iitem a b j ≠ Ilast a b 1 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Iitem, Ilast] at this
      have := j.isLt; omega
    have := hmach _ _ hne (by rw [(pI j).2, (pL 1).2]; simp [Ilm])
    rw [(pI j).1, (pL 1).1] at this
    simp only [Ilp, Ilm] at this
    simp at this
    simp only [List.get_eq_getElem] at this ⊢
    omega
  have hLL : ∀ j k : Fin a.length, j ≠ k → S0 (Iitem a b j) + a.get j ≤ S0 (Iitem a b k) ∨
      S0 (Iitem a b k) + a.get k ≤ S0 (Iitem a b j) := by
    intro j k hjk
    have hne : Iitem a b j ≠ Iitem a b k := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Iitem] at this
      exact hjk (Fin.ext this)
    have := hmach _ _ hne (by rw [(pI j).2, (pI k).2])
    rw [(pI j).1, (pI k).1] at this
    exact this
  refine ⟨Finset.univ.filter (fun j => S0 (Iitem a b j) + a.get j ≤ b), ?_⟩
  have u1 := sh_sum_le (Finset.univ.filter (fun j => S0 (Iitem a b j) + a.get j ≤ b))
    (fun j => S0 (Iitem a b j)) (fun j => a.get j) 0 b
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega)
    (by intro i _ j _ hij; exact hLL i j hij)
  have u2 := sh_sum_le (Finset.univ.filter (fun j => ¬ (S0 (Iitem a b j) + a.get j ≤ b)))
    (fun j => S0 (Iitem a b j)) (fun j => a.get j) (b+1) (yI a)
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; have := hItem i; have := hL1 i; omega)
    (by intro i _ j _ hij; exact hLL i j hij)
  have u3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin a.length))
    (fun j => S0 (Iitem a b j) + a.get j ≤ b) (fun j => a.get j)
  unfold yI at u2
  omega

theorem knapI_core (a : List ℕ) (b : ℕ) (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrI a b).HasScheduleLE (yI a) :=
  ⟨fun ⟨S, hS⟩ => I_rev a b hbA S hS, I_fwd a b hbA⟩

end SchedComplexity.Shops

open SchedComplexity.Shops


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrI a b).HasScheduleLE (yI a) := by
  exact knapI_core a b hbA
