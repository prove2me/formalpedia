-- Prove2me | solution 1 for SchedComplexity.Shops.theorem_4j_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:25:55.941927+00:00
-- url     : https://prove2.me/submissions/7fcf2ff1-1839-4b95-b061-bcc7dce1cc7b

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

def ga (a : List ℕ) (j : Fin a.length) : ℕ := a.get j

def shW (a : List ℕ) (w : Fin a.length → ℕ) (T : Finset (Fin a.length)) (j : Fin a.length) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∈ T), w i

lemma shW_step (a : List ℕ) (w : Fin a.length → ℕ) (T : Finset (Fin a.length))
    (i j : Fin a.length) (hij : i < j) (hi : i ∈ T) : shW a w T i + w i ≤ shW a w T j := by
  unfold shW
  have : insert i (Finset.univ.filter (fun k => k < i ∧ k ∈ T)) ⊆
      Finset.univ.filter (fun k => k < j ∧ k ∈ T) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | ⟨h1, h2⟩
    · exact ⟨hij, hi⟩
    · exact ⟨lt_trans h1 hij, h2⟩
  have h2 := Finset.sum_le_sum_of_subset (f := w) this
  rw [Finset.sum_insert (by simp)] at h2
  linarith

lemma shW_le (a : List ℕ) (w : Fin a.length → ℕ) (T : Finset (Fin a.length))
    (j : Fin a.length) (hj : j ∈ T) : shW a w T j + w j ≤ ∑ i ∈ T, w i := by
  unfold shW
  have : insert j (Finset.univ.filter (fun k => k < j ∧ k ∈ T)) ⊆ T := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hk with rfl | ⟨h1, h2⟩
    · exact hj
    · exact h2
  have h2 := Finset.sum_le_sum_of_subset (f := w) this
  rw [Finset.sum_insert (by simp)] at h2
  linarith

def pA (a : List ℕ) (T : Finset (Fin a.length)) (j : Fin a.length) : ℕ := shW a (ga a) T j

lemma J_len (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) :
    ((constrJ a b).ops j).length = 2 := by
  by_cases hj : j.val < a.length
  · simp [constrJ, hj]
  · by_cases hj2 : j.val = a.length <;> simp [constrJ, hj, hj2]

def Jp (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) (k : ℕ) : ℕ :=
  if h : j.val < a.length then ga a ⟨j.val, h⟩
  else if j.val = a.length then (if k = 0 then b else 2 * (a.sum - b))
  else (if k = 0 then 2 * b else a.sum - b)
def Jm (a : List ℕ) (j : Fin (a.length+2)) (k : ℕ) : Fin 3 :=
  if j.val < a.length then (if k = 0 then 0 else 2)
  else if j.val = a.length then (if k = 0 then 0 else 1)
  else (if k = 0 then 1 else 2)

lemma J_pm (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) (r : Fin ((constrJ a b).ops j).length) :
    r.val < 2 ∧ (constrJ a b).proc ⟨j,r⟩ = Jp a b j r.val ∧
      (constrJ a b).mach ⟨j,r⟩ = Jm a j r.val := by
  have hl := J_len a b j
  have hr := r.isLt
  have hr2 : r.val < 2 := by omega
  refine ⟨hr2, ?_⟩
  have hk : r.val = 0 ∨ r.val = 1 := by omega
  by_cases hj : j.val < a.length
  · have hL : (constrJ a b).ops j = [(0, a.get ⟨j.val,hj⟩), (2, a.get ⟨j.val,hj⟩)] := by
      simp [constrJ, hj]
    have h1 := sh_get_of_eq hL r (by simp; omega)
    rcases hk with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
      simp [Jp, Jm, hj, ga]
  · by_cases hj2 : j.val = a.length
    · have hL : (constrJ a b).ops j = [(0, b), (1, 2 * (a.sum - b))] := by
        simp [constrJ, hj, hj2]
      have h1 := sh_get_of_eq hL r (by simp; omega)
      rcases hk with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
        simp [Jp, Jm, hj, hj2]
    · have hL : (constrJ a b).ops j = [(1, 2 * b), (2, a.sum - b)] := by
        simp [constrJ, hj, hj2]
      have h1 := sh_get_of_eq hL r (by simp; omega)
      rcases hk with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
        simp [Jp, Jm, hj, hj2]

def Js (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (j : Fin (a.length+2)) (r : ℕ) : ℕ :=
  if h : j.val < a.length then
    (if r = 0 then
      (if (⟨j.val, h⟩ : Fin a.length) ∈ S then pA a S ⟨j.val, h⟩
       else 2 * b + pA a Sᶜ ⟨j.val, h⟩)
     else
      (if (⟨j.val, h⟩ : Fin a.length) ∈ S then b + pA a S ⟨j.val, h⟩
       else a.sum + b + pA a Sᶜ ⟨j.val, h⟩))
  else if j.val = a.length then (if r = 0 then b else 2 * b)
  else (if r = 0 then 0 else 2 * b)

lemma J_rev (a : List ℕ) (b : ℕ) (hbA : b < a.sum)
    (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b) :
    (constrJ a b).HasScheduleLE (yJ a) := by
  classical
  have hA := sh_sum_get a
  have hSc : ∑ j ∈ Sᶜ, a.get j = a.sum - b := by
    have := Finset.sum_compl_add_sum S (fun j => a.get j)
    omega
  have hin : ∀ j : Fin a.length, j ∈ S → pA a S j + ga a j ≤ b := by
    intro j hj
    have h : pA a S j + ga a j ≤ ∑ i ∈ S, ga a i := shW_le a (ga a) S j hj
    have e : ∑ i ∈ S, ga a i = b := hS
    omega
  have hout : ∀ j : Fin a.length, j ∉ S → pA a Sᶜ j + ga a j ≤ a.sum - b := by
    intro j hj
    have h : pA a Sᶜ j + ga a j ≤ ∑ i ∈ Sᶜ, ga a i := shW_le a (ga a) Sᶜ j (by simpa using hj)
    have e : ∑ i ∈ Sᶜ, ga a i = a.sum - b := hSc
    omega
  have step1 : ∀ i j : Fin a.length, i < j → i ∈ S → pA a S i + ga a i ≤ pA a S j :=
    fun i j hij hi => shW_step a (ga a) S i j hij hi
  have step2 : ∀ i j : Fin a.length, i < j → i ∉ S → pA a Sᶜ i + ga a i ≤ pA a Sᶜ j :=
    fun i j hij hi => shW_step a (ga a) Sᶜ i j hij (by simpa using hi)
  have pair : ∀ (j j' : Fin (a.length+2)) (r r' : ℕ), j < j' → r < 2 → r' < 2 →
      Jm a j r = Jm a j' r' →
      (Js a b S j r + Jp a b j r ≤ Js a b S j' r' ∨ Js a b S j' r' + Jp a b j' r' ≤ Js a b S j r) := by
    intro j j' r r' hjj hr hr' hm
    have hjj' : j.val < j'.val := hjj
    have hj'2 := j'.isLt
    by_cases hj : j.val < a.length
    · by_cases hj' : j'.val < a.length
      · have hlt : (⟨j.val, hj⟩ : Fin a.length) < ⟨j'.val, hj'⟩ := hjj'
        simp only [Jp, Js, Jm, dif_pos hj, dif_pos hj'] at hm ⊢
        by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
          by_cases h2 : (⟨j'.val, hj'⟩ : Fin a.length) ∈ S <;>
          rcases (show r = 0 ∨ r = 1 by omega) with h | h <;>
          rcases (show r' = 0 ∨ r' = 1 by omega) with h' | h' <;> subst h <;> subst h' <;>
          simp only [h1, h2, if_pos, ↓reduceIte, one_ne_zero, hj, hj'] at hm ⊢ <;>
          first
          | (exfalso; revert hm; decide)
          | skip
        · left; have := step1 _ _ hlt h1; omega
        · left; have := step1 _ _ hlt h1; omega
        · left; have := hin _ h1; omega
        · left; have := hin _ h1; omega
        · right; have := hin _ h2; omega
        · right; have := hin _ h2; omega
        · left; have := step2 _ _ hlt h1; omega
        · left; have := step2 _ _ hlt h1; omega
      · by_cases hj2 : j'.val = a.length
        · simp only [Jp, Js, Jm, dif_pos hj, dif_neg hj', if_pos hj2] at hm ⊢
          by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
            rcases (show r = 0 ∨ r = 1 by omega) with h | h <;>
            rcases (show r' = 0 ∨ r' = 1 by omega) with h' | h' <;> subst h <;> subst h' <;>
            simp only [h1, if_pos, ↓reduceIte, one_ne_zero, hj, hj'] at hm ⊢ <;>
            first
            | (exfalso; revert hm; decide)
            | skip
          · left; have := hin _ h1; omega
          · right; omega
        · simp only [Jp, Js, Jm, dif_pos hj, dif_neg hj', if_neg hj2] at hm ⊢
          by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
            rcases (show r = 0 ∨ r = 1 by omega) with h | h <;>
            rcases (show r' = 0 ∨ r' = 1 by omega) with h' | h' <;> subst h <;> subst h' <;>
            simp only [h1, if_pos, ↓reduceIte, one_ne_zero, hj, hj'] at hm ⊢ <;>
            first
            | (exfalso; revert hm; decide)
            | skip
          · left; have := hin _ h1; omega
          · right; have := hout _ h1; omega
    · have hj2 : j.val = a.length := by
        have := j.isLt; omega
      have hj' : ¬ j'.val < a.length := by omega
      have hj'2' : ¬ j'.val = a.length := by omega
      simp only [Jp, Js, Jm, dif_neg hj, dif_neg hj', if_pos hj2, if_neg hj'2', if_neg hj, if_neg hj'] at hm ⊢
      rcases (show r = 0 ∨ r = 1 by omega) with h | h <;>
        rcases (show r' = 0 ∨ r' = 1 by omega) with h' | h' <;> subst h <;> subst h' <;>
        simp only [↓reduceIte, one_ne_zero] at hm ⊢ <;>
        first
        | (exfalso; revert hm; decide)
        | skip
      right; omega
  refine ⟨fun o => Js a b S o.1 o.2.val, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o; simp [constrJ]
  · intro j r r' hrr
    obtain ⟨hr2, hp, -⟩ := J_pm a b j r
    have hr2' := (J_pm a b j r').1
    have hk : r.val = 0 ∧ r'.val = 1 := by omega
    beta_reduce
    rw [hp, hk.2, hk.1]
    by_cases hj : j.val < a.length
    · simp only [Js, Jp, dif_pos hj, ↓reduceIte, one_ne_zero]
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;> simp only [h1, ↓reduceIte]
      · have := hin _ h1; omega
      · have := hout _ h1; omega
    · by_cases hj2 : j.val = a.length
      · simp only [Js, Jp, dif_neg hj, if_pos hj2, ↓reduceIte, one_ne_zero]; omega
      · simp only [Js, Jp, dif_neg hj, if_neg hj2, ↓reduceIte, one_ne_zero]; omega
  · intro o o' hne hm
    rcases o with ⟨j, r⟩
    rcases o' with ⟨j', r'⟩
    obtain ⟨hr2, hp, hmm⟩ := J_pm a b j r
    obtain ⟨hr2', hp', hmm'⟩ := J_pm a b j' r'
    rw [hmm, hmm'] at hm
    beta_reduce
    rw [hp, hp']
    by_cases hjj : j = j'
    · subst hjj
      exfalso
      have hkk : r.val ≠ r'.val := fun h => hne (by
        have : r = r' := Fin.ext h
        subst this; rfl)
      revert hm hkk
      have hk : r.val = 0 ∨ r.val = 1 := by omega
      have hk' : r'.val = 0 ∨ r'.val = 1 := by omega
      rcases hk with h | h <;> rcases hk' with h' | h' <;> simp [Jm, h, h'] <;>
        split_ifs <;> simp
    rcases lt_or_gt_of_ne hjj with h | h
    · exact pair j j' r.val r'.val h hr2 hr2' hm
    · exact (pair j' j r'.val r.val h hr2' hr2 hm.symm).symm
  · intro j k hjk; simp [constrJ] at hjk
  · intro j
    apply sh_completion_le
    intro r
    obtain ⟨hr2, hp, -⟩ := J_pm a b j r
    beta_reduce
    rw [hp]
    have hk : r.val = 0 ∨ r.val = 1 := by omega
    unfold yJ
    by_cases hj : j.val < a.length
    · simp only [Js, Jp, dif_pos hj]
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
        rcases hk with h | h <;> simp only [h, h1, ↓reduceIte, one_ne_zero]
      · have := hin _ h1; omega
      · have := hin _ h1; omega
      · have := hout _ h1; omega
      · have := hout _ h1; omega
    · by_cases hj2 : j.val = a.length
      · simp only [Js, Jp, dif_neg hj, if_pos hj2]
        rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero] <;> omega
      · simp only [Js, Jp, dif_neg hj, if_neg hj2]
        rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero] <;> omega

def Jop (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) (k : Fin 2) : (constrJ a b).Op :=
  ⟨j, ⟨k.val, by rw [J_len a b]; exact k.isLt⟩⟩

lemma J_fwd (a : List ℕ) (b : ℕ) (hbA : b < a.sum)
    (h : (constrJ a b).HasScheduleLE (yJ a)) : SchedComplexity.OneMachine.KnapsackYes a b := by
  classical
  obtain ⟨S0, ⟨-, hchain, hmach, -⟩, hC⟩ := h
  have hA := sh_sum_get a
  have hy : yJ a = 2 * a.sum := rfl
  let jP : Fin (a.length+2) := ⟨a.length, by omega⟩
  let jQ : Fin (a.length+2) := Fin.last (a.length+1)
  let jI : Fin a.length → Fin (a.length+2) := fun j => ⟨j.val, by omega⟩
  have pI0 : ∀ j : Fin a.length, (constrJ a b).proc (Jop a b (jI j) 0) = ga a j ∧
      (constrJ a b).mach (Jop a b (jI j) 0) = 0 := by
    intro j
    have := (J_pm a b _ (Jop a b (jI j) 0).2).2
    simpa [Jp, Jm, Jop, jI, j.isLt] using this
  have pI1 : ∀ j : Fin a.length, (constrJ a b).proc (Jop a b (jI j) 1) = ga a j ∧
      (constrJ a b).mach (Jop a b (jI j) 1) = 2 := by
    intro j
    have := (J_pm a b _ (Jop a b (jI j) 1).2).2
    simpa [Jp, Jm, Jop, jI, j.isLt] using this
  have pP0 : (constrJ a b).proc (Jop a b jP 0) = b ∧ (constrJ a b).mach (Jop a b jP 0) = 0 := by
    have := (J_pm a b _ (Jop a b jP 0).2).2
    simpa [Jp, Jm, Jop, jP] using this
  have pP1 : (constrJ a b).proc (Jop a b jP 1) = 2 * (a.sum - b) ∧
      (constrJ a b).mach (Jop a b jP 1) = 1 := by
    have := (J_pm a b _ (Jop a b jP 1).2).2
    simpa [Jp, Jm, Jop, jP] using this
  have pQ0 : (constrJ a b).proc (Jop a b jQ 0) = 2 * b ∧ (constrJ a b).mach (Jop a b jQ 0) = 1 := by
    have := (J_pm a b _ (Jop a b jQ 0).2).2
    simpa [Jp, Jm, Jop, jQ] using this
  have pQ1 : (constrJ a b).proc (Jop a b jQ 1) = a.sum - b ∧
      (constrJ a b).mach (Jop a b jQ 1) = 2 := by
    have := (J_pm a b _ (Jop a b jQ 1).2).2
    simpa [Jp, Jm, Jop, jQ] using this
  have cP : S0 (Jop a b jP 0) + (constrJ a b).proc (Jop a b jP 0) ≤ S0 (Jop a b jP 1) :=
    hchain jP (Jop a b jP 0).2 (Jop a b jP 1).2 (by simp [Jop])
  have cQ : S0 (Jop a b jQ 0) + (constrJ a b).proc (Jop a b jQ 0) ≤ S0 (Jop a b jQ 1) :=
    hchain jQ (Jop a b jQ 0).2 (Jop a b jQ 1).2 (by simp [Jop])
  rw [pP0.1] at cP
  rw [pQ0.1] at cQ
  have eP : S0 (Jop a b jP 1) + (constrJ a b).proc (Jop a b jP 1) ≤ yJ a :=
    le_trans (sh_le_completion _ S0 (Jop a b jP 1)) (hC jP)
  have eQ : S0 (Jop a b jQ 1) + (constrJ a b).proc (Jop a b jQ 1) ≤ yJ a :=
    le_trans (sh_le_completion _ S0 (Jop a b jQ 1)) (hC jQ)
  rw [pP1.1] at eP
  rw [pQ1.1] at eQ
  have hPQ : S0 (Jop a b jP 1) + (constrJ a b).proc (Jop a b jP 1) ≤ S0 (Jop a b jQ 0) ∨
      S0 (Jop a b jQ 0) + (constrJ a b).proc (Jop a b jQ 0) ≤ S0 (Jop a b jP 1) := by
    apply hmach
    · intro h; have := congrArg (fun o => o.1.val) h; simp [Jop, jP, jQ] at this
    · rw [pP1.2, pQ0.2]
  rw [pP1.1, pQ0.1] at hPQ
  have hq : S0 (Jop a b jQ 0) + 2 * b ≤ S0 (Jop a b jP 1) := by
    rcases hPQ with h | h
    · omega
    · exact h
  have hp2 : S0 (Jop a b jP 0) + b ≤ 2 * b := by omega
  have d1 : ∀ j : Fin a.length, S0 (Jop a b (jI j) 0) + ga a j ≤ S0 (Jop a b (jI j) 1) := by
    intro j
    have e : S0 (Jop a b (jI j) 0) + (constrJ a b).proc (Jop a b (jI j) 0) ≤
        S0 (Jop a b (jI j) 1) :=
      hchain (jI j) (Jop a b (jI j) 0).2 (Jop a b (jI j) 1).2 (by simp [Jop])
    rw [(pI0 j).1] at e
    exact e
  have d2 : ∀ j : Fin a.length, S0 (Jop a b (jI j) 1) + ga a j ≤ yJ a := by
    intro j
    have := le_trans (sh_le_completion _ S0 (Jop a b (jI j) 1)) (hC (jI j))
    rw [(pI1 j).1] at this
    exact this
  have hLP : ∀ j : Fin a.length, S0 (Jop a b (jI j) 0) + ga a j ≤ S0 (Jop a b jP 0) ∨
      S0 (Jop a b jP 0) + b ≤ S0 (Jop a b (jI j) 0) := by
    intro j
    have hne : Jop a b (jI j) 0 ≠ Jop a b jP 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Jop, jI, jP] at this
      have := j.isLt; omega
    have := hmach _ _ hne (by rw [(pI0 j).2, pP0.2])
    rw [(pI0 j).1, pP0.1] at this
    exact this
  have hLQ : ∀ j : Fin a.length, S0 (Jop a b (jI j) 1) + ga a j ≤ S0 (Jop a b jQ 1) ∨
      S0 (Jop a b jQ 1) + (a.sum - b) ≤ S0 (Jop a b (jI j) 1) := by
    intro j
    have hne : Jop a b (jI j) 1 ≠ Jop a b jQ 1 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Jop, jI, jQ] at this
      have := j.isLt; omega
    have := hmach _ _ hne (by rw [(pI1 j).2, pQ1.2])
    rw [(pI1 j).1, pQ1.1] at this
    exact this
  have hLL0 : ∀ j k : Fin a.length, j ≠ k →
      S0 (Jop a b (jI j) 0) + ga a j ≤ S0 (Jop a b (jI k) 0) ∨
      S0 (Jop a b (jI k) 0) + ga a k ≤ S0 (Jop a b (jI j) 0) := by
    intro j k hjk
    have hne : Jop a b (jI j) 0 ≠ Jop a b (jI k) 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Jop, jI] at this
      exact hjk (Fin.ext this)
    have := hmach _ _ hne (by rw [(pI0 j).2, (pI0 k).2])
    rw [(pI0 j).1, (pI0 k).1] at this
    exact this
  have hLL1 : ∀ j k : Fin a.length, j ≠ k →
      S0 (Jop a b (jI j) 1) + ga a j ≤ S0 (Jop a b (jI k) 1) ∨
      S0 (Jop a b (jI k) 1) + ga a k ≤ S0 (Jop a b (jI j) 1) := by
    intro j k hjk
    have hne : Jop a b (jI j) 1 ≠ Jop a b (jI k) 1 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Jop, jI] at this
      exact hjk (Fin.ext this)
    have := hmach _ _ hne (by rw [(pI1 j).2, (pI1 k).2])
    rw [(pI1 j).1, (pI1 k).1] at this
    exact this
  refine ⟨Finset.univ.filter (fun j => S0 (Jop a b (jI j) 1) < 2 * b), ?_⟩
  show ∑ j ∈ Finset.univ.filter (fun j => S0 (Jop a b (jI j) 1) < 2 * b), ga a j = b
  have hA' : ∑ j : Fin a.length, ga a j = a.sum := hA
  have uB1 := sh_sum_le ((Finset.univ.filter (fun j => S0 (Jop a b (jI j) 1) < 2 * b)).filter
      (fun j => S0 (Jop a b (jI j) 0) + ga a j ≤ S0 (Jop a b jP 0)))
    (fun j => S0 (Jop a b (jI j) 0)) (fun j => ga a j) 0 (S0 (Jop a b jP 0))
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega)
    (by intro i _ j _ hij; exact hLL0 i j hij)
  have uB2 := sh_sum_le ((Finset.univ.filter (fun j => S0 (Jop a b (jI j) 1) < 2 * b)).filter
      (fun j => ¬ (S0 (Jop a b (jI j) 0) + ga a j ≤ S0 (Jop a b jP 0))))
    (fun j => S0 (Jop a b (jI j) 0)) (fun j => ga a j) (S0 (Jop a b jP 0) + b) (2 * b)
    (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have := d1 i; have := hLP i; omega)
    (by intro i _ j _ hij; exact hLL0 i j hij)
  have uC1 := sh_sum_le ((Finset.univ.filter (fun j => ¬ (S0 (Jop a b (jI j) 1) < 2 * b))).filter
      (fun j => S0 (Jop a b (jI j) 1) + ga a j ≤ S0 (Jop a b jQ 1)))
    (fun j => S0 (Jop a b (jI j) 1)) (fun j => ga a j) (2 * b) (S0 (Jop a b jQ 1))
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega)
    (by intro i _ j _ hij; exact hLL1 i j hij)
  have uC2 := sh_sum_le ((Finset.univ.filter (fun j => ¬ (S0 (Jop a b (jI j) 1) < 2 * b))).filter
      (fun j => ¬ (S0 (Jop a b (jI j) 1) + ga a j ≤ S0 (Jop a b jQ 1))))
    (fun j => S0 (Jop a b (jI j) 1)) (fun j => ga a j) (S0 (Jop a b jQ 1) + (a.sum - b))
    (yJ a)
    (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have := d2 i; have := hLQ i; omega)
    (by intro i _ j _ hij; exact hLL1 i j hij)
  have s1 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun j => S0 (Jop a b (jI j) 1) < 2 * b))
    (fun j => S0 (Jop a b (jI j) 0) + ga a j ≤ S0 (Jop a b jP 0)) (fun j => ga a j)
  have s2 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun j => ¬ (S0 (Jop a b (jI j) 1) < 2 * b)))
    (fun j => S0 (Jop a b (jI j) 1) + ga a j ≤ S0 (Jop a b jQ 1)) (fun j => ga a j)
  have s3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin a.length))
    (fun j => S0 (Jop a b (jI j) 1) < 2 * b) (fun j => ga a j)
  omega

theorem knapJ_core (a : List ℕ) (b : ℕ) (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrJ a b).HasScheduleLE (yJ a) :=
  ⟨fun ⟨S, hS⟩ => J_rev a b hbA S hS, J_fwd a b hbA⟩

end SchedComplexity.Shops

open SchedComplexity.Shops


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrJ a b).HasScheduleLE (yJ a) := by
  exact knapJ_core a b hbA
