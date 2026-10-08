-- Prove2me | solution 1 for SchedComplexity.Shops.theorem_4h_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:20:32.241977+00:00
-- url     : https://prove2.me/submissions/0322335a-71b3-413b-9761-93881d884e49

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

lemma H_len (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) :
    ((constrH a b).ops j).length = 2 := by
  by_cases hj : j.val < a.length
  · simp [constrH, hj]
  · by_cases hj2 : j.val = a.length <;> simp [constrH, hj, hj2]

def Hp (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) (k : ℕ) : ℕ :=
  if h : j.val < a.length then (if k = 0 then a.length * ga a ⟨j.val, h⟩ else 1)
  else if j.val = a.length then (if k = 0 then 1 else a.length * b)
  else (if k = 0 then 1 else a.length * (a.sum - b))
def Gm (k : ℕ) : Fin 2 := if k = 0 then 0 else 1

lemma H_pm (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) (r : Fin ((constrH a b).ops j).length) :
    r.val < 2 ∧ (constrH a b).proc ⟨j,r⟩ = Hp a b j r.val ∧
      (constrH a b).mach ⟨j,r⟩ = Gm r.val := by
  have hl := H_len a b j
  have hr := r.isLt
  have hr2 : r.val < 2 := by omega
  refine ⟨hr2, ?_⟩
  have hk : r.val = 0 ∨ r.val = 1 := by omega
  by_cases hj : j.val < a.length
  · have hL : (constrH a b).ops j = [(0, a.length * a.get ⟨j.val,hj⟩), (1, 1)] := by
      simp [constrH, hj]
    have h1 := sh_get_of_eq hL r (by simp; omega)
    rcases hk with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
      simp [Hp, Gm, hj, ga]
  · by_cases hj2 : j.val = a.length
    · have hL : (constrH a b).ops j = [(0, 1), (1, a.length * b)] := by
        simp [constrH, hj, hj2]
      have h1 := sh_get_of_eq hL r (by simp; omega)
      rcases hk with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
        simp [Hp, Gm, hj, hj2]
    · have hL : (constrH a b).ops j = [(0, 1), (1, a.length * (a.sum - b))] := by
        simp [constrH, hj, hj2]
      have h1 := sh_get_of_eq hL r (by simp; omega)
      rcases hk with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
        simp [Hp, Gm, hj, hj2]

def pA (a : List ℕ) (T : Finset (Fin a.length)) (j : Fin a.length) : ℕ := shW a (ga a) T j
def rk (a : List ℕ) (T : Finset (Fin a.length)) (j : Fin a.length) : ℕ := shW a (fun _ => 1) T j

def Hs (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (j : Fin (a.length+2)) (r : ℕ) : ℕ :=
  if h : j.val < a.length then
    (if r = 0 then
      (if (⟨j.val, h⟩ : Fin a.length) ∈ S then 1 + a.length * pA a S ⟨j.val, h⟩
       else a.length * b + 2 + a.length * pA a Sᶜ ⟨j.val, h⟩)
     else
      (if (⟨j.val, h⟩ : Fin a.length) ∈ S then a.length * b + 1 + rk a S ⟨j.val, h⟩
       else a.length * a.sum + 1 + S.card + rk a Sᶜ ⟨j.val, h⟩))
  else if j.val = a.length then (if r = 0 then 0 else 1)
  else (if r = 0 then a.length * b + 1 else a.length * b + 1 + S.card)

lemma H_rev (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b) (hbA : b < a.sum)
    (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b) :
    (constrH a b).HasScheduleLE (yH a) := by
  classical
  have hA := sh_sum_get a
  have hSc : ∑ j ∈ Sᶜ, a.get j = a.sum - b := by
    have := Finset.sum_compl_add_sum S (fun j => a.get j)
    omega
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h; simp at hS; omega
  have hScard : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hcard : S.card + Sᶜ.card = a.length := by
    simpa using Finset.card_add_card_compl S
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
  have rkS : ∀ j : Fin a.length, j ∈ S → rk a S j + 1 ≤ S.card := by
    intro j hj
    have h : rk a S j + 1 ≤ ∑ i ∈ S, 1 := shW_le a (fun _ => 1) S j hj
    simpa using h
  have rkN : ∀ j : Fin a.length, j ∉ S → rk a Sᶜ j + 1 ≤ Sᶜ.card := by
    intro j hj
    have h : rk a Sᶜ j + 1 ≤ ∑ i ∈ Sᶜ, 1 := shW_le a (fun _ => 1) Sᶜ j (by simpa using hj)
    simpa using h
  have hapos : ∀ j : Fin a.length, 1 ≤ ga a j := fun j => ha _ (List.get_mem _ _)
  have hT1 : 1 ≤ a.length := by have := Finset.card_le_univ S; simp at this; omega
  have hTA : a.length * (a.sum - b) + a.length * b = a.length * a.sum := by
    rw [← mul_add]; congr 1; omega
  have hbA' : a.length * b ≤ a.length * a.sum := Nat.mul_le_mul_left _ hbA.le
  have F1 : ∀ j : Fin a.length, j ∈ S → a.length * (pA a S j + ga a j) ≤ a.length * b :=
    fun j hj => Nat.mul_le_mul_left _ (hin j hj)
  have F2 : ∀ j : Fin a.length, j ∉ S →
      a.length * b + 2 + a.length * (pA a Sᶜ j + ga a j) ≤ a.length * a.sum + 2 := by
    intro j hj
    have h := Nat.mul_le_mul_left a.length (hout j hj)
    have h' : a.length * (pA a Sᶜ j + ga a j) ≤ a.length * (a.sum - b) := h
    linarith
  have hTa : ∀ j : Fin a.length, a.length ≤ a.length * ga a j := by
    intro j; have := hapos j; nlinarith
  have step1 : ∀ i j : Fin a.length, i < j → i ∈ S →
      a.length * (pA a S i + ga a i) ≤ a.length * pA a S j := fun i j hij hi =>
    Nat.mul_le_mul_left _ (shW_step a (ga a) S i j hij hi)
  have step2 : ∀ i j : Fin a.length, i < j → i ∉ S →
      a.length * (pA a Sᶜ i + ga a i) ≤ a.length * pA a Sᶜ j := fun i j hij hi =>
    Nat.mul_le_mul_left _ (shW_step a (ga a) Sᶜ i j hij (by simpa using hi))
  have stepr1 : ∀ i j : Fin a.length, i < j → i ∈ S → rk a S i + 1 ≤ rk a S j :=
    fun i j hij hi => shW_step a (fun _ => 1) S i j hij hi
  have stepr2 : ∀ i j : Fin a.length, i < j → i ∉ S → rk a Sᶜ i + 1 ≤ rk a Sᶜ j :=
    fun i j hij hi => shW_step a (fun _ => 1) Sᶜ i j hij (by simpa using hi)
  have nn : ∀ i : Fin a.length, 0 ≤ a.length * pA a S i ∧ 0 ≤ a.length * pA a Sᶜ i ∧
      0 ≤ rk a S i ∧ 0 ≤ rk a Sᶜ i := fun i => ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  have nb : 0 ≤ a.length * b := Nat.zero_le _
  have pair : ∀ (j j' : Fin (a.length+2)) (r : ℕ), j < j' → r < 2 →
      (Hs a b S j r + Hp a b j r ≤ Hs a b S j' r ∨ Hs a b S j' r + Hp a b j' r ≤ Hs a b S j r) := by
    intro j j' r hjj hr
    have hr' : r = 0 ∨ r = 1 := by omega
    have hjj' : j.val < j'.val := hjj
    have hj'2 := j'.isLt
    by_cases hj : j.val < a.length
    · obtain ⟨n1, n2, n3, n4⟩ := nn ⟨j.val, hj⟩
      by_cases hj' : j'.val < a.length
      · obtain ⟨m1, m2, m3, m4⟩ := nn ⟨j'.val, hj'⟩
        have hlt : (⟨j.val, hj⟩ : Fin a.length) < ⟨j'.val, hj'⟩ := hjj'
        simp only [Hp, Hs, dif_pos hj, dif_pos hj']
        by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
          by_cases h2 : (⟨j'.val, hj'⟩ : Fin a.length) ∈ S <;>
          rcases hr' with h | h <;> subst h <;> simp only [h1, h2, ↓reduceIte, one_ne_zero]
        · left; have := step1 _ _ hlt h1; linarith
        · left; have := stepr1 _ _ hlt h1; linarith
        · left; have := F1 _ h1; linarith
        · left; have := rkS _ h1; linarith
        · right; have := F1 _ h2; linarith
        · right; have := rkS _ h2; linarith
        · left; have := step2 _ _ hlt h1; linarith
        · left; have := stepr2 _ _ hlt h1; linarith
      · by_cases hj2 : j'.val = a.length
        · simp only [Hp, Hs, dif_pos hj, dif_neg hj', if_pos hj2]
          by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
            rcases hr' with h | h <;> subst h <;> simp only [h1, ↓reduceIte, one_ne_zero]
          · right; linarith
          · right; linarith
          · right; linarith
          · right; linarith
        · simp only [Hp, Hs, dif_pos hj, dif_neg hj', if_neg hj2]
          by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
            rcases hr' with h | h <;> subst h <;> simp only [h1, ↓reduceIte, one_ne_zero]
          · left; have := F1 _ h1; linarith
          · left; have := rkS _ h1; linarith
          · right; linarith
          · right; have := rkN _ h1; linarith
    · have hj2 : j.val = a.length := by
        have := j.isLt; omega
      have hj' : ¬ j'.val < a.length := by omega
      have hj'2' : ¬ j'.val = a.length := by omega
      simp only [Hp, Hs, dif_neg hj, dif_neg hj', if_pos hj2, if_neg hj'2']
      rcases hr' with h | h <;> subst h <;> simp only [↓reduceIte, one_ne_zero]
      · left; linarith
      · left; linarith
  refine ⟨fun o => Hs a b S o.1 o.2.val, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o; simp [constrH]
  · intro j r r' hrr
    obtain ⟨hr2, hp, -⟩ := H_pm a b j r
    have hr2' := (H_pm a b j r').1
    have hk : r.val = 0 ∧ r'.val = 1 := by omega
    beta_reduce
    rw [hp, hk.2, hk.1]
    by_cases hj : j.val < a.length
    · obtain ⟨n1, n2, n3, n4⟩ := nn ⟨j.val, hj⟩
      simp only [Hs, Hp, dif_pos hj, ↓reduceIte, one_ne_zero]
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;> simp only [h1, ↓reduceIte]
      · have := F1 _ h1; linarith
      · have := F2 _ h1; linarith
    · by_cases hj2 : j.val = a.length
      · simp only [Hs, Hp, dif_neg hj, if_pos hj2, ↓reduceIte, one_ne_zero]; linarith
      · simp only [Hs, Hp, dif_neg hj, if_neg hj2, ↓reduceIte, one_ne_zero]; linarith
  · intro o o' hne hm
    rcases o with ⟨j, r⟩
    rcases o' with ⟨j', r'⟩
    obtain ⟨hr2, hp, hmm⟩ := H_pm a b j r
    obtain ⟨hr2', hp', hmm'⟩ := H_pm a b j' r'
    rw [hmm, hmm'] at hm
    beta_reduce
    rw [hp, hp']
    have hkk : r.val = r'.val := by
      have hk : r.val = 0 ∨ r.val = 1 := by omega
      have hk' : r'.val = 0 ∨ r'.val = 1 := by omega
      rcases hk with h | h <;> rcases hk' with h' | h' <;> simp [Gm, h, h'] at hm ⊢
    by_cases hjj : j = j'
    · subst hjj
      have : r = r' := Fin.ext hkk
      subst this; exact absurd rfl hne
    rw [← hkk]
    rcases lt_or_gt_of_ne hjj with h | h
    · exact pair j j' r.val h hr2
    · exact (pair j' j r.val h hr2).symm
  · intro j k hjk r'
    simp only [constrH, Finset.mem_singleton, Prod.mk.injEq] at hjk
    obtain ⟨rfl, rfl⟩ := hjk
    have hr2' := (H_pm a b _ r').1
    apply le_trans (sh_completion_le _ _ _ (a.length * b + 1) ?_)
    · beta_reduce
      have hk : r'.val = 0 ∨ r'.val = 1 := by omega
      have hnl : ¬ (a.length + 1 < a.length) := by omega
      have hne2 : ¬ (a.length + 1 = a.length) := by omega
      simp only [Hs, Fin.val_last, dif_neg hnl, if_neg hne2]
      rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero] <;> linarith
    · intro r
      obtain ⟨hr2, hp, -⟩ := H_pm a b _ r
      beta_reduce
      rw [hp]
      have hk : r.val = 0 ∨ r.val = 1 := by omega
      simp only [Hs, Hp, lt_irrefl, dif_neg, not_false_eq_true, ↓reduceIte]
      rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero] <;> linarith
  · intro j
    apply sh_completion_le
    intro r
    obtain ⟨hr2, hp, -⟩ := H_pm a b j r
    beta_reduce
    rw [hp]
    have hk : r.val = 0 ∨ r.val = 1 := by omega
    unfold yH
    by_cases hj : j.val < a.length
    · obtain ⟨n1, n2, n3, n4⟩ := nn ⟨j.val, hj⟩
      simp only [Hs, Hp, dif_pos hj]
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
        rcases hk with h | h <;> simp only [h, h1, ↓reduceIte, one_ne_zero]
      · have := F1 _ h1; linarith
      · have := rkS _ h1; linarith
      · have := F2 _ h1; linarith
      · have := rkN _ h1; linarith
    · by_cases hj2 : j.val = a.length
      · simp only [Hs, Hp, dif_neg hj, if_pos hj2]
        rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero] <;> linarith
      · simp only [Hs, Hp, dif_neg hj, if_neg hj2]
        rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero] <;> linarith

theorem knapH_core_rev (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b) (hbA : b < a.sum)
    (h : SchedComplexity.OneMachine.KnapsackYes a b) : (constrH a b).HasScheduleLE (yH a) :=
  match h with | ⟨S, hS⟩ => H_rev a b ha hb hbA S hS

lemma H_arith (T A b x xc sp1 q1 y : ℕ) (hT : 1 ≤ T) (hbA : b < A) (hsum : x + xc = A)
    (h1 : sp1 + 1 + T * b ≤ q1) (h2 : q1 + 1 + T * (A - b) ≤ y) (hy : y = T * A + T + 1)
    (u1 : T * x ≤ q1 - (sp1 + 1)) (u2 : T * xc ≤ (y - 1) - (q1 + 1)) : x = b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbA.le
  rw [Nat.add_sub_cancel_left] at h2
  have hTd : 1 ≤ T * d := Nat.mul_pos hT (by omega)
  have u1' : T * x + (sp1 + 1) ≤ q1 := by omega
  have u2' : T * xc + (q1 + 1) ≤ y - 1 := by omega
  have e1 : x ≤ b := by
    by_contra hcon
    have := Nat.mul_le_mul_left T (show b + 1 ≤ x by omega)
    nlinarith
  have e2 : b ≤ x := by
    by_contra hcon
    have := Nat.mul_le_mul_left T (show d + 1 ≤ xc by omega)
    have u2'' : T * xc + q1 + 2 ≤ y := by omega
    nlinarith
  omega

def Hop (a : List ℕ) (b : ℕ) (j : Fin (a.length+2)) (k : Fin 2) : (constrH a b).Op :=
  ⟨j, ⟨k.val, by rw [H_len a b]; exact k.isLt⟩⟩

lemma H_fwd (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hbA : b < a.sum)
    (h : (constrH a b).HasScheduleLE (yH a)) : SchedComplexity.OneMachine.KnapsackYes a b := by
  classical
  obtain ⟨S0, ⟨-, hchain, hmach, hprec⟩, hC⟩ := h
  have hA := sh_sum_get a
  have hT1 : 1 ≤ a.length := by
    rcases a with _ | ⟨x, l⟩
    · simp at hbA
    · simp
  have hTA : a.length * (a.sum - b) + a.length * b = a.length * a.sum := by
    rw [← mul_add]; congr 1; omega
  have hy : yH a = a.length * a.sum + a.length + 1 := by unfold yH; ring
  have hapos : ∀ j : Fin a.length, 1 ≤ ga a j := fun j => ha _ (List.get_mem _ _)
  have hTa : ∀ j : Fin a.length, a.length ≤ a.length * ga a j := by
    intro j; have := hapos j; nlinarith
  let jP : Fin (a.length+2) := ⟨a.length, by omega⟩
  let jQ : Fin (a.length+2) := Fin.last (a.length+1)
  let jI : Fin a.length → Fin (a.length+2) := fun j => ⟨j.val, by omega⟩
  have pI0 : ∀ j : Fin a.length, (constrH a b).proc (Hop a b (jI j) 0) = a.length * ga a j ∧
      (constrH a b).mach (Hop a b (jI j) 0) = 0 := by
    intro j
    have := (H_pm a b _ (Hop a b (jI j) 0).2).2
    simpa [Hp, Gm, Hop, jI, j.isLt] using this
  have pI1 : ∀ j : Fin a.length, (constrH a b).proc (Hop a b (jI j) 1) = 1 ∧
      (constrH a b).mach (Hop a b (jI j) 1) = 1 := by
    intro j
    have := (H_pm a b _ (Hop a b (jI j) 1).2).2
    simpa [Hp, Gm, Hop, jI, j.isLt] using this
  have pP0 : (constrH a b).proc (Hop a b jP 0) = 1 ∧ (constrH a b).mach (Hop a b jP 0) = 0 := by
    have := (H_pm a b _ (Hop a b jP 0).2).2
    simpa [Hp, Gm, Hop, jP] using this
  have pP1 : (constrH a b).proc (Hop a b jP 1) = a.length * b ∧
      (constrH a b).mach (Hop a b jP 1) = 1 := by
    have := (H_pm a b _ (Hop a b jP 1).2).2
    simpa [Hp, Gm, Hop, jP] using this
  have pQ0 : (constrH a b).proc (Hop a b jQ 0) = 1 ∧ (constrH a b).mach (Hop a b jQ 0) = 0 := by
    have := (H_pm a b _ (Hop a b jQ 0).2).2
    simpa [Hp, Gm, Hop, jQ] using this
  have pQ1 : (constrH a b).proc (Hop a b jQ 1) = a.length * (a.sum - b) ∧
      (constrH a b).mach (Hop a b jQ 1) = 1 := by
    have := (H_pm a b _ (Hop a b jQ 1).2).2
    simpa [Hp, Gm, Hop, jQ] using this
  have cP : S0 (Hop a b jP 0) + (constrH a b).proc (Hop a b jP 0) ≤ S0 (Hop a b jP 1) :=
    hchain jP (Hop a b jP 0).2 (Hop a b jP 1).2 (by simp [Hop])
  have cQ : S0 (Hop a b jQ 0) + (constrH a b).proc (Hop a b jQ 0) ≤ S0 (Hop a b jQ 1) :=
    hchain jQ (Hop a b jQ 0).2 (Hop a b jQ 1).2 (by simp [Hop])
  rw [pP0.1] at cP
  rw [pQ0.1] at cQ
  have hpr : (constrH a b).completion S0 jP ≤ S0 (Hop a b jQ 0) :=
    hprec jP jQ (by simp [constrH, jP, jQ]) (Hop a b jQ 0).2
  have eP : S0 (Hop a b jP 1) + (constrH a b).proc (Hop a b jP 1) ≤
      (constrH a b).completion S0 jP := sh_le_completion _ S0 (Hop a b jP 1)
  rw [pP1.1] at eP
  have eQ : S0 (Hop a b jQ 1) + (constrH a b).proc (Hop a b jQ 1) ≤ yH a :=
    le_trans (sh_le_completion _ S0 (Hop a b jQ 1)) (hC jQ)
  rw [pQ1.1] at eQ
  have h1 : S0 (Hop a b jP 0) + 1 + a.length * b ≤ S0 (Hop a b jQ 0) := by omega
  have h2 : S0 (Hop a b jQ 0) + 1 + a.length * (a.sum - b) ≤ yH a := by omega
  have hsp : S0 (Hop a b jP 0) + 1 ≤ a.length := by omega
  have d1 : ∀ j : Fin a.length, S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b (jI j) 1) := by
    intro j
    have e : S0 (Hop a b (jI j) 0) + (constrH a b).proc (Hop a b (jI j) 0) ≤ S0 (Hop a b (jI j) 1) :=
      hchain (jI j) (Hop a b (jI j) 0).2 (Hop a b (jI j) 1).2 (by simp [Hop])
    rw [(pI0 j).1] at e
    exact e
  have d2 : ∀ j : Fin a.length, S0 (Hop a b (jI j) 1) + 1 ≤ yH a := by
    intro j
    have := le_trans (sh_le_completion _ S0 (Hop a b (jI j) 1)) (hC (jI j))
    rw [(pI1 j).1] at this
    exact this
  have hLP : ∀ j : Fin a.length, S0 (Hop a b jP 0) + 1 ≤ S0 (Hop a b (jI j) 0) := by
    intro j
    have hne : Hop a b (jI j) 0 ≠ Hop a b jP 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Hop, jI, jP] at this
      have := j.isLt; omega
    have := hmach _ _ hne (by rw [(pI0 j).2, pP0.2])
    rw [(pI0 j).1, pP0.1] at this
    have := hTa j
    rcases ‹_ ∨ _› with h | h
    · omega
    · exact h
  have hLQ : ∀ j : Fin a.length, S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0) ∨
      S0 (Hop a b jQ 0) + 1 ≤ S0 (Hop a b (jI j) 0) := by
    intro j
    have hne : Hop a b (jI j) 0 ≠ Hop a b jQ 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Hop, jI, jQ] at this
      have := j.isLt; omega
    have := hmach _ _ hne (by rw [(pI0 j).2, pQ0.2])
    rw [(pI0 j).1, pQ0.1] at this
    exact this
  have hLL : ∀ j k : Fin a.length, j ≠ k →
      S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b (jI k) 0) ∨
      S0 (Hop a b (jI k) 0) + a.length * ga a k ≤ S0 (Hop a b (jI j) 0) := by
    intro j k hjk
    have hne : Hop a b (jI j) 0 ≠ Hop a b (jI k) 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Hop, jI] at this
      exact hjk (Fin.ext this)
    have := hmach _ _ hne (by rw [(pI0 j).2, (pI0 k).2])
    rw [(pI0 j).1, (pI0 k).1] at this
    exact this
  refine ⟨Finset.univ.filter
    (fun j => S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0)), ?_⟩
  have u1 := sh_sum_le (Finset.univ.filter
      (fun j => S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0)))
    (fun j => S0 (Hop a b (jI j) 0)) (fun j => a.length * ga a j) (S0 (Hop a b jP 0) + 1)
    (S0 (Hop a b jQ 0))
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have := hLP i; omega)
    (by intro i _ j _ hij; exact hLL i j hij)
  have u2 := sh_sum_le (Finset.univ.filter
      (fun j => ¬ (S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0))))
    (fun j => S0 (Hop a b (jI j) 0)) (fun j => a.length * ga a j) (S0 (Hop a b jQ 0) + 1)
    (yH a - 1)
    (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have := d1 i; have := d2 i; have := hLQ i; omega)
    (by intro i _ j _ hij; exact hLL i j hij)
  have u3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin a.length))
    (fun j => S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0)) (fun j => ga a j)
  have hA' : ∑ j : Fin a.length, ga a j = a.sum := hA
  rw [← Finset.mul_sum] at u1 u2
  show ∑ j ∈ Finset.univ.filter
      (fun j => S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0)), ga a j = b
  generalize hx : ∑ j ∈ Finset.univ.filter
      (fun j => S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0)), ga a j = x
    at u1 u2 u3 ⊢
  generalize hxc : ∑ j ∈ Finset.univ.filter
      (fun j => ¬ (S0 (Hop a b (jI j) 0) + a.length * ga a j ≤ S0 (Hop a b jQ 0))), ga a j = xc
    at u1 u2 u3
  have hsum : x + xc = a.sum := by rw [← hA']; exact u3
  exact H_arith a.length a.sum b x xc _ _ _ hT1 hbA hsum h1 h2 hy u1 u2

theorem knapH_core (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b) (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrH a b).HasScheduleLE (yH a) :=
  ⟨fun h => knapH_core_rev a b ha hb hbA h, H_fwd a b ha hbA⟩

end SchedComplexity.Shops

open SchedComplexity.Shops


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrH a b).HasScheduleLE (yH a) := by
  exact knapH_core a b ha hb hbA
