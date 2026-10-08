-- Prove2me | solution 1 for SchedComplexity.Shops.theorem_4g_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:08:39.870167+00:00
-- url     : https://prove2.me/submissions/b6321a02-90e3-4c2d-a9fc-d09f0b5c96df

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

lemma G_len (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) :
    ((constrG a b).ops j).length = 2 := by
  by_cases hj : j.val < a.length <;> simp [constrG, hj]

def ga (a : List ℕ) (j : Fin a.length) : ℕ := a.get j

def Gp (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) (k : ℕ) : ℕ :=
  if h : j.val < a.length then (if k = 0 then a.length * ga a ⟨j.val, h⟩ else 1)
  else (if k = 0 then 1 else a.length * (a.sum - b))
def Gm (k : ℕ) : Fin 2 := if k = 0 then 0 else 1

lemma G_pm (a : List ℕ) (b : ℕ) (j : Fin (a.length+1)) (r : Fin ((constrG a b).ops j).length) :
    r.val < 2 ∧ (constrG a b).proc ⟨j,r⟩ = Gp a b j r.val ∧
      (constrG a b).mach ⟨j,r⟩ = Gm r.val := by
  have hl := G_len a b j
  have hr := r.isLt
  have hr2 : r.val < 2 := by omega
  refine ⟨hr2, ?_⟩
  by_cases hj : j.val < a.length
  · have hL : (constrG a b).ops j = [(0, a.length * a.get ⟨j.val,hj⟩), (1, 1)] := by
      simp [constrG, hj]
    have h1 := sh_get_of_eq hL r (by simp; omega)
    have : r.val = 0 ∨ r.val = 1 := by omega
    rcases this with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
      simp [Gp, Gm, hj, ga]
  · have hL : (constrG a b).ops j = [(0, 1), (1, a.length * (a.sum - b))] := by
      simp [constrG, hj]
    have h1 := sh_get_of_eq hL r (by simp; omega)
    have : r.val = 0 ∨ r.val = 1 := by omega
    rcases this with h | h <;> simp only [ShopInstance.proc, ShopInstance.mach, h1, h] <;>
      simp [Gp, Gm, hj, ga]

def Gf (a : List ℕ) (i0 j : Fin a.length) : ℕ := if j.val < i0.val then j.val else j.val - 1

def Gs (a : List ℕ) (b : ℕ) (S : Finset (Fin a.length)) (i0 : Fin a.length)
    (j : Fin (a.length+1)) (r : ℕ) : ℕ :=
  if h : j.val < a.length then
    (if r = 0 then
      (if (⟨j.val, h⟩ : Fin a.length) ∈ S then a.length * shPre a S ⟨j.val, h⟩
       else a.length * b + 1 + a.length * shPre a Sᶜ ⟨j.val, h⟩)
     else
      (if (⟨j.val, h⟩ : Fin a.length) ∈ S then
        a.length * (shPre a S ⟨j.val, h⟩ + ga a ⟨j.val, h⟩)
       else a.length * a.sum + 1 + Gf a i0 ⟨j.val, h⟩))
  else (if r = 0 then a.length * b else a.length * b + 1)

lemma G_rev (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b) (hbA : b < a.sum)
    (S : Finset (Fin a.length)) (hS : ∑ j ∈ S, a.get j = b) :
    (constrG a b).HasScheduleLE (yG a) := by
  classical
  have hA := sh_sum_get a
  have hSc : ∑ j ∈ Sᶜ, a.get j = a.sum - b := by
    have := Finset.sum_compl_add_sum S (fun j => a.get j)
    omega
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h; simp at hS; omega
  obtain ⟨i0, hi0⟩ := hSne
  have hin : ∀ j : Fin a.length, j ∈ S → shPre a S j + a.get j ≤ b := by
    intro j hj; have := shPre_le a S j hj; omega
  have hout : ∀ j : Fin a.length, j ∉ S → shPre a Sᶜ j + a.get j ≤ a.sum - b := by
    intro j hj; have := shPre_le a Sᶜ j (by simpa using hj); omega
  have hapos : ∀ j : Fin a.length, 1 ≤ ga a j := fun j => ha _ (List.get_mem _ _)
  have hT1 : 1 ≤ a.length := by have := i0.isLt; omega
  have hTA : a.length * (a.sum - b) + a.length * b = a.length * a.sum := by
    rw [← mul_add]; congr 1; omega
  have hf : ∀ j : Fin a.length, j ∉ S → Gf a i0 j + 2 ≤ a.length := by
    intro j hj
    have hne : j ≠ i0 := fun h => hj (h ▸ hi0)
    have h1 := j.isLt; have h2 := i0.isLt
    have h3 : j.val ≠ i0.val := fun h => hne (Fin.ext h)
    unfold Gf; split_ifs <;> omega
  have hfinj : ∀ i j : Fin a.length, i ∉ S → j ∉ S → i ≠ j → Gf a i0 i ≠ Gf a i0 j := by
    intro i j hi hj hij
    have hne : i ≠ i0 := fun h => hi (h ▸ hi0)
    have hne' : j ≠ i0 := fun h => hj (h ▸ hi0)
    have h3 : i.val ≠ i0.val := fun h => hne (Fin.ext h)
    have h4 : j.val ≠ i0.val := fun h => hne' (Fin.ext h)
    have h5 : i.val ≠ j.val := fun h => hij (Fin.ext h)
    unfold Gf; split_ifs <;> omega
  have F1 : ∀ j : Fin a.length, j ∈ S → a.length * (shPre a S j + ga a j) ≤ a.length * b := by
    intro j hj; exact Nat.mul_le_mul_left a.length (hin j hj)
  have F2 : ∀ j : Fin a.length, j ∉ S →
      a.length * b + 1 + a.length * (shPre a Sᶜ j + ga a j) ≤ a.length * a.sum + 1 := by
    intro j hj
    have h := Nat.mul_le_mul_left a.length (hout j hj)
    have h' : a.length * (shPre a Sᶜ j + ga a j) ≤ a.length * (a.sum - b) := h
    linarith
  have hTa : ∀ j : Fin a.length, a.length ≤ a.length * ga a j := by
    intro j; nlinarith [hapos j]
  have hbA' : a.length * b ≤ a.length * a.sum := Nat.mul_le_mul_left _ hbA.le
  have step1 : ∀ i j : Fin a.length, i < j → i ∈ S →
      a.length * (shPre a S i + ga a i) ≤ a.length * shPre a S j := fun i j hij hi =>
    Nat.mul_le_mul_left _ (shPre_step a S i j hij hi)
  have step2 : ∀ i j : Fin a.length, i < j → i ∉ S →
      a.length * (shPre a Sᶜ i + ga a i) ≤ a.length * shPre a Sᶜ j := fun i j hij hi =>
    Nat.mul_le_mul_left _ (shPre_step a Sᶜ i j hij (by simpa using hi))
  refine ⟨fun o => Gs a b S i0 o.1 o.2.val, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o
    by_cases hj : o.1.val < a.length
    · simp [constrG, hj, Gs]
    · simp only [Gs, constrG, dif_neg hj]
      by_cases hr : o.2.val = 0 <;> simp [hr, hj]
  · intro j r r' hrr
    obtain ⟨hr2, hp, -⟩ := G_pm a b j r
    have hr2' := (G_pm a b j r').1
    have hk : r.val = 0 ∧ r'.val = 1 := by omega
    simp only [hp, Gp, Gs, hk.1, hk.2]
    by_cases hj : j.val < a.length
    · simp only [dif_pos hj]
      simp
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S
      · simp only [h1, if_true]; linarith [Nat.mul_add a.length (shPre a S ⟨j.val, hj⟩) (ga a ⟨j.val, hj⟩)]
      · simp only [h1, if_false]
        have := F2 _ h1
        have := hTa ⟨j.val, hj⟩
        linarith
    · simp [dif_neg hj]
  · intro o o' hne hm
    rcases o with ⟨j, r⟩
    rcases o' with ⟨j', r'⟩
    obtain ⟨hr2, hp, hmm⟩ := G_pm a b j r
    obtain ⟨hr2', hp', hmm'⟩ := G_pm a b j' r'
    rw [hmm, hmm'] at hm
    beta_reduce
    rw [hp, hp']
    have hk : r.val = 0 ∨ r.val = 1 := by omega
    have hk' : r'.val = 0 ∨ r'.val = 1 := by omega
    have hkk : r.val = r'.val := by
      rcases hk with h | h <;> rcases hk' with h' | h' <;> simp [Gm, h, h'] at hm ⊢
    by_cases hjj : j = j'
    · subst hjj
      have : r = r' := Fin.ext hkk
      subst this; exact absurd rfl hne
    simp only [← hkk]
    by_cases hj : j.val < a.length <;> by_cases hj' : j'.val < a.length
    · have hjj' : (⟨j.val, hj⟩ : Fin a.length) ≠ ⟨j'.val, hj'⟩ := by
        intro h; apply hjj; exact Fin.ext (by simpa using congrArg Fin.val h)
      simp only [Gp, Gs, dif_pos hj, dif_pos hj']
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
        by_cases h2 : (⟨j'.val, hj'⟩ : Fin a.length) ∈ S <;>
        rcases hk with h | h <;> simp only [h, h1, h2, ↓reduceIte, one_ne_zero]
      · rcases lt_or_gt_of_ne hjj' with hl | hl
        · left; have := step1 _ _ hl h1; linarith
        · right; have := step1 _ _ hl h2; linarith
      · rcases lt_or_gt_of_ne hjj' with hl | hl
        · left; have := step1 _ _ hl h1; have := hTa ⟨j'.val, hj'⟩; linarith
        · right; have := step1 _ _ hl h2; have := hTa ⟨j.val, hj⟩; linarith
      · left; have := F1 _ h1; have := Nat.zero_le (a.length * shPre a Sᶜ ⟨j'.val, hj'⟩); linarith
      · left; have := F1 _ h1; have := Nat.zero_le (a.length * Gf a i0 ⟨j'.val, hj'⟩); linarith
      · right; have := F1 _ h2; have := Nat.zero_le (a.length * shPre a Sᶜ ⟨j.val, hj⟩); linarith
      · right; have := F1 _ h2; linarith
      · rcases lt_or_gt_of_ne hjj' with hl | hl
        · left; have := step2 _ _ hl h1; linarith
        · right; have := step2 _ _ hl h2; linarith
      · have := hfinj _ _ h1 h2 hjj'
        rcases lt_or_gt_of_ne this with hl | hl
        · left; omega
        · right; omega
    · simp only [Gp, Gs, dif_pos hj, dif_neg hj']
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
        rcases hk with h | h <;> simp only [h, h1, ↓reduceIte, one_ne_zero]
      · left; have := F1 _ h1; linarith
      · left; have := F1 _ h1; linarith
      · right; have := Nat.zero_le (a.length * shPre a Sᶜ ⟨j.val, hj⟩); linarith
      · right; have := Nat.zero_le (a.length * Gf a i0 ⟨j.val, hj⟩); linarith
    · simp only [Gp, Gs, dif_pos hj', dif_neg hj]
      by_cases h2 : (⟨j'.val, hj'⟩ : Fin a.length) ∈ S <;>
        rcases hk with h | h <;> simp only [h, h2, ↓reduceIte, one_ne_zero]
      · right; have := F1 _ h2; linarith
      · right; have := F1 _ h2; linarith
      · left; have := Nat.zero_le (a.length * shPre a Sᶜ ⟨j'.val, hj'⟩); linarith
      · left; have := Nat.zero_le (a.length * Gf a i0 ⟨j'.val, hj'⟩); linarith
    · exfalso; apply hjj; apply Fin.ext; have := j.isLt; have := j'.isLt; omega
  · intro j k hjk; simp [constrG] at hjk
  · intro j
    apply sh_completion_le
    intro r
    obtain ⟨hr2, hp, -⟩ := G_pm a b j r
    rw [hp]
    have hk : r.val = 0 ∨ r.val = 1 := by omega
    unfold yG
    by_cases hj : j.val < a.length
    · simp only [Gp, Gs, dif_pos hj]
      by_cases h1 : (⟨j.val, hj⟩ : Fin a.length) ∈ S <;>
        rcases hk with h | h <;> simp only [h, h1, ↓reduceIte, one_ne_zero]
      · have := F1 _ h1; linarith
      · have := F1 _ h1; linarith
      · have := F2 _ h1; linarith
      · have := hf _ h1; linarith
    · simp only [Gp, Gs, dif_neg hj]
      rcases hk with h | h <;> simp only [h, ↓reduceIte, one_ne_zero]
      · linarith
      · linarith

theorem knapG_core_rev (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b) (hbA : b < a.sum)
    (h : SchedComplexity.OneMachine.KnapsackYes a b) : (constrG a b).HasScheduleLE (yG a) :=
  match h with | ⟨S, hS⟩ => G_rev a b ha hb hbA S hS

lemma G_arith (T A b x xc s1 s2 y : ℕ) (hT : 1 ≤ T) (hbA : b < A) (hsum : x + xc = A)
    (hrel : T * b ≤ s1) (c1 : s1 + 1 ≤ s2) (e1 : s2 + T * (A - b) ≤ y) (hy : y = T * A + T)
    (u1 : T * x ≤ s1) (u2 : T * xc + (s1 + 1) ≤ y - 1) : x = b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbA.le
  rw [Nat.add_sub_cancel_left] at e1
  have hy' : T * xc + s1 + 2 ≤ y := by omega
  have h1 : x ≤ b := by
    by_contra hcon
    have := Nat.mul_le_mul_left T (show b + 1 ≤ x by omega)
    nlinarith
  have h2 : b ≤ x := by
    by_contra hcon
    have := Nat.mul_le_mul_left T (show d + 1 ≤ xc by omega)
    nlinarith
  omega

def Glast (a : List ℕ) (b : ℕ) (k : Fin 2) : (constrG a b).Op :=
  ⟨Fin.last a.length, ⟨k.val, by rw [G_len a b]; exact k.isLt⟩⟩

def Gitem (a : List ℕ) (b : ℕ) (j : Fin a.length) (k : Fin 2) : (constrG a b).Op :=
  ⟨⟨j.val, by omega⟩, ⟨k.val, by rw [G_len a b]; exact k.isLt⟩⟩

lemma G_fwd (a : List ℕ) (b : ℕ) (hbA : b < a.sum)
    (h : (constrG a b).HasScheduleLE (yG a)) : SchedComplexity.OneMachine.KnapsackYes a b := by
  classical
  obtain ⟨S0, ⟨hrel, hchain, hmach, -⟩, hC⟩ := h
  have hA := sh_sum_get a
  have hT1 : 1 ≤ a.length := by
    rcases a with _ | ⟨x, l⟩
    · simp at hbA
    · simp
  have hTA : a.length * (a.sum - b) + a.length * b = a.length * a.sum := by
    rw [← mul_add]; congr 1; omega
  have hTpos : 1 ≤ a.length * (a.sum - b) := Nat.mul_pos hT1 (by omega)
  have hy : yG a = a.length * a.sum + a.length := by unfold yG; ring
  have pI0 : ∀ j : Fin a.length, (constrG a b).proc (Gitem a b j 0) = a.length * ga a j ∧
      (constrG a b).mach (Gitem a b j 0) = 0 := by
    intro j
    have := (G_pm a b _ (Gitem a b j 0).2).2
    simpa [Gp, Gm, Gitem, j.isLt] using this
  have pI1 : ∀ j : Fin a.length, (constrG a b).proc (Gitem a b j 1) = 1 ∧
      (constrG a b).mach (Gitem a b j 1) = 1 := by
    intro j
    have := (G_pm a b _ (Gitem a b j 1).2).2
    simpa [Gp, Gm, Gitem, j.isLt] using this
  have pL0 : (constrG a b).proc (Glast a b 0) = 1 ∧ (constrG a b).mach (Glast a b 0) = 0 := by
    have := (G_pm a b _ (Glast a b 0).2).2
    simpa [Gp, Gm, Glast] using this
  have pL1 : (constrG a b).proc (Glast a b 1) = a.length * (a.sum - b) ∧
      (constrG a b).mach (Glast a b 1) = 1 := by
    have := (G_pm a b _ (Glast a b 1).2).2
    simpa [Gp, Gm, Glast] using this
  have rel : a.length * b ≤ S0 (Glast a b 0) := by
    have := hrel (Glast a b 0)
    simpa [constrG, Glast] using this
  have c1 : S0 (Glast a b 0) + (constrG a b).proc (Glast a b 0) ≤ S0 (Glast a b 1) :=
    hchain (Fin.last a.length) (Glast a b 0).2 (Glast a b 1).2 (by simp [Glast])
  have e1 : S0 (Glast a b 1) + (constrG a b).proc (Glast a b 1) ≤ yG a :=
    le_trans (sh_le_completion _ S0 (Glast a b 1)) (hC (Fin.last a.length))
  rw [pL0.1] at c1
  rw [pL1.1] at e1
  have d1 : ∀ j : Fin a.length, S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Gitem a b j 1) := by
    intro j
    have := hchain ⟨j.val, by omega⟩ (Gitem a b j 0).2 (Gitem a b j 1).2 (by simp [Gitem])
    have e : S0 (Gitem a b j 0) + (constrG a b).proc (Gitem a b j 0) ≤ S0 (Gitem a b j 1) := this
    rw [(pI0 j).1] at e
    exact e
  have d2 : ∀ j : Fin a.length, S0 (Gitem a b j 1) + 1 ≤ yG a := by
    intro j
    have := le_trans (sh_le_completion _ S0 (Gitem a b j 1)) (hC (Gitem a b j 1).1)
    rw [(pI1 j).1] at this
    exact this
  have hL1 : ∀ j : Fin a.length, S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0) ∨
      S0 (Glast a b 0) + 1 ≤ S0 (Gitem a b j 0) := by
    intro j
    have hne : Gitem a b j 0 ≠ Glast a b 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Gitem, Glast] at this
      have := j.isLt; omega
    have := hmach _ _ hne (by rw [(pI0 j).2, pL0.2])
    rw [(pI0 j).1, pL0.1] at this
    exact this
  have hLL : ∀ j k : Fin a.length, j ≠ k →
      S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Gitem a b k 0) ∨
      S0 (Gitem a b k 0) + a.length * ga a k ≤ S0 (Gitem a b j 0) := by
    intro j k hjk
    have hne : Gitem a b j 0 ≠ Gitem a b k 0 := by
      intro h; have := congrArg (fun o => o.1.val) h; simp [Gitem] at this
      exact hjk (Fin.ext this)
    have := hmach _ _ hne (by rw [(pI0 j).2, (pI0 k).2])
    rw [(pI0 j).1, (pI0 k).1] at this
    exact this
  refine ⟨Finset.univ.filter (fun j => S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0)), ?_⟩
  have u1 := sh_sum_le (Finset.univ.filter
      (fun j => S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0)))
    (fun j => S0 (Gitem a b j 0)) (fun j => a.length * ga a j) 0 (S0 (Glast a b 0))
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega)
    (by intro i _ j _ hij; exact hLL i j hij)
  have u2 := sh_sum_le (Finset.univ.filter
      (fun j => ¬ (S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0))))
    (fun j => S0 (Gitem a b j 0)) (fun j => a.length * ga a j) (S0 (Glast a b 0) + 1) (yG a - 1)
    (by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have := d1 i; have := d2 i; have := hL1 i; omega)
    (by intro i _ j _ hij; exact hLL i j hij)
  have u3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin a.length))
    (fun j => S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0)) (fun j => ga a j)
  have hA' : ∑ j : Fin a.length, ga a j = a.sum := hA
  rw [← Finset.mul_sum] at u1 u2
  show ∑ j ∈ Finset.univ.filter
      (fun j => S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0)), ga a j = b
  generalize hx : ∑ j ∈ Finset.univ.filter
      (fun j => S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0)), ga a j = x at u1 u2 u3 ⊢
  generalize hxc : ∑ j ∈ Finset.univ.filter
      (fun j => ¬ (S0 (Gitem a b j 0) + a.length * ga a j ≤ S0 (Glast a b 0))), ga a j = xc
    at u1 u2 u3
  have hsum : x + xc = a.sum := by rw [← hA']; exact u3
  have u1' : a.length * x ≤ S0 (Glast a b 0) := by omega
  have u2' : a.length * xc + (S0 (Glast a b 0) + 1) ≤ yG a - 1 := by omega
  exact G_arith a.length a.sum b x xc _ _ _ hT1 hbA hsum rel c1 e1 hy u1' u2'

theorem knapG_core (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b) (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrG a b).HasScheduleLE (yG a) :=
  ⟨fun h => knapG_core_rev a b ha hb hbA h, G_fwd a b hbA⟩

end SchedComplexity.Shops

open SchedComplexity.Shops


theorem solution (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrG a b).HasScheduleLE (yG a) := by
  exact knapG_core a b ha hb hbA
