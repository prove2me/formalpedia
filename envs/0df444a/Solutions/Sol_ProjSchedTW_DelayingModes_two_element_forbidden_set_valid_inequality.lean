-- Prove2me | solution 1 for ProjSchedTW.DelayingModes.two_element_forbidden_set_valid_inequality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T20:12:13.444883+00:00
-- url     : https://prove2.me/submissions/b8b3df90-1f24-417d-adcd-9d43a4f29f24

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project
import Definitions.Def_ProjSchedTW_DelayingModes_Distance

open ProjSchedTW.DelayingModes

private lemma sum_fin_succ_sub_castSucc :
    ∀ (m : ℕ) (g : Fin (m + 1) → ℝ),
      (∑ l : Fin m, (g l.succ - g l.castSucc)) = g (Fin.last m) - g 0
  | 0, g => by simp
  | m + 1, g => by
    rw [Fin.sum_univ_castSucc]
    have ih := sum_fin_succ_sub_castSucc m (fun k : Fin (m + 1) => g k.castSucc)
    have hstep :
        (∑ l : Fin m, (g l.castSucc.succ - g l.castSucc.castSucc)) =
          ∑ l : Fin m, (g l.succ.castSucc - g l.castSucc.castSucc) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Fin.succ_castSucc]
    rw [hstep, ih]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring

private lemma plusWeight_le_sub {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (UB : ℤ) (S : Fin (n + 2) → ℝ)
    (hTF : P.IsTimeFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB)
    {a b : Fin (n + 2)} (hab : (a, b) ∈ P.plusArcs) :
    (P.plusWeight UB a b : ℝ) ≤ S b - S a := by
  unfold Project.plusArcs at hab
  unfold Project.plusWeight
  have hS0 : S 0 = 0 := hTF.1.1
  split_ifs with h1 h2
  · rcases h1 with ⟨ rfl, rfl ⟩
    push_cast
    refine max_le ?_ ?_
    · exact hTF.2 (Fin.last (n + 1), 0) h2
    · linarith
  · rcases h1 with ⟨ rfl, rfl ⟩
    push_cast
    linarith
  · rw [Finset.mem_insert] at hab
    rcases hab with hab | hab
    · exfalso
      apply h1
      exact ⟨Prod.mk.inj hab |>.1, Prod.mk.inj hab |>.2⟩
    · exact hTF.2 (a, b) hab

private lemma distPlus_le_sub {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (UB : ℤ) (S : Fin (n + 2) → ℝ)
    (hTF : P.IsTimeFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB)
    (u v : Fin (n + 2)) :
    P.distPlus UB u v ≤ ((S v - S u : ℝ) : WithBot ℝ) := by
  classical
  unfold Project.distPlus longestPathLength
  refine Finset.sup_le fun Q hQ => ?_
  rw [Finset.mem_filter] at hQ
  rcases hQ.2 with ⟨hQ0, hQlast, hQarcs⟩
  rw [WithBot.coe_le_coe]
  unfold SimplePath.length
  push_cast
  have hle :
      (∑ l : Fin Q.1.1, (P.plusWeight UB (Q.2 l.castSucc) (Q.2 l.succ) : ℝ)) ≤
        ∑ l : Fin Q.1.1, (S (Q.2 l.succ) - S (Q.2 l.castSucc)) := by
    refine Finset.sum_le_sum fun l _ => ?_
    exact plusWeight_le_sub P UB S hTF hUB (hQarcs l)
  rw [sum_fin_succ_sub_castSucc Q.1.1 (fun k => S (Q.2 k)), hQ0, hQlast] at hle
  exact hle

private lemma forbidden_pair_disjoint_execution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (i j : Fin (n + 2)) (hij : i ≠ j)
    (hF : P.IsForbidden {i, j}) (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) :
    S i + P.p i ≤ S j ∨ S j + P.p j ≤ S i := by
  rcases hP with ⟨_, hp0, hplast, hppos, _, hr0, hrle, _, _⟩
  have hpi : 0 < P.p i := by
    by_contra hle
    have hzero : i = 0 ∨ i = Fin.last (n + 1) := by
      by_contra hne
      push_neg at hne
      exact hle (hppos i hne.1 hne.2)
    have hri : ∀ k, P.r i k = 0 := by
      intro k
      rcases hzero with rfl | rfl
      · exact (hr0 k).1
      · exact (hr0 k).2
    rcases hF with ⟨k, hk⟩
    rw [Finset.sum_pair hij, hri k, zero_add] at hk
    exact not_lt_of_ge (hrle j k) hk
  have hpj : 0 < P.p j := by
    by_contra hle
    have hzero : j = 0 ∨ j = Fin.last (n + 1) := by
      by_contra hne
      push_neg at hne
      exact hle (hppos j hne.1 hne.2)
    have hrj : ∀ k, P.r j k = 0 := by
      intro k
      rcases hzero with rfl | rfl
      · exact (hr0 k).1
      · exact (hr0 k).2
    rcases hF with ⟨k, hk⟩
    rw [Finset.sum_pair hij, hrj k, add_zero] at hk
    exact not_lt_of_ge (hrle i k) hk
  by_contra hnot
  push_neg at hnot
  rcases hnot with ⟨hj, hi⟩
  let t : ℝ := max (S i) (S j)
  have ht0 : 0 ≤ t := le_trans (hS.1.1.2 i) (le_max_left _ _)
  have hi_act : i ∈ P.activeSet S t := by
    unfold Project.activeSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, le_max_left _ _, max_lt ?_ hj⟩
    have : (0 : ℝ) < P.p i := Nat.cast_pos.mpr hpi
    linarith
  have hj_act : j ∈ P.activeSet S t := by
    unfold Project.activeSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, le_max_right _ _, max_lt hi ?_⟩
    have : (0 : ℝ) < P.p j := Nat.cast_pos.mpr hpj
    linarith
  have hsub : ({i, j} : Finset (Fin (n + 2))) ⊆ P.activeSet S t := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi_act
    · exact hj_act
  rcases hF with ⟨k, hk⟩
  have husage := hS.2.2 t ht0 k
  unfold Project.usage at husage
  have hsum_le : ∑ x ∈ ({i, j} : Finset (Fin (n + 2))), P.r x k ≤ P.R k :=
    le_trans (Finset.sum_le_sum_of_subset hsub) husage
  exact not_lt_of_ge hsum_le hk

private lemma withBot_add3_le {a b c a' b' c' d : ℝ}
    (ha : (a : WithBot ℝ) ≤ a') (hb : (b : WithBot ℝ) ≤ b') (hc : (c : WithBot ℝ) ≤ c')
    (hsum : a' + b' + c' ≤ d) :
    (a : WithBot ℝ) + (b : WithBot ℝ) + (c : WithBot ℝ) ≤ (d : WithBot ℝ) := by
  have h1 : (a : WithBot ℝ) + (b : WithBot ℝ) ≤ (a' : WithBot ℝ) + (b' : WithBot ℝ) :=
    add_le_add ha hb
  have h2 : (a : WithBot ℝ) + (b : WithBot ℝ) + (c : WithBot ℝ) ≤
      (a' : WithBot ℝ) + (b' : WithBot ℝ) + (c' : WithBot ℝ) :=
    add_le_add h1 hc
  refine le_trans h2 ?_
  rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact hsum

theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (UB : ℤ) (i j : Fin (n + 2)) (hij : i ≠ j)
    (hF : P.IsForbidden {i, j})
    (hij_not : ¬ (((-(P.p j : ℝ) : ℝ) : WithBot ℝ) < P.distPlus UB i j))
    (hji_not : ¬ (((-(P.p i : ℝ) : ℝ) : WithBot ℝ) < P.distPlus UB j i))
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB)
    (h l : Fin (n + 2)) :
    min (P.distPlus UB h i + ((P.p i : ℝ) : WithBot ℝ) + P.distPlus UB j l)
        (P.distPlus UB h j + ((P.p j : ℝ) : WithBot ℝ) + P.distPlus UB i l)
      ≤ ((S l - S h : ℝ) : WithBot ℝ) := by
  have hhi := distPlus_le_sub P UB S hS.1 hUB h i
  have hjl := distPlus_le_sub P UB S hS.1 hUB j l
  have hhj := distPlus_le_sub P UB S hS.1 hUB h j
  have hil := distPlus_le_sub P UB S hS.1 hUB i l
  rcases forbidden_pair_disjoint_execution P hP i j hij hF S hS with hij_ord | hji_ord
  · refine le_trans (min_le_left _ _) ?_
    have h1 : P.distPlus UB h i + ((P.p i : ℝ) : WithBot ℝ) ≤
        ((S i - S h : ℝ) : WithBot ℝ) + ((P.p i : ℝ) : WithBot ℝ) :=
      add_le_add hhi le_rfl
    have h2 : P.distPlus UB h i + ((P.p i : ℝ) : WithBot ℝ) + P.distPlus UB j l ≤
        (((S i - S h : ℝ) : WithBot ℝ) + ((P.p i : ℝ) : WithBot ℝ)) +
          ((S l - S j : ℝ) : WithBot ℝ) :=
      add_le_add h1 hjl
    refine le_trans h2 ?_
    rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
    linarith
  · refine le_trans (min_le_right _ _) ?_
    have h1 : P.distPlus UB h j + ((P.p j : ℝ) : WithBot ℝ) ≤
        ((S j - S h : ℝ) : WithBot ℝ) + ((P.p j : ℝ) : WithBot ℝ) :=
      add_le_add hhj le_rfl
    have h2 : P.distPlus UB h j + ((P.p j : ℝ) : WithBot ℝ) + P.distPlus UB i l ≤
        (((S j - S h : ℝ) : WithBot ℝ) + ((P.p j : ℝ) : WithBot ℝ)) +
          ((S l - S i : ℝ) : WithBot ℝ) :=
      add_le_add h1 hil
    refine le_trans h2 ?_
    rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
    linarith
