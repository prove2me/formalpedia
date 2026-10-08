-- Prove2me | solution 1 for ProjSchedTW.DelayingModes.two_element_forbidden_set_precedence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:03:41.747789+00:00
-- url     : https://prove2.me/submissions/d454d600-940c-411a-aa3e-0825592f6a56

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project
import Definitions.Def_ProjSchedTW_DelayingModes_Distance

set_option autoImplicit false

open ProjSchedTW.DelayingModes in
theorem tef9f_path_le {n : ℕ} (A : Finset (Fin (n + 2) × Fin (n + 2)))
    (w : Fin (n + 2) → Fin (n + 2) → ℤ) (S : Fin (n + 2) → ℝ)
    (hA : ∀ e ∈ A, ((w e.1 e.2 : ℤ) : ℝ) ≤ S e.2 - S e.1)
    (a b : Fin (n + 2)) (Q : SimplePath n) (hQ : Q.IsFromTo A a b) :
    ((Q.length w : ℤ) : ℝ) ≤ S b - S a := by
  obtain ⟨h0, hl, harc⟩ := hQ
  obtain ⟨m, v⟩ := Q
  simp only at h0 hl harc
  let g : ℕ → ℝ := fun l => if h : l < m.1 + 1 then S (v ⟨l, h⟩) else 0
  have key : ∀ l : Fin m.1, S (v l.succ) - S (v l.castSucc) = g (l.1 + 1) - g l.1 := by
    intro l
    simp only [g, dif_pos (Nat.succ_lt_succ l.2), dif_pos (Nat.lt_succ_of_lt l.2)]
    rfl
  have htel : ∑ l : Fin m.1, (S (v l.succ) - S (v l.castSucc)) = S b - S a := by
    rw [Finset.sum_congr rfl (fun l _ => key l)]
    rw [Fin.sum_univ_eq_sum_range (fun l => g (l + 1) - g l) m.1, Finset.sum_range_sub]
    simp only [g, dif_pos (Nat.lt_succ_self m.1), dif_pos (Nat.succ_pos m.1)]
    rw [← hl, ← h0]
    rfl
  unfold SimplePath.length
  push_cast
  rw [← htel]
  exact Finset.sum_le_sum (fun l _ => hA _ (harc l))

open ProjSchedTW.DelayingModes in
theorem tef9f_dist_le {n : ℕ} {K : Type} [Fintype K] (P : Project n K) (UB : ℤ)
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB)
    (a b : Fin (n + 2)) : P.distPlus UB a b ≤ (((S b - S a : ℝ)) : WithBot ℝ) := by
  classical
  have hA : ∀ e ∈ P.plusArcs, (((P.plusWeight UB) e.1 e.2 : ℤ) : ℝ) ≤ S e.2 - S e.1 := by
    intro e he
    obtain ⟨⟨⟨hS0, _⟩, hT⟩, _⟩ := hS
    unfold Project.plusWeight
    by_cases hc : e.1 = Fin.last (n + 1) ∧ e.2 = 0
    · rw [if_pos hc]
      have hb : (-(UB : ℝ)) ≤ S e.2 - S e.1 := by
        rw [hc.1, hc.2, hS0]; linarith
      split_ifs with hE
      · have h1 := hT _ hE
        push_cast
        exact max_le (by rw [hc.1, hc.2]; exact h1) hb
      · push_cast; exact hb
    · rw [if_neg hc]
      unfold Project.plusArcs at he
      rcases Finset.mem_insert.mp he with h | h
      · exact absurd (by rw [h]; exact ⟨rfl, rfl⟩) hc
      · exact hT e h
  unfold Project.distPlus longestPathLength
  apply Finset.sup_le
  intro Q hQ
  rw [Finset.mem_filter] at hQ
  exact WithBot.coe_le_coe.mpr (tef9f_path_le _ _ S hA a b Q hQ.2)

open ProjSchedTW.DelayingModes in
theorem solution {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (UB : ℤ) (i j : Fin (n + 2)) (hij : i ≠ j)
    (hF : P.IsForbidden {i, j})
    (hlt : P.distPlus UB i j < (((P.p i : ℝ)) : WithBot ℝ))
    (hgt : ((-(P.p j : ℝ) : ℝ) : WithBot ℝ) < P.distPlus UB i j)
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB) :
    S i + P.p i ≤ S j := by
  obtain ⟨_, _, _, hpos, _, hr0, hrR, _, _⟩ := hP
  obtain ⟨k, hk⟩ := hF
  rw [Finset.sum_pair hij] at hk
  have hri : 0 < P.r i k := by have := hrR j k; omega
  have hrj : 0 < P.r j k := by have := hrR i k; omega
  have hpi : (0 : ℝ) < P.p i := by
    have : i ≠ 0 := by rintro rfl; rw [(hr0 k).1] at hri; omega
    have : i ≠ Fin.last (n + 1) := by rintro rfl; rw [(hr0 k).2] at hri; omega
    exact_mod_cast hpos i (by assumption) (by assumption)
  have hpj : (0 : ℝ) < P.p j := by
    have : j ≠ 0 := by rintro rfl; rw [(hr0 k).1] at hrj; omega
    have : j ≠ Fin.last (n + 1) := by rintro rfl; rw [(hr0 k).2] at hrj; omega
    exact_mod_cast hpos j (by assumption) (by assumption)
  have hd := tef9f_dist_le P UB S hS hUB i j
  have h2 : (-(P.p j : ℝ)) < S j - S i := by
    have := lt_of_lt_of_le hgt hd
    exact WithBot.coe_lt_coe.mp this
  by_contra hcon
  push Not at hcon
  -- overlap at t = max (S i) (S j)
  obtain ⟨⟨⟨_, hnn⟩, _⟩, ⟨_, hres⟩⟩ := hS
  set t := max (S i) (S j) with ht
  have hsub : ({i, j} : Finset (Fin (n + 2))) ⊆ P.activeSet S t := by
    intro x hx
    unfold Project.activeSet
    rw [Finset.mem_filter]
    rcases Finset.mem_insert.mp hx with h | h
    · subst h
      refine ⟨Finset.mem_univ _, le_max_left _ _, ?_⟩
      exact max_lt (by linarith) hcon
    · rw [Finset.mem_singleton] at h; subst h
      refine ⟨Finset.mem_univ _, le_max_right _ _, ?_⟩
      exact max_lt (by linarith) (by linarith)
  have hu := hres t (le_trans (hnn i) (le_max_left _ _)) k
  have hmono := Finset.sum_le_sum_of_subset (f := fun x => P.r x k) hsub
  rw [Finset.sum_pair hij] at hmono
  unfold Project.usage at hu
  omega
