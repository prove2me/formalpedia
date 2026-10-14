-- Prove2me | solution 1 for WagelmansELS.DualGreedy.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:15:34.554684+00:00
-- url     : https://prove2.me/submissions/d1b560dd-82ec-4987-b05f-b0374aaf0847

import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Model



namespace WagelmansELS.DualGreedy

noncomputable def Rf (P : Instance) (j : ℕ) : ℕ → ℝ :=
  (Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun k hist =>
    fun t => if t = k + 1 then
      if k + 1 ≤ P.n then
        if P.d (k + 1) = 0 then hist k
        else (Finset.Icc 1 (k + 1)).inf' (by
          refine ⟨1, Finset.mem_Icc.mpr ?_⟩
          omega) (fun i => P.f i + P.c i * demand P i (k + 1) + hist (i - 1))
      else 0
    else hist t) j)

lemma F_eq_Rf (P : Instance) (j : ℕ) : F P j = Rf P j j := rfl

lemma Rf_succ_ne (P : Instance) (k t : ℕ) (h : t ≠ k + 1) : Rf P (k+1) t = Rf P k t := by
  show (if t = k + 1 then _ else _) = _
  rw [if_neg h]
  rfl

lemma Rf_hist (P : Instance) : ∀ k t, t ≤ k → Rf P k t = F P t := by
  intro k
  induction k with
  | zero =>
    intro t ht
    have : t = 0 := by omega
    subst this; rfl
  | succ k ih =>
    intro t ht
    rcases Nat.lt_or_ge t (k+1) with h | h
    · rw [Rf_succ_ne P k t (by omega), ih t (by omega)]
    · have : t = k + 1 := by omega
      subst this; rfl

lemma F_zero (P : Instance) : F P 0 = 0 := rfl

lemma F_succ_zero (P : Instance) (j : ℕ) (hj : j + 1 ≤ P.n) (h : P.d (j+1) = 0) :
    F P (j+1) = F P j := by
  have h1 : F P (j+1) = Rf P (j+1) (j+1) := rfl
  rw [h1]
  show (if j + 1 = j + 1 then _ else _) = _
  rw [if_pos rfl, if_pos hj, if_pos h]
  exact Rf_hist P j j le_rfl

lemma F_succ_pos (P : Instance) (j : ℕ) (hj : j + 1 ≤ P.n) (h : P.d (j+1) ≠ 0) :
    ∃ hne, F P (j+1) = (Finset.Icc 1 (j + 1)).inf' hne
      (fun i => P.f i + P.c i * demand P i (j + 1) + F P (i - 1)) := by
  refine ⟨⟨1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩, ?_⟩
  have h1 : F P (j+1) = Rf P (j+1) (j+1) := rfl
  rw [h1]
  show (if j + 1 = j + 1 then _ else _) = _
  rw [if_pos rfl, if_pos hj, if_neg h]
  apply Finset.inf'_congr _ rfl
  intro i hi
  have := (Finset.mem_Icc.mp hi)
  have h2 := Rf_hist P j (i-1) (by omega)
  show P.f i + P.c i * demand P i (j + 1) + Rf P j (i - 1) = _
  rw [h2]

lemma F_le_block (P : Instance) (j i : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j)
    (hi1 : 1 ≤ i) (hij : i ≤ j) :
    F P j ≤ P.f i + P.c i * demand P i j + F P (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hne, h⟩ := F_succ_pos P m hjn hdj.ne'
  rw [h]
  exact Finset.inf'_le (fun i => P.f i + P.c i * demand P i (m + 1) + F P (i - 1))
    (Finset.mem_Icc.mpr ⟨hi1, hij⟩)

lemma F_exists_block (P : Instance) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j) :
    ∃ i, 1 ≤ i ∧ i ≤ j ∧ F P j = P.f i + P.c i * demand P i j + F P (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hne, h⟩ := F_succ_pos P m hjn hdj.ne'
  obtain ⟨i, hi, hi2⟩ := Finset.exists_mem_eq_inf' hne
    (fun i => P.f i + P.c i * demand P i (m + 1) + F P (i - 1))
  have := Finset.mem_Icc.mp hi
  exact ⟨i, this.1, this.2, by rw [h, hi2]⟩

lemma objective_succ (P : Instance) (v : ℕ → ℝ) (j : ℕ) :
    objective P v (j+1) = objective P v j + P.d (j+1) * v (j+1) := by
  unfold objective
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma objective_split (P : Instance) (v : ℕ → ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j + 1) :
    objective P v j = objective P v (i - 1) + ∑ t ∈ Finset.Icc i j, P.d t * v t := by
  unfold objective
  have : Finset.Icc 1 j = Finset.Icc 1 (i-1) ∪ Finset.Icc i j := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  rw [this, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Icc] at hx hx'
  omega

lemma demand_nonneg (P : Instance) (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t) (i j : ℕ)
    (hi : 1 ≤ i) (hj : j ≤ P.n) : 0 ≤ demand P i j := by
  unfold demand
  apply Finset.sum_nonneg
  intro t ht
  have := Finset.mem_Icc.mp ht
  exact hd t (by omega) (by omega)

lemma weak_duality_core (P : Instance) (u : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hu : IsFeasible P u)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) :
    objective P u j ≤ F P j := by
  have main : ∀ j, j ≤ P.n → objective P u j ≤ F P j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjn
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [objective, F_zero]
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      by_cases h0 : P.d (m+1) = 0
      · rw [objective_succ, h0, F_succ_zero P m hjn h0]
        simpa using ih m (by omega) (by omega)
      · have hpos : 0 < P.d (m+1) := lt_of_le_of_ne (hd _ (by omega) hjn) (Ne.symm h0)
        obtain ⟨i, hi1, hij, hFi⟩ := F_exists_block P (m+1) (by omega) hjn hpos
        rw [hFi]
        have ih' := ih (i-1) (by omega) (by omega)
        rw [objective_split P u i (m+1) hi1 (by omega)]
        have hin : i ≤ P.n := by omega
        have hfeas := hu i hi1 hin
        have h1 : ∑ t ∈ Finset.Icc i (m+1), P.d t * u t ≤
            P.c i * demand P i (m+1) + P.f i := by
          have h2 : ∑ t ∈ Finset.Icc i (m+1), P.d t * u t ≤
              ∑ t ∈ Finset.Icc i (m+1), (P.d t * P.c i + P.d t * max 0 (u t - P.c i)) := by
            apply Finset.sum_le_sum
            intro t ht
            have : u t ≤ P.c i + max 0 (u t - P.c i) := by
              have := le_max_right 0 (u t - P.c i); linarith
            have htd := hd t (by have := Finset.mem_Icc.mp ht; omega)
              (by have := Finset.mem_Icc.mp ht; omega)
            nlinarith
          have h3 : ∑ t ∈ Finset.Icc i (m+1), (P.d t * P.c i + P.d t * max 0 (u t - P.c i))
              = P.c i * demand P i (m+1) + constraintUse P u i (m+1) := by
            rw [Finset.sum_add_distrib]
            unfold demand constraintUse
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl; intro t _; ring
          have h4 : constraintUse P u i (m+1) ≤ constraintUse P u i P.n := by
            unfold constraintUse
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht; simp only [Finset.mem_Icc] at ht ⊢; omega
            · intro t ht _
              have := Finset.mem_Icc.mp ht
              exact mul_nonneg (hd t (by omega) this.2) (le_max_left _ _)
          linarith
        linarith
  exact main j hjn

end WagelmansELS.DualGreedy

open WagelmansELS.DualGreedy


theorem solution (P : Instance) (u : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hu : IsFeasible P u)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) :
    objective P u j ≤ F P j := by
  exact weak_duality_core P u hd hf hu j hj1 hjn
