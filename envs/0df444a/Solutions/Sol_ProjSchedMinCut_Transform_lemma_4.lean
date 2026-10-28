-- Prove2me | solution 1 for ProjSchedMinCut.Transform.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:49:02.80039+00:00
-- url     : https://prove2.me/submissions/528d9df9-fbd4-46a4-b142-01a247945525

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_ProjSchedMinCut_Transform_Setting
import Theorems.Thm_ProjSchedMinCut_Transform_lemma_1
import Theorems.Thm_ProjSchedMinCut_Transform_lemma_2
import Theorems.Thm_ProjSchedMinCut_Transform_lemma_3

open ProjSchedMinCut.Transform
open ProjSchedMinCut.Transform.Instance
open scoped ENNReal

private lemma finset_exists_min {α : Type*} [LinearOrder α] (U : Finset α) (hU : U.Nonempty) :
    ∃ m ∈ U, ∀ x ∈ U, m ≤ x := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    rcases hU with ⟨x, hx⟩
    simp at hx
  | @insert a s _ ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · refine ⟨a, Finset.mem_singleton_self a, ?_⟩
      intro x hx
      rw [Finset.mem_singleton.mp hx]
    · obtain ⟨m, hm, hle⟩ := ih hs
      rcases le_total a m with ham | hma
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact le_rfl
        · exact le_trans ham (hle x hxs)
      · refine ⟨m, Finset.mem_insert_of_mem hm, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact hma
        · exact hle x hxs

private lemma finset_sum_ite_eq (A : Finset ℕ) (a : ℕ) :
    (∑ s ∈ A, (if s = a then (1 : ℤ) else 0)) = if a ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs, ih]
    by_cases hba : b = a
    · subst hba
      simp [hbs]
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]

private lemma exists_minCut {n : ℕ} (I : Instance n) : ∃ X, I.IsMinCut X := by
  classical
  let U : Finset ℝ≥0∞ :=
    (I.A.powerset.image (fun F => ∑ α ∈ F, I.cap α)).filter (fun c => ∃ X, I.IsCut X ∧ I.cutCap X = c)
  have hmem_U : ∀ Y, I.IsCut Y → I.cutCap Y ∈ U := by
    intro Y hY
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨I.A.filter (fun α => I.InCut Y α), ?_, rfl⟩, ⟨Y, hY, rfl⟩⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have ha_cut : I.IsCut ({Node.a} : Set (Node n)) := by
    refine ⟨?_, Set.mem_singleton Node.a, by simp⟩
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact Or.inl (Or.inl rfl)
  have hU_ne : U.Nonempty := ⟨I.cutCap {Node.a}, hmem_U {Node.a} ha_cut⟩
  obtain ⟨m, hm_mem, hm_le⟩ := finset_exists_min U hU_ne
  obtain ⟨_, ⟨X₀, hX₀_cut, hX₀_eq⟩⟩ := Finset.mem_filter.mp hm_mem
  refine ⟨X₀, hX₀_cut, ?_⟩
  intro Y hY
  rw [hX₀_eq]
  exact hm_le (I.cutCap Y) (hmem_U Y hY)

private lemma ipFeasible_of_feasible {n : ℕ} (I : Instance n) {S : Fin (n + 1) → ℤ}
    (hS : I.Feasible S) :
    I.IPFeasible (fun j (t : ℕ) => if (t : ℤ) = S j then 1 else 0) := by
  have hbddBelow : ∀ j, BddBelow (I.startTimes j) := by
    intro j
    refine ⟨0, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 j).1
  have hbddAbove : ∀ j, BddAbove (I.startTimes j) := by
    intro j
    refine ⟨I.T, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  have hearliest_le : ∀ j, I.earliest j ≤ S j :=
    fun j => csInf_le (hbddBelow j) ⟨S, hS, rfl⟩
  have hle_latest : ∀ j, S j ≤ I.latest j :=
    fun j => le_csSup (hbddAbove j) ⟨S, hS, rfl⟩
  have hS_nonneg : ∀ j, 0 ≤ S j := fun j => (hS.2 j).1
  have hS_le_T : ∀ j, S j ≤ I.T := by
    intro j
    have h1 := (hS.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  have hsum_eq : ∀ j (A : Finset ℕ),
      (∑ s ∈ A, (if (s : ℤ) = S j then (1 : ℤ) else 0)) =
        if (S j).toNat ∈ A then 1 else 0 := by
    intro j A
    have hiff : ∀ s : ℕ, ((s : ℤ) = S j) ↔ s = (S j).toNat := by
      intro s
      have h0 := hS_nonneg j
      omega
    simp_rw [hiff]
    exact finset_sum_ite_eq A (S j).toNat
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rw [hsum_eq, if_pos]
    rw [Finset.mem_range]
    have h0 := hS_nonneg j
    have hT := hS_le_T j
    omega
  · intro ij hij t _
    rw [hsum_eq, hsum_eq]
    split_ifs with h1 h2
    · exfalso
      rw [Finset.mem_Icc] at h1
      rw [Finset.mem_range] at h2
      have h0_1 := hS_nonneg ij.1
      have h0_2 := hS_nonneg ij.2
      have hlag := hS.1 ij hij
      omega
    · omega
    · omega
    · omega
  · intro j t _
    dsimp only
    split_ifs <;> omega
  · intro j t ht
    dsimp only
    have he := hearliest_le j
    have hl := hle_latest j
    rw [if_neg]
    omega

private lemma cost_nonneg {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    {y : Fin (n + 1) → ℕ → ℤ} (hy : I.IPFeasible y) : 0 ≤ I.cost y := by
  unfold Instance.cost
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun t ht => ?_
  have hy_nonneg : (0 : ℝ) ≤ (y j t : ℝ) := by exact_mod_cast hy.2.2.1 j t ht
  exact mul_nonneg (hw j t) hy_nonneg

theorem solution {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    (∃ X, I.IsMinCut X) ∧
      ∀ X, I.IsMinCut X → ∃ x, I.IsOptimal x ∧ I.cutCap X = ENNReal.ofReal (I.cost x) := by
  refine ⟨exists_minCut I, ?_⟩
  intro X hX
  rcases hfeas with ⟨S, hS⟩
  have hfeas' : ∃ S, I.Feasible S := ⟨S, hS⟩
  have hx₀ : I.IPFeasible (fun j (t : ℕ) => if (t : ℤ) = S j then 1 else 0) :=
    ipFeasible_of_feasible I hS
  obtain ⟨X₀, hX₀_ncut, hX₀_cap, _, _⟩ := lemma_2 I hw hfeas' _ hx₀
  obtain ⟨Xs, hXs_ncut, hXs_cap⟩ := lemma_1 I hw hfeas' X hX
  have hXs_lt_top : I.cutCap Xs < ⊤ := by
    rw [hXs_cap]
    exact lt_of_le_of_lt (hX.2 X₀ hX₀_ncut.1) hX₀_cap
  obtain ⟨hx_feas, hx_cap⟩ := lemma_3 I hw hfeas' Xs hXs_ncut hXs_lt_top
  refine ⟨I.xOfCut Xs, ⟨hx_feas, ?_⟩, ?_⟩
  · intro y hy
    obtain ⟨Y, hY_ncut, _, _, hY_cap⟩ := lemma_2 I hw hfeas' y hy
    have hle : ENNReal.ofReal (I.cost (I.xOfCut Xs)) ≤ ENNReal.ofReal (I.cost y) := by
      rw [← hx_cap, hXs_cap, ← hY_cap]
      exact hX.2 Y hY_ncut.1
    exact (ENNReal.ofReal_le_ofReal_iff (cost_nonneg I hw hy)).mp hle
  · rw [← hXs_cap, hx_cap]
