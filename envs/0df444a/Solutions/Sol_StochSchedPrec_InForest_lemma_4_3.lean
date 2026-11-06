-- Prove2me | solution 1 for StochSchedPrec.InForest.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:56:19.230019+00:00
-- url     : https://prove2.me/submissions/82a8d3f1-768a-4ecd-b3a8-0eeeedd60001

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Definitions.Def_StochSchedPrec_InForest_Graham

namespace StochSchedPrec.InForest.L43Aux

variable {V : Type*} [Fintype V]

lemma availTime_le_iff (A : V → V → Prop) (p S : V → ℝ) (j : V) (c : ℝ) :
    availTime A p S j ≤ c ↔ 0 ≤ c ∧ ∀ i, Relation.TransGen A i j → S i + p i ≤ c := by
  classical
  unfold availTime
  rw [Finset.fold_max_le]
  simp [Finset.mem_filter]

lemma le_availTime (A : V → V → Prop) (p S : V → ℝ) (j i : V) (h : Relation.TransGen A i j) :
    S i + p i ≤ availTime A p S j := by
  have := (availTime_le_iff A p S j (availTime A p S j)).mp le_rfl
  exact this.2 i h

lemma availTime_nonneg (A : V → V → Prop) (p S : V → ℝ) (j : V) :
    0 ≤ availTime A p S j :=
  ((availTime_le_iff A p S j (availTime A p S j)).mp le_rfl).1

lemma exists_attain (A : V → V → Prop) (p S : V → ℝ) (j : V) (h : 0 < availTime A p S j) :
    ∃ i, Relation.TransGen A i j ∧ S i + p i = availTime A p S j := by
  classical
  have h2 : availTime A p S j ≤ availTime A p S j := le_rfl
  unfold availTime at h2
  rw [Finset.le_fold_max] at h2
  rcases h2 with h2 | ⟨i, hi, hle⟩
  · exact absurd h (not_lt.mpr h2)
  · refine ⟨i, (Finset.mem_filter.mp hi).2, le_antisymm ?_ hle⟩
    exact le_availTime A p S j i (Finset.mem_filter.mp hi).2

/-- Completion times increase along paths of a feasible schedule. -/
lemma path_le (A : V → V → Prop) (m : ℕ) (p S : V → ℝ) (hp : IsNonneg p)
    (hS : IsFeasibleSchedule A m p S) {i j : V} (h : Relation.TransGen A i j) :
    S i + p i ≤ S j := by
  induction h with
  | single hab => exact hS.2.1 _ _ hab
  | @tail b c _ hbc ih =>
    have := hS.2.1 _ _ hbc
    have := hp b
    linarith

lemma exists_imm (A : V → V → Prop) (m : ℕ) (p S : V → ℝ) (hp : IsNonneg p)
    (hS : IsFeasibleSchedule A m p S) (x : V) (h : 0 < availTime A p S x) :
    ∃ y, A y x ∧ S y + p y = availTime A p S x := by
  obtain ⟨i, hi, hieq⟩ := exists_attain A p S x h
  rcases Relation.TransGen.tail'_iff.mp hi with ⟨y, hiy, hyx⟩
  refine ⟨y, hyx, le_antisymm (le_availTime A p S x y (Relation.TransGen.single hyx)) ?_⟩
  rw [← hieq]
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hiy with h' | h'
  · rw [h']
  · have := path_le A m p S hp hS h'
    have := hp y
    linarith

lemma availTime_le_start (A : V → V → Prop) (m : ℕ) (p S : V → ℝ) (hp : IsNonneg p)
    (hS : IsFeasibleSchedule A m p S) (x : V) : availTime A p S x ≤ S x :=
  (availTime_le_iff A p S x (S x)).mpr ⟨hS.1 x, fun i hi => path_le A m p S hp hS hi⟩

end StochSchedPrec.InForest.L43Aux

open StochSchedPrec.InForest StochSchedPrec.InForest.L43Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A) (hforest : IsInForest A)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsLinearExtension A L)
    (p : V → ℝ) (hp : IsNonneg p) (S : V → ℝ) (hS : IsGraham A m L p S)
    (j k : V) (hk : k ∈ Aset L j) (t : ℝ) (ht₁ : availTime A p S j ≤ t) (ht₂ : t < S j) :
    ¬ (S k ≤ t ∧ t < S k + p k) := by
  classical
  obtain ⟨hF, hgreedy, hlist, -⟩ := hS
  -- violators
  let Viol : V → Prop := fun x => ∃ k, L.symm x < L.symm k ∧ ∃ t, availTime A p S x ≤ t ∧
    t < S x ∧ S k ≤ t ∧ t < S k + p k
  suffices hno : ∀ x, ¬ Viol x by
    intro ⟨h1, h2⟩
    exact hno j ⟨k, by simpa [Aset] using hk, t, ht₁, ht₂, h1, h2⟩
  intro x0 hx0
  obtain ⟨j, hjV, hmin⟩ := (Finset.univ.filter Viol).exists_min_image S ⟨x0, by simp [hx0]⟩
  have hmin' : ∀ x, Viol x → S j ≤ S x := fun x hx => hmin x (by simp [hx])
  obtain ⟨k, hjk, t, ht₁, ht₂, hk₁, hk₂⟩ := (Finset.mem_filter.mp hjV).2
  clear hjV hmin x0 hx0
  set r := availTime A p S j with hr
  have hrle : ∀ i, Relation.TransGen A i j → S i + p i ≤ r := fun i hi => le_availTime A p S j i hi
  -- 1. k started before r
  have hSk : S k < r := by
    by_contra h
    push_neg at h
    have hav : IsAvailable A p S j (S k) := ⟨hF.1 k, fun i hi => (hrle i hi).trans h⟩
    have := hlist k j hav (lt_of_le_of_lt hk₁ ht₂)
    exact absurd hjk (not_lt.mpr this.le)
  have hr0 : 0 < r := lt_of_le_of_lt (hF.1 k) hSk
  have hkr : r < S k + p k := lt_of_le_of_lt ht₁ hk₂
  have hrSj : r < S j := lt_of_le_of_lt ht₁ ht₂
  have havail : IsAvailable A p S j r := ⟨hr0.le, hrle⟩
  have hbusy := hgreedy j r havail hrSj
  -- partition of the jobs in process at r
  set Old := Finset.univ.filter fun x => S x < r ∧ r < S x + p x with hOld
  set St := Finset.univ.filter fun x => S x = r ∧ 0 < p x with hSt
  have hB : (Finset.univ.filter fun x => S x ≤ r ∧ r < S x + p x) ⊆ Old ∪ St := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [hOld, hSt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_eq_of_le hx.1 with h | h
    · exact Or.inl ⟨h, hx.2⟩
    · right; refine ⟨h, ?_⟩; linarith [hx.2]
  have hbusy2 : m ≤ Old.card + St.card :=
    hbusy.trans ((Finset.card_le_card hB).trans (Finset.card_union_le _ _))
  -- jobs completing exactly at r, and jobs starting at r
  set D := Finset.univ.filter fun y => S y + p y = r with hD
  set N := insert j (Finset.univ.filter fun x => S x = r) with hN
  have hkey : ∀ x ∈ N, ∃ y, A y x ∧ S y + p y = r := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxj | hx
    · subst hxj
      exact exists_imm A m p S hp hF _ hr0
    · have hSx : S x = r := (Finset.mem_filter.mp hx).2
      have hxj : L.symm x < L.symm j := by
        apply hlist x j _ (by rw [hSx]; exact hrSj)
        rw [hSx]; exact havail
      have hax : availTime A p S x = r := by
        by_contra hne
        have hlt : availTime A p S x < r :=
          lt_of_le_of_ne (hSx ▸ availTime_le_start A m p S hp hF x) hne
        have hv : Viol x := by
          refine ⟨k, hxj.trans hjk, max (availTime A p S x) (S k), le_max_left _ _, ?_,
            le_max_right _ _, ?_⟩
          · rw [hSx]; exact max_lt hlt hSk
          · exact lt_of_lt_of_le (max_lt hlt hSk) hkr.le
        have := hmin' x hv
        linarith
      obtain ⟨y, hyx, hy⟩ := exists_imm A m p S hp hF x (by rw [hax]; exact hr0)
      exact ⟨y, hyx, hy.trans hax⟩
  choose! φ hφA hφC using hkey
  have hND : N.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn φ
    · intro x hx
      simp only [hD, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hφC x hx
    · intro x hx x' hx' he
      exact hforest _ _ _ (hφA x hx) (he ▸ hφA x' hx')
  set Dpos := D.filter fun y => 0 < p y with hDpos
  set Dz := D.filter fun y => ¬ 0 < p y with hDz
  have hDcard : Dpos.card + Dz.card = D.card := Finset.card_filter_add_card_filter_not _
  have hjSt : j ∉ St := by
    simp only [hSt, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; linarith
  have hjDz : j ∉ Dz := by
    simp only [hDz, hD, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; linarith [hp j]
  have hdisj : Disjoint St Dz := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [hSt, hDz, hD, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.2 h1.2
  have hsub : insert j (St ∪ Dz) ⊆ N := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp h with h | h
      · simp only [hSt, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
      · simp only [hDz, hD, Finset.mem_filter, Finset.mem_univ, true_and] at h
        have := hp x
        have : p x = 0 := le_antisymm (not_lt.mp h.2) this
        linarith [h.1]
  have hcard1 : St.card + Dz.card + 1 ≤ N.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hjSt, hjDz]),
      Finset.card_union_of_disjoint hdisj] at this
    exact this
  have hDpos1 : St.card + 1 ≤ Dpos.card := by omega
  -- a time just before r
  have hne : (Old ∪ Dpos).Nonempty := by
    have : 0 < Dpos.card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp this
    exact ⟨y, Finset.mem_union_right _ hy⟩
  have hlt_r : ∀ x ∈ Old ∪ Dpos, S x < r := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.mem_filter.mp h).2.1
    · simp only [hDpos, hD, Finset.mem_filter, Finset.mem_univ, true_and] at h
      linarith [h.1, h.2]
  have hend : ∀ x ∈ Old ∪ Dpos, r ≤ S x + p x := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.mem_filter.mp h).2.2.le
    · simp only [hDpos, hD, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.1.ge
  set τ := (Old ∪ Dpos).sup' hne S with hτ
  have hτr : τ < r := (Finset.sup'_lt_iff hne).mpr hlt_r
  have hsub2 : Old ∪ Dpos ⊆ Finset.univ.filter fun x => S x ≤ τ ∧ τ < S x + p x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.le_sup' S hx, lt_of_lt_of_le hτr (hend x hx)⟩
  have hdisj2 : Disjoint Old Dpos := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [hOld, hDpos, hD, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    linarith [h1.2, h2.1]
  have hcap := hF.2.2 τ
  have := Finset.card_le_card hsub2
  rw [Finset.card_union_of_disjoint hdisj2] at this
  omega
