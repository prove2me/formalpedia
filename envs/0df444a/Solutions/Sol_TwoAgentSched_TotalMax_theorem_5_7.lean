-- Prove2me | solution 1 for TwoAgentSched.TotalMax.theorem_5_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:24:08.057969+00:00
-- url     : https://prove2.me/submissions/e64b00ff-d0d1-4c59-90e8-534aefa56085

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_TotalMax_Rules
import Theorems.Thm_TwoAgentSched_TotalMax_theorem_5_5

set_option autoImplicit false
open TwoAgentSched.TotalMax TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma ttm57_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma ttm57_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact ttm57_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma ttm57_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma ttm57_ct_append_right (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime p (l₁ ++ l₂) x = (l₁.map p).sum + completionTime p l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx, List.take_append]
  have e1 : l₁.take (l₁.length + l₂.idxOf x + 1) = l₁ := List.take_of_length_le (by omega)
  have e3 : l₁.length + l₂.idxOf x + 1 - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e3]
  simp

lemma ttm57_ct_cons_ne (y : ι) (R : List ι) (x : ι) (hx : x ≠ y) :
    completionTime p (y :: R) x = p y + completionTime p R x := by
  unfold completionTime completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hx)]
  simp [List.take_succ_cons]

lemma ttm57_ct_cons_self (y : ι) (R : List ι) :
    completionTime p (y :: R) y = p y := by
  unfold completionTime completionAt
  simp

lemma ttm57_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hz
  have hza : z ∉ a := fun h => (List.nodup_append.1 hnd).2.2 z h z (by simp) rfl
  have herase : (a ++ z :: b).erase z = a ++ b := by
    rw [List.erase_append_right _ hza]; simp
  rw [herase]
  have hx' : x ∈ a ∨ x ∈ b := by
    rcases List.mem_append.1 hx with h | h
    · exact Or.inl h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h hxz
      · exact Or.inr h
  rcases hx' with hxa | hxb
  · rw [ttm57_ct_append_left p a b x hxa, ttm57_ct_append_left p a (z :: b) x hxa]
  · have hxa : x ∉ a := fun h => (List.nodup_append.1 hnd).2.2 x h x (by simp [hxb]) rfl
    unfold completionTime completionAt
    rw [List.idxOf_append_of_notMem hxa, List.idxOf_append_of_notMem hxa,
      List.idxOf_cons_ne _ (Ne.symm hxz)]
    rw [List.take_append, List.take_append]
    have e1 : a.take (a.length + List.idxOf x b + 1) = a := List.take_of_length_le (by omega)
    have e2 : a.take (a.length + (List.idxOf x b).succ + 1) = a :=
      List.take_of_length_le (by omega)
    rw [e1, e2]
    have e3 : a.length + List.idxOf x b + 1 - a.length = List.idxOf x b + 1 := by omega
    have e4 : a.length + (List.idxOf x b).succ + 1 - a.length = List.idxOf x b + 1 + 1 := by omega
    rw [e3, e4]
    simp only [List.take_succ_cons, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    linarith [hp z]

lemma ttm57_erase_ex (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z : ι) (hz : z ∈ l) :
    ∃ l'', l.Perm (l'' ++ [z]) ∧
      ∀ x ∈ l'', x ∈ l ∧ x ≠ z ∧ completionTime p l'' x ≤ completionTime p l x := by
  refine ⟨l.erase z, ?_, fun x hx => ?_⟩
  · exact (List.perm_cons_erase hz).trans (List.perm_append_singleton z _).symm
  · rw [hnd.mem_erase_iff] at hx
    exact ⟨hx.2, hx.1, ttm57_ct_erase_le p hp l hnd z x hz hx.2 hx.1⟩

end generic

local instance (priority := high) ttm57BEq {nA nB : ℕ} : BEq (Job nA nB) := instBEqOfDecidableEq

def ttm57LastOK {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ)
    (Q : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) : Prop :=
  ((∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
      ∃ k : Fin nB, z = Sum.inr k ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) ∧
    ((¬ ∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
      ∃ h : Fin nA, z = Sum.inl h ∧
        ∀ h' : Fin nA, Sum.inl h' ∈ (σ ++ [z]).toFinset →
          p (Sum.inl h') ≤ p (Sum.inl h))

def ttm57LeastLastOK {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ)
    (Q : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) : Prop :=
  ((∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
      ∃ k : Fin nB, z = Sum.inr k ∧
        ∀ k' : Fin nB, Sum.inr k' ∈ (σ ++ [z]).toFinset →
          fB k ((σ ++ [z]).map p).sum ≤ fB k' ((σ ++ [z]).map p).sum) ∧
    ((¬ ∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
      ∃ h : Fin nA, z = Sum.inl h ∧
        ∀ h' : Fin nA, Sum.inl h' ∈ (σ ++ [z]).toFinset →
          p (Sum.inl h') ≤ p (Sum.inl h))

lemma isFig1_of_leastCost {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (Job nA nB)) (hrule : IsLeastCostSeq p fB Q l) : IsFig1Seq p fB Q l := by
  intro m hm
  obtain ⟨h1, h2⟩ := hrule m hm
  refine ⟨fun hex => ?_, h2⟩
  obtain ⟨k0, hk0_mem, hk0_le⟩ := hex
  obtain ⟨k, hk_eq, hmin⟩ := h1 ⟨k0, hk0_mem, hk0_le⟩
  exact ⟨k, hk_eq, (hmin k0 hk0_mem).trans hk0_le⟩

lemma ttm57_rule_append_iff {nA nB : ℕ} (p : Job nA nB → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) :
    IsFig1Seq p fB Q (σ ++ [z]) ↔
      IsFig1Seq p fB Q σ ∧ ttm57LastOK p fB Q σ z := by
  have hT : ∀ m, m < σ.length → (σ ++ [z]).take (m + 1) = σ.take (m + 1) :=
    fun m hm => List.take_append_of_le_length (by omega)
  have hCA : ∀ m, m < σ.length → completionAt p (σ ++ [z]) m = completionAt p σ m :=
    fun m hm => ttm57_ca_append_left p σ [z] m hm
  have hTlast : (σ ++ [z]).take (σ.length + 1) = σ ++ [z] := List.take_of_length_le (by simp)
  have hCAlast : completionAt p (σ ++ [z]) σ.length = ((σ ++ [z]).map p).sum := by
    unfold completionAt; rw [hTlast]
  have hlen : (σ ++ [z]).length = σ.length + 1 := by simp
  constructor
  · intro H
    refine ⟨fun m hm => ?_, ?_⟩
    · have := H m (by omega)
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm
      rw [hg, hT m hm, hCA m hm] at this
      exact this
    · have := H σ.length (by omega)
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast] at this
      exact this
  · rintro ⟨H, hlast⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hlen ▸ hm) with hm' | hm'
    · have := H m hm'
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm'
      rw [hg, hT m hm', hCA m hm']
      exact this
    · subst hm'
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast]
      exact hlast

lemma ttm57_least_append_iff {nA nB : ℕ} (p : Job nA nB → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) :
    IsLeastCostSeq p fB Q (σ ++ [z]) ↔
      IsLeastCostSeq p fB Q σ ∧ ttm57LeastLastOK p fB Q σ z := by
  have hT : ∀ m, m < σ.length → (σ ++ [z]).take (m + 1) = σ.take (m + 1) :=
    fun m hm => List.take_append_of_le_length (by omega)
  have hCA : ∀ m, m < σ.length → completionAt p (σ ++ [z]) m = completionAt p σ m :=
    fun m hm => ttm57_ca_append_left p σ [z] m hm
  have hTlast : (σ ++ [z]).take (σ.length + 1) = σ ++ [z] := List.take_of_length_le (by simp)
  have hCAlast : completionAt p (σ ++ [z]) σ.length = ((σ ++ [z]).map p).sum := by
    unfold completionAt; rw [hTlast]
  have hlen : (σ ++ [z]).length = σ.length + 1 := by simp
  constructor
  · intro H
    refine ⟨fun m hm => ?_, ?_⟩
    · have := H m (by omega)
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm
      rw [hg, hT m hm, hCA m hm] at this
      exact this
    · have := H σ.length (by omega)
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast] at this
      exact this
  · rintro ⟨H, hlast⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hlen ▸ hm) with hm' | hm'
    · have := H m hm'
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm'
      rw [hg, hT m hm', hCA m hm']
      exact this
    · subst hm'
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast]
      exact hlast

def ttm57FeasB {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (Job nA nB)) : Prop :=
  ∀ k : Fin nB, Sum.inr k ∈ l → fB k (completionTime p l (Sum.inr k)) ≤ Q

noncomputable def partialTotalA {nA nB : ℕ} (p : Job nA nB → ℝ) (l : List (Job nA nB)) : ℝ :=
  ∑ h ∈ Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l),
    completionTime p l (Sum.inl h)

lemma partialTotalA_eq_total {nA nB : ℕ} (p : Job nA nB → ℝ) (l : List (Job nA nB))
    (hl : IsSchedule Finset.univ l) :
    partialTotalA p l = totalCompletionA p l := by
  unfold partialTotalA totalCompletionA
  have : Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l) = Finset.univ := by
    ext h
    simp [(hl.2 (Sum.inl h)).2 (Finset.mem_univ _)]
  rw [this]

lemma partialTotalA_append_inr {nA nB : ℕ} (p : Job nA nB → ℝ) (σ : List (Job nA nB))
    (k : Fin nB) :
    partialTotalA p (σ ++ [Sum.inr k]) = partialTotalA p σ := by
  unfold partialTotalA
  have hf : Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ σ ++ [Sum.inr k]) =
      Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ σ) := by
    ext h; simp
  rw [hf]
  refine Finset.sum_congr rfl (fun h hh => ?_)
  rw [Finset.mem_filter] at hh
  exact ttm57_ct_append_left p σ [Sum.inr k] (Sum.inl h) hh.2

lemma partialTotalA_append_inl {nA nB : ℕ} (p : Job nA nB → ℝ) (σ : List (Job nA nB))
    (h0 : Fin nA) (hnot : (Sum.inl h0 : Job nA nB) ∉ σ) :
    partialTotalA p (σ ++ [Sum.inl h0]) =
      partialTotalA p σ + ((σ ++ [Sum.inl h0]).map p).sum := by
  unfold partialTotalA
  have hf : Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ σ ++ [Sum.inl h0]) =
      insert h0 (Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ σ)) := by
    ext h; simp [eq_comm, or_comm]
  have hnot' : h0 ∉ Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ σ) := by
    simp [hnot]
  rw [hf, Finset.sum_insert hnot', ttm57_ct_last p σ (Sum.inl h0) hnot, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun h hh => ?_)
  rw [Finset.mem_filter] at hh
  exact ttm57_ct_append_left p σ [Sum.inl h0] (Sum.inl h) hh.2

lemma partialTotalA_erase_le {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l' : List (Job nA nB)) (hnd : l'.Nodup) (k0 : Fin nB) (hk0 : (Sum.inr k0 : Job nA nB) ∈ l') :
    partialTotalA p (l'.erase (Sum.inr k0)) ≤ partialTotalA p l' := by
  unfold partialTotalA
  have hf : Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l'.erase (Sum.inr k0)) =
      Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l') := by
    ext h
    simp [hnd.mem_erase_iff]
  rw [hf]
  refine Finset.sum_le_sum (fun h hh => ?_)
  rw [Finset.mem_filter] at hh
  exact ttm57_ct_erase_le p hp l' hnd (Sum.inr k0) (Sum.inl h) hk0 hh.2 (by simp)

lemma partialTotalA_erase_lt {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (L : List (Job nA nB)) (h1 : Fin nA) (k0 : Fin nB)
    (hnd : (L ++ [Sum.inl h1]).Nodup) (hk0L : (Sum.inr k0 : Job nA nB) ∈ L) :
    partialTotalA p ((L ++ [Sum.inl h1]).erase (Sum.inr k0)) <
      partialTotalA p (L ++ [Sum.inl h1]) := by
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  have hk0 : (Sum.inr k0 : Job nA nB) ∈ L ++ [Sum.inl h1] := List.mem_append_left _ hk0L
  unfold partialTotalA
  have hf : Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ (L ++ [Sum.inl h1]).erase (Sum.inr k0)) =
      Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ L ++ [Sum.inl h1]) := by
    ext h
    simp [hnd.mem_erase_iff]
  rw [hf]
  apply Finset.sum_lt_sum
  · intro h hh
    rw [Finset.mem_filter] at hh
    exact ttm57_ct_erase_le p hp0 (L ++ [Sum.inl h1]) hnd (Sum.inr k0) (Sum.inl h) hk0 hh.2 (by simp)
  · refine ⟨h1, by simp, ?_⟩
    have herase : (L ++ [Sum.inl h1]).erase (Sum.inr k0) = L.erase (Sum.inr k0) ++ [Sum.inl h1] :=
      List.erase_append_left _ hk0L
    have hh1L : (Sum.inl h1 : Job nA nB) ∉ L := fun h =>
      (List.nodup_append.1 hnd).2.2 _ h _ (by simp) rfl
    have hh1_not : (Sum.inl h1 : Job nA nB) ∉ L.erase (Sum.inr k0) := fun h =>
      hh1L (List.mem_of_mem_erase h)
    rw [herase, ttm57_ct_last p _ _ hh1_not, ttm57_ct_last p L _ hh1L]
    have hperm := (List.perm_cons_erase hk0L).map p
    have hsum := hperm.sum_eq
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
      List.sum_nil] at hsum ⊢
    have := hp (Sum.inr k0)
    linarith

lemma ttm57_swap_le {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (L : List (Job nA nB)) (h h' : Fin nA) (hneh : h ≠ h')
    (hle_p : p (Sum.inl h) ≤ p (Sum.inl h'))
    (hnd : (L ++ [Sum.inl h]).Nodup)
    (haL : (Sum.inl h' : Job nA nB) ∈ L)
    (hfeas : ttm57FeasB p fB Q (L ++ [Sum.inl h])) :
    ∃ L'' : List (Job nA nB),
      (L'' ++ [Sum.inl h']).Perm (L ++ [Sum.inl h]) ∧
      ttm57FeasB p fB Q (L'' ++ [Sum.inl h']) ∧
      partialTotalA p (L'' ++ [Sum.inl h']) ≤ partialTotalA p (L ++ [Sum.inl h]) ∧
      (∀ k : Fin nB, Sum.inr k ∈ L'' ++ [Sum.inl h'] →
        completionTime p (L'' ++ [Sum.inl h']) (Sum.inr k) ≤
          completionTime p (L ++ [Sum.inl h]) (Sum.inr k)) := by
  set a : Job nA nB := Sum.inl h' with ha
  set b : Job nA nB := Sum.inl h with hb
  have hab : a ≠ b := by
    intro e
    have : h' = h := by simpa [ha, hb] using e
    exact hneh this.symm
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem haL
  have hnd' := hnd
  simp only [List.append_assoc, List.cons_append] at hnd'
  obtain ⟨hn1, hn2, hdisj⟩ := List.nodup_append.1 hnd'
  obtain ⟨ha_notin, hnd2⟩ := List.nodup_cons.1 hn2
  obtain ⟨hn3, hn4, hdisj2⟩ := List.nodup_append.1 hnd2
  have haL1 : a ∉ L1 := fun hx => hdisj a hx a (by simp) rfl
  have hbL1 : b ∉ L1 := fun hx => hdisj b hx b (by simp) rfl
  have haL2 : a ∉ L2 := fun hx => ha_notin (List.mem_append_left _ hx)
  have hbL2 : b ∉ L2 := fun hx => hdisj2 b hx b (by simp) rfl
  have hL12 : ∀ x ∈ L2, x ∉ L1 := fun x hx hx1 => hdisj x hx1 x (by simp [hx]) rfl
  set L'' : List (Job nA nB) := L1 ++ b :: L2 with hL''
  set l' : List (Job nA nB) := L'' ++ [a] with hl'
  set l : List (Job nA nB) := (L1 ++ a :: L2) ++ [b] with hl
  have hl_eq : l = L1 ++ (a :: (L2 ++ [b])) := by simp [hl]
  have hl'_eq : l' = L1 ++ (b :: (L2 ++ [a])) := by simp [hl', hL'']
  have hperm : l.Perm l' := by
    rw [hl_eq, hl'_eq]
    refine List.Perm.append_left L1 ?_
    exact ((List.Perm.cons a (List.perm_append_singleton b L2)).trans
      (List.Perm.swap b a L2)).trans (List.Perm.cons b (List.perm_append_singleton a L2).symm)
  set S1 := (L1.map p).sum with hS1
  have hτ : (l.map p).sum = (l'.map p).sum := (hperm.map p).sum_eq
  have c1 : ∀ x ∈ L1, completionTime p l' x = completionTime p l x := by
    intro x hx
    rw [hl_eq, hl'_eq, ttm57_ct_append_left p _ _ x hx, ttm57_ct_append_left p _ _ x hx]
  have c2 : ∀ x ∈ L2, completionTime p l' x = completionTime p l x - (p a - p b) := by
    intro x hx
    have hxa : x ≠ a := fun e => haL2 (e ▸ hx)
    have hxb : x ≠ b := fun e => hbL2 (e ▸ hx)
    rw [hl_eq, hl'_eq, ttm57_ct_append_right p _ _ x (hL12 x hx),
      ttm57_ct_append_right p _ _ x (hL12 x hx),
      ttm57_ct_cons_ne p _ _ x hxa, ttm57_ct_cons_ne p _ _ x hxb,
      ttm57_ct_append_left p _ _ x hx, ttm57_ct_append_left p _ _ x hx]
    ring
  have c3a : completionTime p l a = S1 + p a := by
    rw [hl_eq, ttm57_ct_append_right p _ _ a haL1, ttm57_ct_cons_self]
  have c3b : completionTime p l' b = S1 + p b := by
    rw [hl'_eq, ttm57_ct_append_right p _ _ b hbL1, ttm57_ct_cons_self]
  have hbnot : b ∉ (L1 ++ a :: L2) := by
    intro hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact hbL1 h1
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact hab h2.symm
      · exact hbL2 h2
  have hanot : a ∉ (L1 ++ b :: L2) := by
    intro hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact haL1 h1
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact hab h2
      · exact haL2 h2
  have c4b : completionTime p l b = (l.map p).sum := by
    rw [hl]; exact ttm57_ct_last p _ b hbnot
  have c4a : completionTime p l' a = (l'.map p).sum := by
    rw [hl', hL'']; exact ttm57_ct_last p _ a hanot
  have hcls : ∀ x ∈ l, x ≠ a → x ≠ b → x ∈ L1 ∨ x ∈ L2 := by
    intro x hx hxa hxb
    rw [hl] at hx
    simp only [List.mem_append, List.mem_cons] at hx
    tauto
  have hBct : ∀ k : Fin nB, Sum.inr k ∈ l' →
      completionTime p l' (Sum.inr k) ≤ completionTime p l (Sum.inr k) := by
    intro k hk
    have hkl : Sum.inr k ∈ l := hperm.symm.mem_iff.1 hk
    have hxa : (Sum.inr k : Job nA nB) ≠ a := by simp [ha]
    have hxb : (Sum.inr k : Job nA nB) ≠ b := by simp [hb]
    rcases hcls _ hkl hxa hxb with h1 | h1
    · rw [c1 _ h1]
    · rw [c2 _ h1]; linarith
  refine ⟨L'', hperm.symm, ?_, ?_, hBct⟩
  · intro k hk
    have hkl : Sum.inr k ∈ l := hperm.symm.mem_iff.1 hk
    exact (hfB k (hBct k hk)).trans (hfeas k hkl)
  · unfold partialTotalA
    have hf : Finset.univ.filter (fun x : Fin nA => Sum.inl x ∈ l') =
        Finset.univ.filter (fun x : Fin nA => Sum.inl x ∈ l) := by
      ext x; simp [hperm.mem_iff]
    rw [hf]
    set S := Finset.univ.filter (fun x : Fin nA => Sum.inl x ∈ l)
    have hG1 : ∀ h'' ∈ S, h'' ≠ h → h'' ≠ h' →
        completionTime p l' (Sum.inl h'') - completionTime p l (Sum.inl h'') ≤ 0 := by
      intro h'' hh'' h1 h2
      have hxl : Sum.inl h'' ∈ l := (Finset.mem_filter.1 hh'').2
      have hxa : (Sum.inl h'' : Job nA nB) ≠ a := by simp [ha, h2]
      have hxb : (Sum.inl h'' : Job nA nB) ≠ b := by simp [hb, h1]
      rcases hcls _ hxl hxa hxb with h3 | h3
      · rw [c1 _ h3]; simp
      · rw [c2 _ h3]; linarith
    have hpair : ∑ x ∈ ({h, h'} : Finset (Fin nA)),
        -(completionTime p l' (Sum.inl x) - completionTime p l (Sum.inl x)) = p a - p b := by
      rw [Finset.sum_pair hneh]
      have e1 : completionTime p l' (Sum.inl h') = (l'.map p).sum := c4a
      have e2 : completionTime p l (Sum.inl h) = (l.map p).sum := c4b
      have e3 : completionTime p l (Sum.inl h') = S1 + p a := c3a
      have e4 : completionTime p l' (Sum.inl h) = S1 + p b := c3b
      rw [e1, e2, e3, e4, ← hτ]
      ring
    have hsub : ({h, h'} : Finset (Fin nA)) ⊆ S := by
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hl]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simp [hb]
      · rw [Finset.mem_singleton.1 hx]; simp [ha]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun x => -(completionTime p l' (Sum.inl x) - completionTime p l (Sum.inl x))) hsub
      (by
        intro x hxS hx
        have h1 : x ≠ h := fun e => hx (by simp [e])
        have h2 : x ≠ h' := fun e => hx (by simp [e])
        have := hG1 x hxS h1 h2
        linarith)
    rw [hpair] at hle
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hle
    have hnn : 0 ≤ p a - p b := by rw [ha, hb]; linarith
    linarith

lemma ttm57_fig1_core {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    ∀ σ : List (Job nA nB), IsFig1Seq p fB Q σ → σ.Nodup →
      ∀ l' : List (Job nA nB), l'.Perm σ → ttm57FeasB p fB Q l' →
        partialTotalA p σ ≤ partialTotalA p l' := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
    intro _ _ l' hperm _
    have : l' = [] := (List.Perm.nil_eq hperm.symm).symm
    subst this
    rfl
  | append_singleton σ z ih =>
    intro hrule hnd l' hperm hfeas
    obtain ⟨hr0, hlast⟩ := (ttm57_rule_append_iff p fB Q σ z).1 hrule
    have hnd2 := List.nodup_append.1 hnd
    have hσnd : σ.Nodup := hnd2.1
    have hzσ : z ∉ σ := fun hz => hnd2.2.2 z hz z (by simp) rfl
    have hzl' : z ∈ l' := hperm.mem_iff.2 (by simp)
    have hl'nd : l'.Nodup := hperm.nodup_iff.2 hnd
    rcases z with h0 | k0
    · have hel : ¬ ∃ k : Fin nB, Sum.inr k ∈ (σ ++ [Sum.inl h0]).toFinset ∧
          fB k ((σ ++ [Sum.inl h0]).map p).sum ≤ Q := by
        rintro ⟨k, hk1, hk2⟩
        obtain ⟨k', hk'⟩ := hlast.1 ⟨k, hk1, hk2⟩
        exact absurd hk'.1 (by simp)
      obtain ⟨h0', hh0', hmax⟩ := hlast.2 hel
      have hh0_eq : h0' = h0 := (Sum.inl_injective hh0').symm
      subst hh0_eq
      have hne : l' ≠ [] := List.ne_nil_of_mem hzl'
      obtain ⟨L, y, hLy⟩ := (List.eq_nil_or_concat l').resolve_left hne
      rw [List.concat_eq_append] at hLy
      subst hLy
      have hyL : y ∉ L := fun hy => (List.nodup_append.1 hl'nd).2.2 y hy y (by simp) rfl
      have hyc : completionTime p (L ++ [y]) y = ((σ ++ [Sum.inl h0']).map p).sum := by
        rw [ttm57_ct_last p L y hyL, (hperm.map p).sum_eq]
      have hyU : y ∈ σ ++ [Sum.inl h0'] := hperm.mem_iff.1 (by simp)
      rcases y with h1 | k1
      · by_cases h10 : h1 = h0'
        · subst h10
          have hpermL : L.Perm σ := (List.perm_append_right_iff [Sum.inl h1]).1 hperm
          have hfeasL : ttm57FeasB p fB Q L := by
            intro k hk
            have hk' : Sum.inr k ∈ L ++ [Sum.inl h1] := List.mem_append_left _ hk
            have := hfeas k hk'
            rwa [ttm57_ct_append_left p L [Sum.inl h1] (Sum.inr k) hk] at this
          have ihL := ih hr0 hσnd L hpermL hfeasL
          rw [partialTotalA_append_inl p σ h1 hzσ, partialTotalA_append_inl p L h1 hyL,
            (hperm.map p).sum_eq]
          linarith
        · have haL : (Sum.inl h0' : Job nA nB) ∈ L := by
            rcases List.mem_append.1 hzl' with hh1 | hh1
            · exact hh1
            · exfalso
              have : h0' = h1 := Sum.inl_injective (List.mem_singleton.1 hh1)
              exact h10 this.symm
          have hle_p : p (Sum.inl h1) ≤ p (Sum.inl h0') :=
            hmax h1 (List.mem_toFinset.2 hyU)
          obtain ⟨L'', hperm_sw, hfeas_sw, htot_sw, _⟩ :=
            ttm57_swap_le p fB hfB Q L h1 h0' h10 hle_p hl'nd haL hfeas
          have hpermL'' : L''.Perm σ :=
            (List.perm_append_right_iff [Sum.inl h0']).1 (hperm_sw.trans hperm)
          have hL''nd : (L'' ++ [Sum.inl h0']).Nodup := (hperm_sw.trans hperm).nodup_iff.2 hnd
          have hzL'' : (Sum.inl h0' : Job nA nB) ∉ L'' := fun hz =>
            (List.nodup_append.1 hL''nd).2.2 _ hz _ (by simp) rfl
          have hfeasL'' : ttm57FeasB p fB Q L'' := by
            intro k hk
            have hk' : Sum.inr k ∈ L'' ++ [Sum.inl h0'] := List.mem_append_left _ hk
            have := hfeas_sw k hk'
            rwa [ttm57_ct_append_left p L'' [Sum.inl h0'] (Sum.inr k) hk] at this
          have ihL'' := ih hr0 hσnd L'' hpermL'' hfeasL''
          have hsum_sw : ((L'' ++ [Sum.inl h0']).map p).sum = ((σ ++ [Sum.inl h0']).map p).sum :=
            ((hperm_sw.trans hperm).map p).sum_eq
          have hstep : partialTotalA p (σ ++ [Sum.inl h0']) ≤ partialTotalA p (L'' ++ [Sum.inl h0']) := by
            rw [partialTotalA_append_inl p σ h0' hzσ, partialTotalA_append_inl p L'' h0' hzL'',
              hsum_sw]
            linarith
          exact hstep.trans htot_sw
      · exfalso
        have := hfeas k1 (by simp)
        rw [hyc] at this
        exact hel ⟨k1, List.mem_toFinset.2 hyU, this⟩
    · obtain ⟨l'', hperm0, hl''⟩ := ttm57_erase_ex p hp l' hl'nd (Sum.inr k0) hzl'
      have hperm'' : l''.Perm σ :=
        (List.perm_append_right_iff [Sum.inr k0]).1 (hperm0.symm.trans hperm)
      have hfeas'' : ttm57FeasB p fB Q l'' := fun k hk =>
        (hfB k (hl'' _ hk).2.2).trans (hfeas k (hl'' _ hk).1)
      have ih'' := ih hr0 hσnd l'' hperm'' hfeas''
      rw [partialTotalA_append_inr p σ k0]
      refine ih''.trans ?_
      unfold partialTotalA
      have hf : Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l'') =
          Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l') := by
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hh; exact (hl'' _ hh).1
        · intro hh
          rcases List.mem_append.1 (hperm0.mem_iff.1 hh) with h1 | h1
          · exact h1
          · simp at h1
      rw [hf]
      refine Finset.sum_le_sum (fun h hh => ?_)
      rw [Finset.mem_filter] at hh
      have hmem'' : Sum.inl h ∈ l'' := by
        rcases List.mem_append.1 (hperm0.mem_iff.1 hh.2) with h1 | h1
        · exact h1
        · simp at h1
      exact (hl'' _ hmem'').2.2

lemma ttm57_least_core {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    ∀ σ : List (Job nA nB), IsLeastCostSeq p fB Q σ → σ.Nodup →
      ∀ l' : List (Job nA nB), l'.Perm σ → ttm57FeasB p fB Q l' →
        partialTotalA p l' ≤ partialTotalA p σ →
        ∀ v : ℝ, (∀ k : Fin nB, Sum.inr k ∈ l' → fB k (completionTime p l' (Sum.inr k)) ≤ v) →
          ∀ k : Fin nB, Sum.inr k ∈ σ → fB k (completionTime p σ (Sum.inr k)) ≤ v := by
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
    intro _ _ _ _ _ _ _ _ k hk
    simp at hk
  | append_singleton σ z ih =>
    intro hrule hnd l' hperm hfeas htot_le v hv k hk
    obtain ⟨hr0, hlast⟩ := (ttm57_least_append_iff p fB Q σ z).1 hrule
    have hnd2 := List.nodup_append.1 hnd
    have hσnd : σ.Nodup := hnd2.1
    have hzσ : z ∉ σ := fun hz => hnd2.2.2 z hz z (by simp) rfl
    have hzl' : z ∈ l' := hperm.mem_iff.2 (by simp)
    have hl'nd : l'.Nodup := hperm.nodup_iff.2 hnd
    have hne : l' ≠ [] := List.ne_nil_of_mem hzl'
    obtain ⟨L, y, hLy⟩ := (List.eq_nil_or_concat l').resolve_left hne
    rw [List.concat_eq_append] at hLy
    subst hLy
    have hyL : y ∉ L := fun hy => (List.nodup_append.1 hl'nd).2.2 y hy y (by simp) rfl
    have hyc : completionTime p (L ++ [y]) y = ((σ ++ [z]).map p).sum := by
      rw [ttm57_ct_last p L y hyL, (hperm.map p).sum_eq]
    have hyU : y ∈ σ ++ [z] := hperm.mem_iff.1 (by simp)
    rcases z with h0 | k0
    · -- z = Sum.inl h0
      have hel : ¬ ∃ k' : Fin nB, Sum.inr k' ∈ (σ ++ [Sum.inl h0]).toFinset ∧
          fB k' ((σ ++ [Sum.inl h0]).map p).sum ≤ Q := by
        rintro ⟨k', hk1, hk2⟩
        obtain ⟨k'', hk''⟩ := hlast.1 ⟨k', hk1, hk2⟩
        exact absurd hk''.1 (by simp)
      obtain ⟨h0', hh0', hmax⟩ := hlast.2 hel
      have hh0_eq : h0' = h0 := (Sum.inl_injective hh0').symm
      subst hh0_eq
      have hkσ : Sum.inr k ∈ σ := by
        rcases List.mem_append.1 hk with h1 | h1
        · exact h1
        · simp at h1
      rw [ttm57_ct_append_left p σ [Sum.inl h0'] (Sum.inr k) hkσ]
      rcases y with h1 | k1
      · by_cases h10 : h1 = h0'
        · subst h10
          have hpermL : L.Perm σ := (List.perm_append_right_iff [Sum.inl h1]).1 hperm
          have hfeasL : ttm57FeasB p fB Q L := by
            intro k' hk'
            have hk'' : Sum.inr k' ∈ L ++ [Sum.inl h1] := List.mem_append_left _ hk'
            have := hfeas k' hk''
            rwa [ttm57_ct_append_left p L [Sum.inl h1] (Sum.inr k') hk'] at this
          have htotL : partialTotalA p L ≤ partialTotalA p σ := by
            rw [partialTotalA_append_inl p σ h1 hzσ, partialTotalA_append_inl p L h1 hyL,
              (hperm.map p).sum_eq] at htot_le
            linarith
          have hvL : ∀ k' : Fin nB, Sum.inr k' ∈ L → fB k' (completionTime p L (Sum.inr k')) ≤ v := by
            intro k' hk'
            have := hv k' (List.mem_append_left _ hk')
            rwa [ttm57_ct_append_left p L [Sum.inl h1] (Sum.inr k') hk'] at this
          exact ih hr0 hσnd L hpermL hfeasL htotL v hvL k hkσ
        · have haL : (Sum.inl h0' : Job nA nB) ∈ L := by
            rcases List.mem_append.1 hzl' with hh1 | hh1
            · exact hh1
            · exfalso
              have : h0' = h1 := Sum.inl_injective (List.mem_singleton.1 hh1)
              exact h10 this.symm
          have hle_p : p (Sum.inl h1) ≤ p (Sum.inl h0') :=
            hmax h1 (List.mem_toFinset.2 hyU)
          obtain ⟨L'', hperm_sw, hfeas_sw, htot_sw, hBct_sw⟩ :=
            ttm57_swap_le p fB hfB Q L h1 h0' h10 hle_p hl'nd haL hfeas
          have hpermL'' : L''.Perm σ :=
            (List.perm_append_right_iff [Sum.inl h0']).1 (hperm_sw.trans hperm)
          have hL''nd : (L'' ++ [Sum.inl h0']).Nodup := (hperm_sw.trans hperm).nodup_iff.2 hnd
          have hzL'' : (Sum.inl h0' : Job nA nB) ∉ L'' := fun hz =>
            (List.nodup_append.1 hL''nd).2.2 _ hz _ (by simp) rfl
          have hfeasL'' : ttm57FeasB p fB Q L'' := by
            intro k' hk'
            have hk'' : Sum.inr k' ∈ L'' ++ [Sum.inl h0'] := List.mem_append_left _ hk'
            have := hfeas_sw k' hk''
            rwa [ttm57_ct_append_left p L'' [Sum.inl h0'] (Sum.inr k') hk'] at this
          have hsum_sw : ((L'' ++ [Sum.inl h0']).map p).sum = ((σ ++ [Sum.inl h0']).map p).sum :=
            ((hperm_sw.trans hperm).map p).sum_eq
          have htotL'' : partialTotalA p L'' ≤ partialTotalA p σ := by
            have h1 := htot_sw.trans htot_le
            rw [partialTotalA_append_inl p σ h0' hzσ, partialTotalA_append_inl p L'' h0' hzL'',
              hsum_sw] at h1
            linarith
          have hvL'' : ∀ k' : Fin nB, Sum.inr k' ∈ L'' →
              fB k' (completionTime p L'' (Sum.inr k')) ≤ v := by
            intro k' hk'
            have hk'_sw : Sum.inr k' ∈ L'' ++ [Sum.inl h0'] := List.mem_append_left _ hk'
            have hk'_orig : Sum.inr k' ∈ L ++ [Sum.inl h1] := hperm_sw.mem_iff.1 hk'_sw
            have hle_ct := hBct_sw k' hk'_sw
            rw [ttm57_ct_append_left p L'' [Sum.inl h0'] (Sum.inr k') hk'] at hle_ct
            exact (hfB k' hle_ct).trans (hv k' hk'_orig)
          exact ih hr0 hσnd L'' hpermL'' hfeasL'' htotL'' v hvL'' k hkσ
      · exfalso
        have := hfeas k1 (by simp)
        rw [hyc] at this
        exact hel ⟨k1, List.mem_toFinset.2 hyU, this⟩
    · -- z = Sum.inr k0
      have hel : ∃ k' : Fin nB, Sum.inr k' ∈ (σ ++ [Sum.inr k0]).toFinset ∧
          fB k' ((σ ++ [Sum.inr k0]).map p).sum ≤ Q := by
        by_contra hnot
        obtain ⟨h', hh', _⟩ := hlast.2 hnot
        exact absurd hh' (by simp)
      obtain ⟨k0', hk0', hmin⟩ := hlast.1 hel
      have hk0_eq : k0' = k0 := (Sum.inr_injective hk0').symm
      subst hk0_eq
      set l'' := (L ++ [y]).erase (Sum.inr k0') with hl''_def
      have hperm0 : (L ++ [y]).Perm (l'' ++ [Sum.inr k0']) :=
        (List.perm_cons_erase hzl').trans (List.perm_append_singleton _ _).symm
      have hperm'' : l''.Perm σ :=
        (List.perm_append_right_iff [Sum.inr k0']).1 (hperm0.symm.trans hperm)
      have hfeas'' : ttm57FeasB p fB Q l'' := by
        intro k' hk'
        have hk'_in : Sum.inr k' ∈ L ++ [y] := List.mem_of_mem_erase hk'
        have hk'_ne : (Sum.inr k' : Job nA nB) ≠ Sum.inr k0' :=
          (hl'nd.mem_erase_iff.1 hk').1
        exact (hfB k' (ttm57_ct_erase_le p hp0 (L ++ [y]) hl'nd (Sum.inr k0') (Sum.inr k')
          hzl' hk'_in hk'_ne)).trans (hfeas k' hk'_in)
      have htot_ge : partialTotalA p σ ≤ partialTotalA p l'' :=
        ttm57_fig1_core p hp0 fB hfB Q σ (isFig1_of_leastCost p fB Q σ hr0) hσnd l'' hperm'' hfeas''
      rcases y with h1 | k1
      · -- y = Sum.inl h1 is impossible because moving k0' after h1 strictly reduces partialTotalA
        exfalso
        have hk0L : (Sum.inr k0' : Job nA nB) ∈ L := by
          rcases List.mem_append.1 hzl' with h1 | h1
          · exact h1
          · simp at h1
        have hlt := partialTotalA_erase_lt p hp L h1 k0' hl'nd hk0L
        rw [← hl''_def] at hlt
        rw [partialTotalA_append_inr p σ k0'] at htot_le
        linarith
      · -- y = Sum.inr k1
        rcases List.mem_append.1 hk with hkσ | hkz
        · rw [ttm57_ct_append_left p σ [Sum.inr k0'] (Sum.inr k) hkσ]
          have htot'' : partialTotalA p l'' ≤ partialTotalA p σ := by
            have hle := partialTotalA_erase_le p hp0 (L ++ [Sum.inr k1]) hl'nd k0' hzl'
            rw [← hl''_def] at hle
            rw [partialTotalA_append_inr p σ k0'] at htot_le
            exact hle.trans htot_le
          have hv'' : ∀ k' : Fin nB, Sum.inr k' ∈ l'' →
              fB k' (completionTime p l'' (Sum.inr k')) ≤ v := by
            intro k' hk'
            have hk'_in : Sum.inr k' ∈ L ++ [Sum.inr k1] := List.mem_of_mem_erase hk'
            have hk'_ne : (Sum.inr k' : Job nA nB) ≠ Sum.inr k0' :=
              (hl'nd.mem_erase_iff.1 hk').1
            exact (hfB k' (ttm57_ct_erase_le p hp0 (L ++ [Sum.inr k1]) hl'nd (Sum.inr k0')
              (Sum.inr k') hzl' hk'_in hk'_ne)).trans (hv k' hk'_in)
          exact ih hr0 hσnd l'' hperm'' hfeas'' htot'' v hv'' k hkσ
        · have heq : k = k0' := Sum.inr_injective (List.mem_singleton.1 hkz)
          subst heq
          rw [ttm57_ct_last p σ (Sum.inr k) hzσ]
          have hle1 : fB k ((σ ++ [Sum.inr k]).map p).sum ≤
              fB k1 ((σ ++ [Sum.inr k]).map p).sum :=
            hmin k1 (List.mem_toFinset.2 hyU)
          have hle2 : fB k1 ((σ ++ [Sum.inr k]).map p).sum ≤ v := by
            rw [← hyc]
            exact hv k1 (by simp)
          exact hle1.trans hle2

theorem solution {nA nB : ℕ} (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q) (σtilde : List (TwoAgentSched.MaxMax.Job nA nB))
    (hsched : MooreLateJobs.Shared.IsSchedule Finset.univ σtilde)
    (hrule : IsLeastCostSeq p fB Q σtilde) :
    IsOptimal p fB Q σtilde ∧ IsNondominated hB p fB σtilde := by
  have hfig1 : IsFig1Seq p fB Q σtilde := isFig1_of_leastCost p fB Q σtilde hrule
  have hopt : IsOptimal p fB Q σtilde :=
    (theorem_5_5 p hp fB hfB Q).1 hfeas σtilde hsched hfig1
  refine ⟨hopt, hsched, ?_⟩
  rintro ⟨l', hl', h1, h2, h3⟩
  have hBtilde : maxCostB hB p fB σtilde ≤ Q :=
    Finset.sup'_le _ _ (fun k _ => hopt.1.2 k)
  have hl'feas : IsFeasible p fB Q l' :=
    ⟨hl', fun k => (Finset.le_sup'
      (fun k => fB k (completionTime p l' (Sum.inr k)))
      (Finset.mem_univ k)).trans (h2.trans hBtilde)⟩
  have hopt_le : totalCompletionA p σtilde ≤ totalCompletionA p l' :=
    hopt.2 l' hl'feas
  rcases h3 with h3 | h3
  · linarith
  · have hperm : l'.Perm σtilde := by
      rw [List.perm_ext_iff_of_nodup hl'.1 hsched.1]
      intro x
      rw [hl'.2 x, hsched.2 x]
    have hfe' : ttm57FeasB p fB Q l' := fun k _ => hl'feas.2 k
    have htot_le : partialTotalA p l' ≤ partialTotalA p σtilde := by
      rwa [partialTotalA_eq_total p l' hl', partialTotalA_eq_total p σtilde hsched]
    have hcore := ttm57_least_core p hp fB hfB Q σtilde hrule hsched.1 l' hperm hfe' htot_le
      (maxCostB hB p fB l') (fun k _ => Finset.le_sup'
        (fun k => fB k (completionTime p l' (Sum.inr k))) (Finset.mem_univ k))
    have hBle : maxCostB hB p fB σtilde ≤ maxCostB hB p fB l' :=
      Finset.sup'_le _ _ (fun k _ => hcore k ((hsched.2 _).2 (Finset.mem_univ _)))
    linarith
