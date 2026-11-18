-- Prove2me | solution 1 for WeldedPath.loop_erasure_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T16:48:33.831241+00:00
-- url     : https://prove2.me/submissions/c19896b3-a269-4507-8d5e-6849b4863f5d

import Definitions.Def_WeldedPath_Supplement_pWt
import Definitions.Def_WeldedPath_bEdge
import Definitions.Def_WeldedPath_Nb

set_option autoImplicit false

-- Solutions.WeldedPathLoopErase
section

namespace WeldedPath.LoopProof

section Generic

variable {α β : Type*} [DecidableEq α] (lab : β → α)

def Chain (R : α → β → Prop) (finish : α) : α → List β → Prop
  | start, [] => start = finish
  | start, x :: xs => R start x ∧ Chain R finish (lab x) xs

def after (z : α) : List β → List β
  | [] => []
  | x :: xs => if lab x = z then xs else after z xs

def eraseFrom (start : α) : List β → List β
  | [] => []
  | x :: xs =>
      let ys := x :: eraseFrom (lab x) xs
      if start ∈ ys.map lab then after lab start ys else ys

theorem after_subset (z : α) (xs : List β) : after lab z xs ⊆ xs := by
  induction xs with
  | nil => simp [after]
  | cons x xs ih =>
      simp only [after]
      split
      · exact List.subset_cons_self _ _
      · intro y hy
        exact List.mem_cons_of_mem _ (ih hy)

theorem after_chain (R : α → β → Prop) (finish start z : α) (xs : List β)
    (h : Chain lab R finish start xs) (hz : z ∈ xs.map lab) :
    Chain lab R finish z (after lab z xs) := by
  induction xs generalizing start with
  | nil => simp at hz
  | cons x xs ih =>
      simp only [after]
      by_cases hx : lab x = z
      · simpa [hx] using h.2
      · simp only [hx, if_false]
        exact ih _ h.2 ((List.mem_cons.mp hz).resolve_left (Ne.symm hx))

theorem after_nodup (z : α) (xs : List β)
    (h : (xs.map lab).Nodup) (hz : z ∈ xs.map lab) :
    (z :: (after lab z xs).map lab).Nodup := by
  induction xs with
  | nil => simp at hz
  | cons x xs ih =>
      simp only [after]
      by_cases hx : lab x = z
      · simpa [hx] using h
      · simp only [hx, if_false]
        exact ih h.tail ((List.mem_cons.mp hz).resolve_left (Ne.symm hx))

theorem eraseFrom_subset (start : α) (xs : List β) : eraseFrom lab start xs ⊆ xs := by
  induction xs generalizing start with
  | nil => simp [eraseFrom]
  | cons x xs ih =>
      simp only [eraseFrom]
      split
      · intro y hy
        exact List.cons_subset_cons _ (ih _) (after_subset lab _ _ hy)
      · exact List.cons_subset_cons _ (ih _)

theorem eraseFrom_chain (R : α → β → Prop) (finish start : α) (xs : List β)
    (h : Chain lab R finish start xs) : Chain lab R finish start (eraseFrom lab start xs) := by
  induction xs generalizing start with
  | nil => exact h
  | cons x xs ih =>
      have hy : Chain lab R finish start (x :: eraseFrom lab (lab x) xs) := ⟨h.1, ih _ h.2⟩
      simp only [eraseFrom]
      split
      · exact after_chain lab R finish start start _ hy ‹_›
      · exact hy

theorem eraseFrom_nodup (start : α) (xs : List β) :
    (start :: (eraseFrom lab start xs).map lab).Nodup := by
  induction xs generalizing start with
  | nil => simp [eraseFrom]
  | cons x xs ih =>
      have hy : ((x :: eraseFrom lab (lab x) xs).map lab).Nodup := ih _
      simp only [eraseFrom]
      split
      · rename_i hz
        exact after_nodup lab start _ hy hz
      · exact List.nodup_cons.mpr ⟨‹_›, hy⟩

theorem chain_getD (R : α → β → Prop) (finish start d : α) (default : β)
    (xs : List β) (h : Chain lab R finish start xs) (i : ℕ) (hi : i < xs.length) :
    R ((start :: xs.map lab).getD i d) (xs.getD i default) ∧
      lab (xs.getD i default) = (start :: xs.map lab).getD (i + 1) d := by
  induction xs generalizing start i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simpa using And.intro h.1 (Eq.refl (lab x))
      | succ i => simpa using ih (lab x) h.2 i (by simpa using hi)

theorem chain_last (R : α → β → Prop) (finish start d : α) (xs : List β)
    (h : Chain lab R finish start xs) : (start :: xs.map lab).getD xs.length d = finish := by
  induction xs generalizing start with
  | nil => exact h
  | cons x xs ih => simpa using ih (lab x) h.2

end Generic

open QAlgorithms WeldedInstance

def stepLabel {n : ℕ} (x : Fin 3 × Qubits (2 * n + 1)) : ℕ := bitsToNat x.2

def NatStep {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (z : ℕ) (x : Fin 3 × Qubits (2 * n + 1)) : Prop :=
  ∃ hz : z < labelBound n + 1, ∃ hx : stepLabel x < labelBound n + 1,
    G.F l σ ⟨z, hz⟩ x.1 = ⟨stepLabel x, hx⟩ ∧
      (⟨stepLabel x, hx⟩ : Label n) ≠ ⟨z, hz⟩

theorem chain_iff_walkFrom {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (z : Label n) (xs : List (Fin 3 × Qubits (2 * n + 1))) :
    Chain stepLabel (NatStep l G σ) (σ.1 (exitLabelIdx n)).val z.val xs ↔
      G.WalkFrom l σ z xs := by
  induction xs generalizing z with
  | nil =>
      change z.val = (σ.1 (exitLabelIdx n)).val ↔ z = σ.1 (exitLabelIdx n)
      exact Fin.val_inj
  | cons x xs ih =>
      constructor
      · rintro ⟨⟨hz, hx, hF, hne⟩, ht⟩
        exact ⟨hx, hF, hne, (ih ⟨stepLabel x, hx⟩).mp ht⟩
      · rintro ⟨hx, hF, hne, ht⟩
        exact ⟨⟨z.isLt, hx, hF, hne⟩, (ih ⟨stepLabel x, hx⟩).mpr ht⟩

def erase {n : ℕ} (xs : List (Fin 3 × Qubits (2 * n + 1))) :=
  eraseFrom stepLabel 0 xs

theorem erase_nodup {n : ℕ} (xs : List (Fin 3 × Qubits (2 * n + 1))) :
    (Supplement.pathLabels (erase xs)).Nodup := by
  exact eraseFrom_nodup stepLabel 0 xs

theorem erase_walkFrom {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (xs : List (Fin 3 × Qubits (2 * n + 1))) (h : G.WalkFrom l σ 0 xs) :
    G.WalkFrom l σ 0 (erase xs) := by
  apply (chain_iff_walkFrom l G σ 0 (erase xs)).mp
  exact eraseFrom_chain stepLabel (NatStep l G σ) (σ.1 (exitLabelIdx n)).val 0 xs
    ((chain_iff_walkFrom l G σ 0 xs).mpr h)

theorem erase_subset {n : ℕ} (xs : List (Fin 3 × Qubits (2 * n + 1))) :
    erase xs ⊆ xs := eraseFrom_subset stepLabel 0 xs

end WeldedPath.LoopProof

end


-- Solutions.WeldedPathGraphDepth
section

namespace WeldedPath.LoopProof

lemma pow_root_ge_two (n : ℕ) : 2 ≤ 2 ^ (n + 1) := by
  have h := Nat.two_pow_pos n
  rw [pow_succ]
  omega

lemma numV_eq (n : ℕ) : numV n = 2 * (2 ^ (n + 1) - 1) := by
  have h := pow_root_ge_two n
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma col_zero (n : ℕ) : col n 0 = 0 := by
  have h := pow_root_ge_two n
  simp [col, show 0 < 2 ^ (n + 1) - 1 by omega]

lemma col_exit (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma log_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) :
    Nat.log 2 (v + 1) ≤ n := by
  have h : v + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : v + 1 ≠ 0)).2 h
  omega

lemma log_right_le (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) ≤ n := by
  have hn := pow_root_ge_two n
  rw [IsVertex, numV_eq] at hv
  have h : v - (2 ^ (n + 1) - 1) + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2)
    (by omega : v - (2 ^ (n + 1) - 1) + 1 ≠ 0)).2 h
  omega

lemma col_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) : col n v ≤ n := by
  simpa [col, hv] using log_left_le n v hv

lemma col_right_ge (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    n + 1 ≤ col n v := by
  have hd := log_right_le n v hv hr
  simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1)]
  omega

lemma col_bounds (n v : ℕ) (hv : IsVertex n v) : col n v ≤ 2 * n + 1 := by
  by_cases h : v < 2 ^ (n + 1) - 1
  · have := col_left_le n v h
    omega
  · simp only [col, if_neg h]
    omega

lemma parent_spec {n v p : ℕ} (hp : parent n v = some p) :
    IsVertex n v ∧ IsVertex n p ∧
      ((col n p + 1 = col n v ∧ col n v ≤ n) ∨
        (col n v + 1 = col n p ∧ n + 1 ≤ col n v)) := by
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    have hv := h.1
    have hvleft : v < 2 ^ (n + 1) - 1 := by
      by_contra hh
      have := col_right_ge n v hv (by omega)
      omega
    have hvpos : 1 ≤ v := by
      by_contra hh
      have heq : v = 0 := by omega
      subst v
      simp [col_zero] at h
    have hpval : p = (v - 1) / 2 := by simpa using hp.symm
    have hpv : p < v := by omega
    have hpV : IsVertex n p := by unfold IsVertex at *; omega
    have hpleft : p < 2 ^ (n + 1) - 1 := by omega
    have hdiv : p + 1 = (v + 1) / 2 := by omega
    have hlog : Nat.log 2 (p + 1) = Nat.log 2 (v + 1) - 1 := by
      rw [hdiv, Nat.log_div_base]
    have hcols : col n p + 1 = col n v := by
      simp only [col, if_pos hvleft] at h
      simp only [col, if_pos hpleft, if_pos hvleft]
      omega
    exact ⟨hv, hpV, Or.inl ⟨hcols, h.2.2⟩⟩
  next h =>
    split at hp
    next h' =>
      have hv := h'.1
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc : col n v = 2 * n + 1 := by
          simpa [heq, exitIdx] using col_exit n
        omega
      have hvbig : 2 ^ (n + 1) ≤ v := by omega
      have hpval : p = (v - 2 ^ (n + 1)) / 2 + 2 ^ (n + 1) - 1 := by
        simpa using hp.symm
      have hpv : p < v := by omega
      have hpV : IsVertex n p := by unfold IsVertex at *; omega
      have hpright : 2 ^ (n + 1) - 1 ≤ p := by omega
      have hdiv : p - (2 ^ (n + 1) - 1) + 1 =
          (v - (2 ^ (n + 1) - 1) + 1) / 2 := by omega
      have hlog : Nat.log 2 (p - (2 ^ (n + 1) - 1) + 1) =
          Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) - 1 := by
        rw [hdiv, Nat.log_div_base]
      have hd := log_right_le n v hv hvright
      have hdpos : 1 ≤ Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) := by
        have := Nat.log_pos (by decide : 1 < 2)
          (show 2 ≤ v - (2 ^ (n + 1) - 1) + 1 by omega)
        omega
      have hcols : col n v + 1 = col n p := by
        simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1),
          if_neg (by omega : ¬ p < 2 ^ (n + 1) - 1)]
        omega
      exact ⟨hv, hpV, Or.inr ⟨hcols, h'.2.1⟩⟩
    next h' => simp at hp

lemma parent_eq_exit_imp {n v : ℕ} (hp : parent n v = some (exitIdx n)) :
    v = 2 ^ (n + 1) ∨ v = 2 ^ (n + 1) + 1 := by
  have hs := parent_spec hp
  have hc := col_exit n
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    rcases hs.2.2 with hleft | hright <;> omega
  next h =>
    split at hp
    next h' =>
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc' : col n v = 2 * n + 1 := by simpa [heq, exitIdx] using col_exit n
        omega
      simp only [Option.some.injEq, exitIdx] at hp
      omega
    next h' => simp at hp

lemma tree_mem_iff {n : ℕ} {G : WeldedInstance n} {v : ℕ} :
    Edge.tree v ∈ G.edges ↔ IsVertex n v ∧ (parent n v).isSome := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges, IsVertex]

lemma weld_mem_iff {n : ℕ} {G : WeldedInstance n} {u w : ℕ} :
    Edge.weld u w ∈ G.edges ↔ (u, w) ∈ G.weld := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges]

lemma edge_endpoints {n : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e : Edge} (he : e ∈ G.edges) :
    IsVertex n e.tail ∧ IsVertex n (e.head n) ∧
      (col n e.tail + 1 = col n (e.head n) ∨ col n (e.head n) + 1 = col n e.tail) := by
  cases e with
  | tree v =>
    have hv := tree_mem_iff.mp he
    cases hp : parent n v with
    | none => simp [hp] at hv
    | some p =>
      have hs := parent_spec hp
      simp only [Edge.tail, Edge.head, hp, Option.getD_some]
      exact ⟨hs.1, hs.2.1, hs.2.2.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)⟩
  | weld u w =>
    have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
    dsimp only at hw
    simp only [Edge.tail, Edge.head]
    exact ⟨hw.1, hw.2.2.1, Or.inl (by omega)⟩

lemma tree_head_col {n : ℕ} {G : WeldedInstance n} {v : ℕ}
    (he : Edge.tree v ∈ G.edges) :
    col n ((Edge.tree v).head n) = if col n v ≤ n then col n v - 1 else col n v + 1 := by
  have hv := tree_mem_iff.mp he
  cases hp : parent n v with
  | none => simp [hp] at hv
  | some p =>
    have hs := (parent_spec hp).2.2
    simp only [Edge.head, hp, Option.getD_some]
    rcases hs with h | h
    · rw [if_pos h.2]
      omega
    · rw [if_neg (by omega : ¬ col n v ≤ n)]
      omega

lemma same_class_cols {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e e' : Edge} (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hclass : G.bEdge l e = G.bEdge l e') (hnone : G.bEdge l e ≠ none) :
    col n e.tail = col n e'.tail ∧ col n (e.head n) = col n (e'.head n) := by
  cases e with
  | tree v =>
    have hv : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      simp only [WeldedInstance.bEdge, if_neg h, ne_eq, not_true_eq_false] at hnone
    cases e' with
    | tree w =>
      have hw : n - l ≤ col n w ∧ col n w ≤ n + l := by
        by_contra h
        simp only [WeldedInstance.bEdge, if_pos hv, if_neg h, reduceCtorEq] at hclass
      have hc : col n v = col n w := by
        have hboth : col n v = col n w ∧ G.color (.tree v) = G.color (.tree w) := by
          simpa only [WeldedInstance.bEdge, if_pos hv, if_pos hw,
            Option.some.injEq, EdgeClass.tr.injEq] using hclass
        exact hboth.1
      refine ⟨hc, ?_⟩
      rw [tree_head_col he, tree_head_col he', hc]
    | weld u w => simp [WeldedInstance.bEdge, hv] at hclass
  | weld u w =>
    cases e' with
    | tree v =>
      simp only [WeldedInstance.bEdge] at hclass
      split at hclass <;> simp_all
    | weld u' w' =>
      have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
      have hw' := hG.1.1 (u', w') (weld_mem_iff.mp he')
      dsimp only at hw hw'
      simp only [Edge.tail, Edge.head]
      exact ⟨by omega, by omega⟩

end WeldedPath.LoopProof

end


-- Solutions.WeldedPathOracleSteps
section

namespace WeldedPath.LoopProof

open QAlgorithms WeldedInstance

theorem Nb_col_le {n l : ℕ} (G : WeldedInstance n) (hG : G.IsValid)
    (π : Equiv.Perm G.edges) (hπ : G.IsEdgePerm l π) (v : ℕ) (α : Fin 3) :
    col n (G.Nb l π v α) ≤ col n v + 1 := by
  classical
  by_cases hv : IsVertex n v
  · simp only [WeldedInstance.Nb, hv, not_true_eq_false, if_false]
    cases hsel : G.eAlpha v α with
    | none => simp
    | some e =>
      simp only
      by_cases he : e ∈ G.edges
      · simp only [dif_pos he]
        by_cases hb : G.bEdge l e = none
        · simp only [if_pos hb]
          have hs := (edge_endpoints hG he).2.2
          split_ifs with ht hh
          · rw [ht]
            omega
          · rw [hh]
            omega
          · omega
        · simp only [if_neg hb]
          have hclasses := (hπ ⟨e, he⟩).1
          have hcols := same_class_cols hG he (π ⟨e, he⟩).property hclasses.symm hb
          have hs := (edge_endpoints hG he).2.2
          split_ifs with ht hh
          · rw [ht]
            omega
          · have hclasses' : G.bEdge l (π.symm ⟨e, he⟩).val = G.bEdge l e := by
              have h := (hπ (π.symm ⟨e, he⟩)).1
              simpa only [Equiv.apply_symm_apply] using h.symm
            have hcols' := same_class_cols hG he (π.symm ⟨e, he⟩).property
              hclasses'.symm hb
            rw [hh]
            omega
          · omega
      · simp [he]
  · simp [WeldedInstance.Nb, hv]

theorem F_col_le {n l : ℕ} (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (hπ : G.IsEdgePerm l σ.2)
    (z : Label n) (α : Fin 3) :
    col n (σ.1.symm (G.F l σ z α)).val ≤ col n (σ.1.symm z).val + 1 := by
  unfold WeldedInstance.F
  split_ifs with hb
  · simpa only [Equiv.symm_apply_apply] using Nb_col_le G hG σ.2 hπ (σ.1.symm z).val α
  · omega

theorem walk_column_distance {n l : ℕ} (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (hπ : G.IsEdgePerm l σ.2)
    {z : Label n} {xs : List (Fin 3 × Qubits (2 * n + 1))}
    (hw : G.WalkFrom l σ z xs) :
    2 * n + 1 ≤ col n (σ.1.symm z).val + xs.length := by
  induction xs generalizing z with
  | nil =>
    change z = σ.1 (exitLabelIdx n) at hw
    subst z
    simp only [Equiv.symm_apply_apply, exitLabelIdx, List.length_nil, Nat.add_zero]
    exact (col_exit n).ge
  | cons s xs ih =>
    obtain ⟨hb, hf, _, ht⟩ := hw
    have hstep := F_col_le G hG σ hπ z s.1
    rw [hf] at hstep
    have htail := ih ht
    simp only [List.length_cons]
    omega

theorem walk_length_lower {n l : ℕ} (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (hσ : σ ∈ G.singSupport l)
    {xs : List (Fin 3 × Qubits (2 * n + 1))} (hw : G.WalkFrom l σ 0 xs) :
    n ≤ xs.length := by
  classical
  have hs : σ.1 0 = 0 ∧ G.IsEdgePerm l σ.2 := by
    have hm := (Finset.mem_filter.mp hσ).1
    exact (Finset.mem_filter.mp hm).2
  have hz : σ.1.symm 0 = 0 := by
    apply σ.1.injective
    simpa only [Equiv.apply_symm_apply] using hs.1.symm
  have hlen := walk_column_distance G hG σ hs.2 hw
  rw [hz] at hlen
  simp only [Fin.val_zero, col_zero, Nat.zero_add] at hlen
  omega

end WeldedPath.LoopProof

end


-- Solutions.WeldedPathWalkVerifier
section

namespace WeldedPath.LoopProof

open QAlgorithms WeldedInstance Supplement

theorem walk_labels_bound {n l : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    {z : Label n} {xs : List (Fin 3 × Qubits (2 * n + 1))}
    (hw : G.WalkFrom l σ z xs) :
    ∀ s ∈ xs, bitsToNat s.2 ≤ labelBound n := by
  induction xs generalizing z with
  | nil => simp
  | cons s xs ih =>
    obtain ⟨hb, _, _, ht⟩ := hw
    intro t htmem
    rcases List.mem_cons.mp htmem with rfl | htmem
    · omega
    · exact ih ht t htmem

theorem walk_step_getD {n l : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    {z : Label n} {xs : List (Fin 3 × Qubits (2 * n + 1))}
    (hw : G.WalkFrom l σ z xs) (i : ℕ) (hi : i < xs.length) :
    let zs := z.val :: xs.map (fun s => bitsToNat s.2)
    Fnat l G σ (zs.getD i 0) ((xs.getD i (0, 0)).1) = zs.getD (i + 1) 0 ∧
      zs.getD (i + 1) 0 ≠ zs.getD i 0 := by
  induction xs generalizing z i with
  | nil => simp at hi
  | cons s xs ih =>
    obtain ⟨hb, hf, hne, ht⟩ := hw
    cases i with
    | zero =>
      simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ]
      constructor
      · simp only [Fnat, dif_pos z.isLt]
        exact congrArg Fin.val hf
      · intro heq
        apply hne
        exact Fin.ext heq
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simpa only [List.map_cons, List.getD_cons_succ, Nat.succ_eq_add_one] using
        ih ht i hi'

theorem walk_last_getD {n l : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    {z : Label n} {xs : List (Fin 3 × Qubits (2 * n + 1))}
    (hw : G.WalkFrom l σ z xs) :
    (z.val :: xs.map (fun s => bitsToNat s.2)).getD xs.length 0 =
      (σ.1 (exitLabelIdx n)).val := by
  induction xs generalizing z with
  | nil =>
    simp only [WeldedInstance.WalkFrom] at hw
    simpa using congrArg Fin.val hw
  | cons s xs ih =>
    obtain ⟨hb, _, _, ht⟩ := hw
    simpa only [List.map_cons, List.length_cons, List.getD_cons_succ] using ih ht

theorem accepts_of_walk {n l : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (xs : List (Fin 3 × Qubits (2 * n + 1)))
    (hw : G.WalkFrom l σ 0 xs) (hnd : (pathLabels xs).Nodup) (hlen : n ≤ xs.length)
    (hdegree : (Finset.univ.filter fun α : Fin 3 =>
      Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠ (σ.1 (exitLabelIdx n)).val).card = 2)
    (q : ℕ) : Accepts39 l G σ q xs := by
  classical
  refine ⟨⟨walk_labels_bound G σ hw, hnd, hlen⟩, ?_, ?_⟩
  · intro _
    constructor
    · intro i hi
      exact (walk_step_getD G σ hw i hi).1
    · have hend := walk_last_getD G σ hw
      change (pathLabels xs).getD xs.length 0 = _ at hend
      simpa only [hend] using hdegree
  · intro hlong i _ hi
    have his : i < xs.length := by omega
    obtain ⟨heq, hne⟩ := walk_step_getD G σ hw i his
    refine ⟨(xs.getD i (0, 0)).1, ?_⟩
    exact fun h => hne (heq.symm.trans h)

end WeldedPath.LoopProof

end


-- Solutions.WeldedPathExitDegree
section

namespace WeldedPath.LoopProof

open WeldedInstance

lemma exit_col (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma exit_parent_none (n : ℕ) : parent n (exitIdx n) = none := by
  have h1 : ¬ (IsVertex n (exitIdx n) ∧ 1 ≤ col n (exitIdx n) ∧
      col n (exitIdx n) ≤ n) := by rw [exit_col]; omega
  have h2 : ¬ (IsVertex n (exitIdx n) ∧ n + 1 ≤ col n (exitIdx n) ∧
      col n (exitIdx n) ≤ 2 * n) := by rw [exit_col]; omega
  rw [parent, if_neg h1, if_neg h2]

lemma root_size_bounds (n : ℕ) (hn : 2 ≤ n) :
    4 ≤ 2 ^ (n + 1) ∧ 2 ^ (n + 1) + 1 < numV n := by
  have hp : 4 ≤ 2 ^ (n + 1) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨hp, ?_⟩
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma exit_isVertex (n : ℕ) (hn : 2 ≤ n) : IsVertex n (exitIdx n) := by
  have h := root_size_bounds n hn
  unfold IsVertex exitIdx
  omega

lemma exit_child_col (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    col n (2 ^ (n + 1) + j) = 2 * n := by
  have hp := (root_size_bounds n hn).1
  have hlt : ¬2 ^ (n + 1) + j < 2 ^ (n + 1) - 1 := by omega
  have hdiff : 2 ^ (n + 1) + j - (2 ^ (n + 1) - 1) + 1 = j + 2 := by omega
  simp only [col, hlt, if_false, hdiff]
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with rfl | rfl <;> norm_num <;> omega

lemma exit_child_parent (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    parent n (2 ^ (n + 1) + j) = some (exitIdx n) := by
  have hv : IsVertex n (2 ^ (n + 1) + j) := by
    have h := (root_size_bounds n hn).2
    unfold IsVertex
    omega
  have hc := exit_child_col n hn j hj
  have hfirst : ¬(IsVertex n (2 ^ (n + 1) + j) ∧
      1 ≤ col n (2 ^ (n + 1) + j) ∧ col n (2 ^ (n + 1) + j) ≤ n) := by
    rw [hc]
    omega
  have hsecond : IsVertex n (2 ^ (n + 1) + j) ∧
      n + 1 ≤ col n (2 ^ (n + 1) + j) ∧ col n (2 ^ (n + 1) + j) ≤ 2 * n := by
    rw [hc]
    exact ⟨hv, by omega, le_refl _⟩
  rw [parent, if_neg hfirst, if_pos hsecond]
  simp [Nat.add_sub_cancel_left, show j / 2 = 0 by omega, exitIdx]

lemma exit_child_edge (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n)
    (j : ℕ) (hj : j ≤ 1) : Edge.tree (2 ^ (n + 1) + j) ∈ G.edges := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨2 ^ (n + 1) + j, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · have h := (root_size_bounds n hn).2
    omega
  · rw [exit_child_parent n hn j hj]
    rfl

lemma exit_child_incident (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    (Edge.tree (2 ^ (n + 1) + j)).Incident n (exitIdx n) := by
  right
  simp [Edge.head, exit_child_parent n hn j hj]

lemma exit_child_bEdge (n l : ℕ) (hn : 2 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (j : ℕ) (hj : j ≤ 1) (hn4 : 4 ≤ n) :
    G.bEdge l (.tree (2 ^ (n + 1) + j)) = none := by
  have h : ¬(n - l ≤ col n (2 ^ (n + 1) + j) ∧
      col n (2 ^ (n + 1) + j) ≤ n + l) := by
    rw [exit_child_col n hn j hj]
    omega
  rw [WeldedInstance.bEdge, if_neg h]

lemma eAlpha_of_edge {n : ℕ} (G : WeldedInstance n) (hG : G.IsProperColoring)
    (e : Edge) (he : e ∈ G.edges) (v : ℕ) (hi : e.Incident n v) :
    G.eAlpha v (G.color e) = some e := by
  classical
  unfold WeldedInstance.eAlpha
  split_ifs with h
  · congr 1
    have hs := Classical.choose_spec h
    by_contra hne
    exact hG (Classical.choose h) hs.1 e he hne ⟨v, hs.2.2, hi⟩ hs.2.1
  · exact False.elim (h ⟨e, he, rfl, hi⟩)

lemma exit_incident_cases (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n)
    (hG : G.IsValid) (e : Edge) (he : e ∈ G.edges) (hi : e.Incident n (exitIdx n)) :
    e = .tree (2 ^ (n + 1)) ∨ e = .tree (2 ^ (n + 1) + 1) := by
  classical
  cases e with
  | tree v =>
    have ht : v < numV n ∧ (parent n v).isSome := by
      simpa [WeldedInstance.edges, treeEdges, weldEdges] using he
    cases hp : parent n v with
    | none => simp [hp] at ht
    | some p =>
      have hne : v ≠ exitIdx n := by
        intro hv
        subst v
        rw [exit_parent_none] at hp
        contradiction
      have hvr : exitIdx n = p := by
        simpa [Edge.Incident, Edge.tail, Edge.head, hp, Ne.symm hne] using hi
      have hpar : parent n v = some (exitIdx n) := by simpa [hvr] using hp
      rcases parent_eq_exit_imp hpar with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | weld u w =>
    have hw : (u, w) ∈ G.weld := by
      simpa [WeldedInstance.edges, treeEdges, weldEdges] using he
    rcases hG.1.1 (u, w) hw with ⟨hu, hcu, hw', hcw⟩
    change col n u = n at hcu
    change col n w = n + 1 at hcw
    have hc := exit_col n
    rcases hi with hi | hi
    · change exitIdx n = u at hi
      rw [hi] at hc
      omega
    · change exitIdx n = w at hi
      rw [hi] at hc
      omega

lemma exit_colors_ne (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n) (hG : G.IsValid) :
    G.color (.tree (2 ^ (n + 1))) ≠ G.color (.tree (2 ^ (n + 1) + 1)) := by
  apply hG.2
    (.tree (2 ^ (n + 1))) (by simpa using exit_child_edge n hn G 0 (by omega))
    (.tree (2 ^ (n + 1) + 1)) (exit_child_edge n hn G 1 (by omega))
  · simp
  · exact ⟨exitIdx n, by simpa using exit_child_incident n hn 0 (by omega),
      exit_child_incident n hn 1 (by omega)⟩

lemma exit_neighbor (n l : ℕ) (hn : 4 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid) (π : Equiv.Perm G.edges) (α : Fin 3) :
    G.Nb l π (exitIdx n) α =
      if α = G.color (.tree (2 ^ (n + 1))) then 2 ^ (n + 1)
      else if α = G.color (.tree (2 ^ (n + 1) + 1)) then 2 ^ (n + 1) + 1
      else exitIdx n := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hv := exit_isVertex n hn2
  have hp0 := exit_child_parent n hn2 0 (by omega)
  have hp1 := exit_child_parent n hn2 1 (by omega)
  have hb0 := exit_child_bEdge n l hn2 hl G 0 (by omega) hn
  have hb1 := exit_child_bEdge n l hn2 hl G 1 (by omega) hn
  have he0 : Edge.tree (2 ^ (n + 1)) ∈ G.edges := by
    simpa using exit_child_edge n hn2 G 0 (by omega)
  have he1 := exit_child_edge n hn2 G 1 (by omega)
  have hi0 : (Edge.tree (2 ^ (n + 1))).Incident n (exitIdx n) := by
    simpa using exit_child_incident n hn2 0 (by omega)
  have hi1 := exit_child_incident n hn2 1 (by omega)
  have hne0 : exitIdx n ≠ 2 ^ (n + 1) := by
    have h := (root_size_bounds n hn2).1
    unfold exitIdx
    omega
  have hne1 : exitIdx n ≠ 2 ^ (n + 1) + 1 := by
    unfold exitIdx
    omega
  by_cases h0 : α = G.color (.tree (2 ^ (n + 1)))
  · subst α
    have ha := eAlpha_of_edge G hG.2 _ he0 _ hi0
    simp only [Nat.add_zero] at hp0 hb0
    simp [Nb, hv, ha, he0, hb0, Edge.tail, Edge.head, hp0, hne0]
  · by_cases h1 : α = G.color (.tree (2 ^ (n + 1) + 1))
    · subst α
      have ha := eAlpha_of_edge G hG.2 _ he1 _ hi1
      simp [Nb, hv, ha, he1, hb1, Edge.tail, Edge.head, hp1, hne1, h0]
    · have ha : G.eAlpha (exitIdx n) α = none := by
        unfold WeldedInstance.eAlpha
        split_ifs with h
        · obtain ⟨e, he, hc, hi⟩ := h
          rcases exit_incident_cases n hn2 G hG e he hi with rfl | rfl
          · exact False.elim (h0 hc.symm)
          · exact False.elim (h1 hc.symm)
        · rfl
      simp [Nb, hv, ha, h0, h1]

lemma exit_child_lt_label (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n + 1) + 1 < labelBound n + 1 := by
  have hp : 2 ^ (n + 2) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ] at hp
  have hb := (root_size_bounds n hn).1
  unfold labelBound
  omega

lemma exit_Fnat_ne_iff (n l : ℕ) (hn : 4 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (α : Fin 3) :
    Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠ (σ.1 (exitLabelIdx n)).val ↔
      α = G.color (.tree (2 ^ (n + 1))) ∨
      α = G.color (.tree (2 ^ (n + 1) + 1)) := by
  classical
  have hb := exit_child_lt_label n (by omega)
  have hr : exitIdx n < labelBound n + 1 := (exitLabelIdx n).isLt
  have hN : G.Nb l σ.2 (exitIdx n) α < labelBound n + 1 := by
    rw [exit_neighbor n l hn hl G hG σ.2 α]
    split_ifs <;> omega
  have hne0 : 2 ^ (n + 1) ≠ exitIdx n := by
    have hp := (root_size_bounds n (by omega)).1
    unfold exitIdx
    omega
  have hne1 : 2 ^ (n + 1) + 1 ≠ exitIdx n := by unfold exitIdx; omega
  have heq : Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
      (σ.1 (exitLabelIdx n)).val ↔ G.Nb l σ.2 (exitIdx n) α ≠ exitIdx n := by
    unfold Supplement.Fnat
    rw [dif_pos (σ.1 (exitLabelIdx n)).isLt]
    change (G.F l σ (σ.1 (exitLabelIdx n)) α).val ≠ (σ.1 (exitLabelIdx n)).val ↔ _
    unfold WeldedInstance.F
    simp only [Equiv.symm_apply_apply]
    change (if h : G.Nb l σ.2 (exitIdx n) α < labelBound n + 1 then
      σ.1 ⟨G.Nb l σ.2 (exitIdx n) α, h⟩ else σ.1 (exitLabelIdx n)).val ≠
        (σ.1 (exitLabelIdx n)).val ↔ _
    rw [dif_pos hN]
    constructor
    · intro hnot hval
      apply hnot
      have hx : (⟨G.Nb l σ.2 (exitIdx n) α, hN⟩ : Label n) = exitLabelIdx n :=
        Fin.ext hval
      rw [hx]
    · intro hnot hval
      apply hnot
      have hx := σ.1.injective (Fin.ext hval)
      exact congrArg Fin.val hx
  rw [heq, exit_neighbor n l hn hl G hG σ.2 α]
  split_ifs with h0 h1 <;> simp_all

theorem exit_degree (n l : ℕ) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    (Finset.univ.filter fun α : Fin 3 =>
      Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
        (σ.1 (exitLabelIdx n)).val).card = 2 := by
  classical
  have hset : (Finset.univ.filter fun α : Fin 3 =>
      Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
        (σ.1 (exitLabelIdx n)).val) =
      {G.color (.tree (2 ^ (n + 1))), G.color (.tree (2 ^ (n + 1) + 1))} := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, exit_Fnat_ne_iff n l (by omega) hln G hG σ α]
  rw [hset]
  simp [exit_colors_ne n (by omega) G hG]

end WeldedPath.LoopProof

end

open WeldedPath QAlgorithms WeldedPath.Supplement WeldedPath.LoopProof

theorem solution
    (n l : ℕ) (hnEven : Even n) (hn : 16 ≤ n) (hl : 2 ≤ l) (hlmax : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid) :
    ∃ erase : List (Fin 3 × Qubits (2 * n + 1)) →
        List (Fin 3 × Qubits (2 * n + 1)),
      ∀ σ : Equiv.Perm (Label n) × Equiv.Perm G.edges,
        σ ∈ G.singSupport l →
        ∀ (xs : List (Fin 3 × Qubits (2 * n + 1))) (q : ℕ), 1 ≤ q →
          G.IsEntranceExitWalk l σ xs → Accepts39 l G σ q (erase xs) := by
  refine ⟨LoopProof.erase, ?_⟩
  intro σ hσ xs q _ hsuccess
  have hw := LoopProof.erase_walkFrom l G σ xs hsuccess.2
  exact LoopProof.accepts_of_walk G σ (LoopProof.erase xs) hw
    (LoopProof.erase_nodup xs) (LoopProof.walk_length_lower G hG σ hσ hw)
    (LoopProof.exit_degree n l hn hl hlmax G hG σ) q
