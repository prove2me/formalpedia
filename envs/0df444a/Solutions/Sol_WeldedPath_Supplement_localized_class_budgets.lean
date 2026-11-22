-- Prove2me | solution 1 for WeldedPath.Supplement.localized_class_budgets
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-22T16:22:24.888648+00:00
-- url     : https://prove2.me/submissions/a28a4382-500f-4681-b632-fb7fc24ff6a3

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood
import Theorems.Thm_WeldedPath_observation_3_3

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

namespace WeldedPath.WeldClasses

open Classical LoopProof

theorem mem_weld_class {n l : ℕ} {G : WeldedInstance n} (α : Fin 3) (e : Edge) :
    e ∈ G.classEdges l (.wld α) ↔ e ∈ G.weldEdges ∧ G.color e = α := by
  cases e with
  | tree v =>
    by_cases h : n - l ≤ col n v ∧ col n v ≤ n + l <;>
      simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.weldEdges, h]
  | weld u w =>
    simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.edges,
      WeldedInstance.treeEdges, WeldedInstance.weldEdges]

theorem weld_classes_disjoint {n l : ℕ} (G : WeldedInstance n) {α β : Fin 3}
    (h : α ≠ β) : Disjoint (G.classEdges l (.wld α)) (G.classEdges l (.wld β)) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact h (((mem_weld_class α e).mp he).2.symm.trans ((mem_weld_class β e).mp he').2)

theorem tail_injective {n l : ℕ} {G : WeldedInstance n} (hG : G.IsProperColoring)
    (α : Fin 3) : Set.InjOn Edge.tail (G.classEdges l (.wld α)) := by
  intro e he e' he' htail
  by_contra hne
  have hc := hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.tail, Or.inl rfl, Or.inl htail⟩
  exact hc (((mem_weld_class α e).mp he).2.trans ((mem_weld_class α e').mp he').2.symm)

theorem head_injective {n l : ℕ} {G : WeldedInstance n} (hG : G.IsProperColoring)
    (α : Fin 3) : Set.InjOn (Edge.head n) (G.classEdges l (.wld α)) := by
  intro e he e' he' hhead
  by_contra hne
  have hc := hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.head n, Or.inr rfl, Or.inr hhead⟩
  exact hc (((mem_weld_class α e).mp he).2.trans ((mem_weld_class α e').mp he').2.symm)

theorem left_leaf_bounds {n v : ℕ} (hv : IsVertex n v) (hc : col n v = n) :
    2 ^ n - 1 ≤ v ∧ v < 2 ^ (n + 1) - 1 := by
  have hleft : v < 2 ^ (n + 1) - 1 := by
    by_contra h
    have hh := col_right_ge n v hv (by omega)
    omega
  have hlog : Nat.log 2 (v + 1) = n := by simpa [col, hleft] using hc
  have hh := Nat.pow_log_le_self 2 (by omega : v + 1 ≠ 0)
  rw [hlog] at hh
  exact ⟨by omega, hleft⟩

theorem left_leaf_of_bounds {n v : ℕ} (hn : 1 ≤ n)
    (hlo : 2 ^ n - 1 ≤ v) (hhi : v < 2 ^ (n + 1) - 1) :
    IsVertex n v ∧ col n v = n ∧ parent n v = some ((v - 1) / 2) := by
  have hpow := Nat.two_pow_pos n
  have hroot := pow_root_ge_two n
  have hv : IsVertex n v := by
    rw [IsVertex, numV_eq]
    omega
  have hc : col n v = n := by
    rw [col, if_pos hhi]
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  refine ⟨hv, hc, ?_⟩
  simp [parent, hv, hc, hn]

theorem weld_class_tail_bounds {n l : ℕ} {G : WeldedInstance n} (hG : G.IsWeld)
    {α : Fin 3} {e : Edge} (he : e ∈ G.classEdges l (.wld α)) :
    2 ^ n - 1 ≤ e.tail ∧ e.tail < 2 ^ (n + 1) - 1 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ((mem_weld_class α e).mp he).1
  have hh := hG.1 p hp
  exact left_leaf_bounds hh.1 hh.2.1

theorem weld_class_card_le {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (α : Fin 3) : (G.classEdges l (.wld α)).card ≤ 2 ^ n := by
  have hh := Finset.card_le_card_of_injOn Edge.tail
    (s := G.classEdges l (.wld α)) (t := Finset.Ico (2 ^ n - 1) (2 ^ (n + 1) - 1))
    (fun e he => Finset.mem_Ico.mpr (weld_class_tail_bounds hG.1 he))
    (tail_injective hG.2 α)
  have hp := Nat.two_pow_pos n
  have hcard : (Finset.Ico (2 ^ n - 1) (2 ^ (n + 1) - 1)).card = 2 ^ n := by
    rw [Nat.card_Ico, pow_succ]
    omega
  simpa only [hcard] using hh

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem weld_color_at_leaf {n l v : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (hv : IsVertex n v) (hc : col n v = n) (α : Fin 3)
    (htc : G.color (.tree v) ≠ α) :
    ∃ e ∈ G.classEdges l (.wld α), e.tail = v := by
  have hbounds := left_leaf_bounds hv hc
  have hpv := (left_leaf_of_bounds hn hbounds.1 hbounds.2).2.2
  have ht : Edge.tree v ∈ G.edges := tree_mem_iff.mpr ⟨hv, by simp [hpv]⟩
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp (hG.1.2.1 v ⟨hv, Or.inl hc⟩)
  have hp : p ∈ G.weld ∧ (p.1 = v ∨ p.2 = v) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hq : q ∈ G.weld ∧ (q.1 = v ∨ q.2 = v) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hpt : p.1 = v := by
    rcases hp.2 with h | h
    · exact h
    · have hh := (hG.1.1 p hp.1).2.2.2
      rw [h, hc] at hh
      omega
  have hqt : q.1 = v := by
    rcases hq.2 with h | h
    · exact h
    · have hh := (hG.1.1 q hq.1).2.2.2
      rw [h, hc] at hh
      omega
  have hep : Edge.weld p.1 p.2 ∈ G.edges := weld_mem_iff.mpr hp.1
  have heq : Edge.weld q.1 q.2 ∈ G.edges := weld_mem_iff.mpr hq.1
  have htp := hG.2 (.tree v) ht (.weld p.1 p.2) hep (by simp)
    ⟨v, Or.inl rfl, Or.inl hpt.symm⟩
  have htq := hG.2 (.tree v) ht (.weld q.1 q.2) heq (by simp)
    ⟨v, Or.inl rfl, Or.inl hqt.symm⟩
  have hpq' : Edge.weld p.1 p.2 ≠ Edge.weld q.1 q.2 := by
    intro h
    exact hpq (Prod.ext (congrArg Edge.tail h) (congrArg (Edge.head n) h))
  have hpqc := hG.2 (.weld p.1 p.2) hep (.weld q.1 q.2) heq hpq'
    ⟨v, Or.inl hpt.symm, Or.inl hqt.symm⟩
  rcases three_colors_cover (G.color (.tree v)) (G.color (.weld p.1 p.2))
      (G.color (.weld q.1 q.2)) α htp htq hpqc with h | h | h
  · exact (htc h.symm).elim
  · refine ⟨.weld p.1 p.2, (mem_weld_class α _).mpr ⟨?_, h.symm⟩, hpt⟩
    exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩
  · refine ⟨.weld q.1 q.2, (mem_weld_class α _).mpr ⟨?_, h.symm⟩, hqt⟩
    exact Finset.mem_image.mpr ⟨q, hq.1, rfl⟩

theorem weld_class_card_ge {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) : 2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = 2 * 2 ^ (n - 1) := by rw [pow_succ, Nat.mul_comm]
  have hpow' : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hpos := Nat.two_pow_pos (n - 1)
  have hpairs (j : Fin (2 ^ (n - 1))) :
      ∃ e ∈ G.classEdges l (.wld α),
        e.tail = 2 ^ n - 1 + 2 * j.val ∨ e.tail = 2 ^ n - 1 + 2 * j.val + 1 := by
    let u := 2 ^ n - 1 + 2 * j.val
    have hj := j.isLt
    have hu := left_leaf_of_bounds (v := u) hn (by dsimp [u]; omega)
      (by dsimp [u]; omega)
    have hu' := left_leaf_of_bounds (v := u + 1) hn (by dsimp [u]; omega)
      (by dsimp [u]; omega)
    have ht : Edge.tree u ∈ G.edges := tree_mem_iff.mpr ⟨hu.1, by simp [hu.2.2]⟩
    have ht' : Edge.tree (u + 1) ∈ G.edges := tree_mem_iff.mpr ⟨hu'.1, by simp [hu'.2.2]⟩
    have hparent : (u - 1) / 2 = u / 2 := by dsimp [u]; omega
    have hcolors : G.color (.tree u) ≠ G.color (.tree (u + 1)) := by
      apply hG.2 (.tree u) ht (.tree (u + 1)) ht' (by simp)
      refine ⟨(u - 1) / 2, Or.inr ?_, Or.inr ?_⟩
      · simp [Edge.head, hu.2.2]
      · simp [Edge.head, hu'.2.2, hparent]
    by_cases hcu : G.color (.tree u) ≠ α
    · obtain ⟨e, he, htail⟩ := weld_color_at_leaf hG hn hu.1 hu.2.1 α hcu
      exact ⟨e, he, Or.inl htail⟩
    · have hcu' : G.color (.tree (u + 1)) ≠ α := by
        intro h
        exact hcolors ((not_ne_iff.mp hcu).trans h.symm)
      obtain ⟨e, he, htail⟩ := weld_color_at_leaf hG hn hu'.1 hu'.2.1 α hcu'
      exact ⟨e, he, Or.inr htail⟩
  choose f hf using hpairs
  let F : Fin (2 ^ (n - 1)) → G.classEdges l (.wld α) := fun j => ⟨f j, (hf j).1⟩
  have hinj : Function.Injective F := by
    intro j k h
    have heq : f j = f k := congrArg Subtype.val h
    have ht := congrArg Edge.tail heq
    rcases (hf j).2 with hj | hj <;> rcases (hf k).2 with hk | hk <;>
      apply Fin.ext <;> omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hinj

theorem weld_class_card_bounds {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) :
    2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card ∧
      (G.classEdges l (.wld α)).card ≤ 2 ^ n :=
  ⟨weld_class_card_ge hG hn α, weld_class_card_le hG α⟩

end WeldedPath.WeldClasses

namespace WeldedPath.NearWeldClasses

open Classical LoopProof

/-- Heap coordinates in either of the two binary trees. -/
def heapNode (n : ℕ) (right : Bool) (u : ℕ) : ℕ :=
  (if right then 2 ^ (n + 1) - 1 else 0) + u

def heapCol (n : ℕ) (right : Bool) (d : ℕ) : ℕ :=
  if right then 2 * n + 1 - d else d

theorem heap_node_spec {n d u : ℕ} (right : Bool)
    (hd : 1 ≤ d) (hdn : d ≤ n)
    (hlo : 2 ^ d - 1 ≤ u) (hhi : u < 2 ^ (d + 1) - 1) :
    IsVertex n (heapNode n right u) ∧
      col n (heapNode n right u) = heapCol n right d ∧
      parent n (heapNode n right u) = some (heapNode n right ((u - 1) / 2)) := by
  have hroot := pow_root_ge_two n
  have hpow := Nat.two_pow_pos d
  have hdpow : 2 ≤ 2 ^ d := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  have hupper : u < 2 ^ (n + 1) - 1 := by
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2)
      (show d + 1 ≤ n + 1 by omega)
    omega
  have hlog : Nat.log 2 (u + 1) = d :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have hup : 1 ≤ u := by omega
  cases right with
  | false =>
    simp only [heapNode, Bool.false_eq_true, if_false, zero_add, heapCol]
    have hv : IsVertex n u := by rw [IsVertex, numV_eq]; omega
    have hc : col n u = d := by simp [col, hupper, hlog]
    refine ⟨hv, hc, ?_⟩
    simp [parent, hv, hc, hd, hdn]
  | true =>
    simp only [heapNode, if_true, heapCol]
    let R := 2 ^ (n + 1) - 1
    have hv : IsVertex n (R + u) := by
      rw [IsVertex, numV_eq]
      dsimp [R]
      omega
    have hc : col n (R + u) = 2 * n + 1 - d := by
      rw [col, if_neg (by dsimp [R]; omega)]
      change 2 * n + 1 - Nat.log 2 (R + u - R + 1) = _
      rw [Nat.add_sub_cancel_left, hlog]
    refine ⟨hv, hc, ?_⟩
    have hfirst : ¬ (IsVertex n (R + u) ∧ 1 ≤ col n (R + u) ∧
        col n (R + u) ≤ n) := by rw [hc]; omega
    have hsecond : IsVertex n (R + u) ∧ n + 1 ≤ col n (R + u) ∧
        col n (R + u) ≤ 2 * n := by rw [hc]; exact ⟨hv, by omega, by omega⟩
    change parent n (R + u) = some (R + (u - 1) / 2)
    rw [parent, if_neg hfirst, if_pos hsecond]
    congr 1
    dsimp [R]
    omega

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem child_color_of_parent_ne {n : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (p a b : ℕ)
    (hp : Edge.tree p ∈ G.edges) (ha : Edge.tree a ∈ G.edges)
    (hb : Edge.tree b ∈ G.edges) (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hapar : parent n a = some p) (hbpar : parent n b = some p)
    (α : Fin 3) (hc : G.color (.tree p) ≠ α) :
    G.color (.tree a) = α ∨ G.color (.tree b) = α := by
  have hca := hG (.tree p) hp (.tree a) ha (by simpa using hpa)
    ⟨p, Or.inl rfl, Or.inr (by simp [Edge.head, hapar])⟩
  have hcb := hG (.tree p) hp (.tree b) hb (by simpa using hpb)
    ⟨p, Or.inl rfl, Or.inr (by simp [Edge.head, hbpar])⟩
  have hcab := hG (.tree a) ha (.tree b) hb (by simpa using hab)
    ⟨p, Or.inr (by simp [Edge.head, hapar]), Or.inr (by simp [Edge.head, hbpar])⟩
  rcases three_colors_cover _ _ _ α hca hcb hcab with h | h | h
  · exact (hc h.symm).elim
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem pow_two_levels {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n = 4 * 2 ^ (n - 2) ∧ 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  constructor
  · rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    omega
  · rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    omega

theorem quad_leaf_spec {n : ℕ} (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (k : Fin 4) :
    IsVertex n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) ∧
      col n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) = heapCol n right n ∧
      parent n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) =
        some (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val / 2)) := by
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hsucc : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hj := j.isLt
  have hk := k.isLt
  have hs := heap_node_spec (n := n) (d := n)
    (u := 2 ^ n - 1 + 4 * j.val + k.val) right (by omega) le_rfl (by omega) (by omega)
  have hdiv : (2 ^ n - 1 + 4 * j.val + k.val - 1) / 2 =
      2 ^ (n - 1) - 1 + 2 * j.val + k.val / 2 := by omega
  simpa only [hdiv] using hs

theorem quad_parent_spec {n : ℕ} (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (k : Fin 2) :
    IsVertex n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) ∧
      col n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) =
        heapCol n right (n - 1) ∧
      parent n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) =
        some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hsucc : 2 ^ ((n - 1) + 1) = 2 ^ n := congrArg (2 ^ ·) (by omega)
  have hj := j.isLt
  have hk := k.isLt
  have hs := heap_node_spec (n := n) (d := n - 1)
    (u := 2 ^ (n - 1) - 1 + 2 * j.val + k.val) right
    (by omega) (by omega) (by omega) (by omega)
  have hdiv : (2 ^ (n - 1) - 1 + 2 * j.val + k.val - 1) / 2 =
      2 ^ (n - 2) - 1 + j.val := by omega
  simpa only [hdiv] using hs

theorem leaf_quad_has_color {n : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (α : Fin 3) :
    ∃ k : Fin 4,
      G.color (.tree (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val))) = α := by
  let v (k : Fin 4) := heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)
  let p (k : Fin 2) := heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hv (k : Fin 4) : Edge.tree (v k) ∈ G.edges := by
    apply tree_mem_iff.mpr
    have hs := quad_leaf_spec hn right j k
    exact ⟨hs.1, by simp [v, hs.2.2]⟩
  have hpm (k : Fin 2) : Edge.tree (p k) ∈ G.edges := by
    apply tree_mem_iff.mpr
    have hs := quad_parent_spec hn right j k
    exact ⟨hs.1, by simp [p, hs.2.2]⟩
  have hpar0 : parent n (v 0) = some (p 0) := by
    simpa [v, p] using (quad_leaf_spec hn right j 0).2.2
  have hpar1 : parent n (v 1) = some (p 0) := by
    simpa [v, p] using (quad_leaf_spec hn right j 1).2.2
  have hpar2 : parent n (v 2) = some (p 1) := by
    simpa [v, p] using (quad_leaf_spec hn right j 2).2.2
  have hpar3 : parent n (v 3) = some (p 1) := by
    simpa [v, p] using (quad_leaf_spec hn right j 3).2.2
  have hpp0 : parent n (p 0) = some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
    simpa [p] using (quad_parent_spec hn right j 0).2.2
  have hpp1 : parent n (p 1) = some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
    simpa [p] using (quad_parent_spec hn right j 1).2.2
  have hpn : p 0 ≠ p 1 := by dsimp [p, heapNode]; omega
  have hpc : G.color (.tree (p 0)) ≠ G.color (.tree (p 1)) := by
    apply hG (.tree (p 0)) (hpm 0) (.tree (p 1)) (hpm 1) (by simpa using hpn)
    refine ⟨heapNode n right (2 ^ (n - 2) - 1 + j.val), Or.inr ?_, Or.inr ?_⟩ <;>
      simp [Edge.head, hpp0, hpp1]
  by_cases hc : G.color (.tree (p 0)) ≠ α
  · have hh := child_color_of_parent_ne hG (p 0) (v 0) (v 1) (hpm 0) (hv 0) (hv 1)
      (by dsimp [p, v, heapNode]; omega) (by dsimp [p, v, heapNode]; omega)
      (by dsimp [v, heapNode]; omega) hpar0 hpar1 α hc
    rcases hh with hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩
  · have hc' : G.color (.tree (p 1)) ≠ α := by
      intro hh
      exact hpc ((not_ne_iff.mp hc).trans hh.symm)
    have hh := child_color_of_parent_ne hG (p 1) (v 2) (v 3) (hpm 1) (hv 2) (hv 3)
      (by dsimp [p, v, heapNode]; omega) (by dsimp [p, v, heapNode]; omega)
      (by dsimp [v, heapNode]; omega) hpar2 hpar3 α hc'
    rcases hh with hh | hh
    · exact ⟨2, hh⟩
    · exact ⟨3, hh⟩

theorem tree_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (right : Bool)
    (hmid : n - l ≤ heapCol n right n ∧ heapCol n right n ≤ n + l)
    (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr (heapCol n right n) α)).card := by
  choose k hk using fun j : Fin (2 ^ (n - 2)) => leaf_quad_has_color hG hn right j α
  let v (j : Fin (2 ^ (n - 2))) := heapNode n right (2 ^ n - 1 + 4 * j.val + (k j).val)
  have hm (j : Fin (2 ^ (n - 2))) :
      Edge.tree (v j) ∈ G.classEdges l (.tr (heapCol n right n) α) := by
    have hs := quad_leaf_spec hn right j (k j)
    refine Finset.mem_filter.mpr ⟨tree_mem_iff.mpr ⟨hs.1, ?_⟩, ?_⟩
    · simp [v, hs.2.2]
    · change G.bEdge l (.tree (v j)) = some (.tr (heapCol n right n) α)
      simp only [WeldedInstance.bEdge]
      change (if n - l ≤ col n (v j) ∧ col n (v j) ≤ n + l then
        some (EdgeClass.tr (col n (v j)) (G.color (.tree (v j)))) else none) = _
      rw [show col n (v j) = heapCol n right n from hs.2.1, if_pos hmid]
      exact congrArg (fun c => some (EdgeClass.tr (heapCol n right n) c)) (hk j)
  let F : Fin (2 ^ (n - 2)) → G.classEdges l (.tr (heapCol n right n) α) :=
    fun j => ⟨.tree (v j), hm j⟩
  have hinj : Function.Injective F := by
    intro j j' heq
    have hv : v j = v j' := Edge.tree.inj (congrArg Subtype.val heq)
    have hj := (k j).isLt
    have hj' := (k j').isLt
    dsimp [v, heapNode] at hv
    apply Fin.ext
    omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hinj

theorem left_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr n α)).card := by
  exact tree_class_card_ge hG hn false ⟨Nat.sub_le n l, Nat.le_add_right n l⟩ α

theorem right_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (hl : 1 ≤ l) (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr (n + 1) α)).card := by
  have hc : heapCol n true n = n + 1 := by unfold heapCol; simp only [if_true]; omega
  have hh := tree_class_card_ge (l := l) hG hn true (by rw [hc]; constructor <;> omega) α
  simpa only [hc] using hh

theorem reciprocal_le_four_dyadic {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ^ (n - 2) ≤ m) :
    1 / (m : ℝ) ≤ 4 / (2 : ℝ) ^ n := by
  have hmp : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (Nat.two_pow_pos (n - 2)) hm)
  apply (div_le_div_iff₀ hmp (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  simp only [one_mul]
  have hp : 2 ^ n ≤ 4 * m := by
    rw [(pow_two_levels hn).1]
    exact Nat.mul_le_mul_left 4 hm
  exact_mod_cast hp

theorem left_class_reciprocal_le {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (α : Fin 3) :
    1 / ((G.classEdges l (.tr n α)).card : ℝ) ≤ 4 / (2 : ℝ) ^ n :=
  reciprocal_le_four_dyadic hn (left_class_card_ge hG hn α)

theorem right_class_reciprocal_le {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (hl : 1 ≤ l) (α : Fin 3) :
    1 / ((G.classEdges l (.tr (n + 1) α)).card : ℝ) ≤ 4 / (2 : ℝ) ^ n :=
  reciprocal_le_four_dyadic hn (right_class_card_ge hG hn hl α)

end WeldedPath.NearWeldClasses

namespace WeldedPath.Supplement.FirstFreeStep

open Classical WeldedInstance LoopProof NearWeldClasses

variable {n l : ℕ} {G : WeldedInstance n}

theorem tree_head_not_weld {w : ℕ} (he : Edge.tree w ∈ G.edges) :
    col n ((Edge.tree w).head n) ≠ n ∧ col n ((Edge.tree w).head n) ≠ n + 1 := by
  have hm := tree_mem_iff.mp he
  cases hp : parent n w with
  | none => simp [hp] at hm
  | some p =>
    have hs := (parent_spec hp).2.2
    simp only [Edge.head, hp, Option.getD_some]
    constructor <;> intro hc <;> rcases hs with hs | hs <;> omega

/-- At a weld vertex, an incident permuted edge belongs to one of exactly
three kinds of class: the left leaf-tree class, the right leaf-tree class,
or a weld class. -/
theorem class_of_incident_weld {u : ℕ} {e : Edge} {b : EdgeClass}
    (he : e ∈ G.classEdges l b) (hi : e.Incident n u) (hu : u ∈ Vweld n) :
    b = .tr n (G.color e) ∨ b = .tr (n + 1) (G.color e) ∨ b = .wld (G.color e) := by
  have he' := Finset.mem_filter.mp he
  have hu' := (Finset.mem_filter.mp hu).2
  cases e with
  | weld a c =>
    exact Or.inr (Or.inr (Option.some.inj he'.2.symm))
  | tree w =>
    have hc : col n w = n ∨ col n w = n + 1 := by
      rcases hi with hi | hi
      · change u = w at hi
        simpa only [hi] using hu'
      · have hne := tree_head_not_weld he'.1
        change u = (Edge.tree w).head n at hi
        rw [hi] at hu'
        exact (hu'.elim hne.1 hne.2).elim
    have hb : b = .tr (col n w) (G.color (.tree w)) := by
      have hh := he'.2
      simp only [WeldedInstance.bEdge] at hh
      split at hh
      · exact Option.some.inj hh.symm
      · simp at hh
    rcases hc with hc | hc
    · exact Or.inl (by simpa only [hc] using hb)
    · exact Or.inr (Or.inl (by simpa only [hc] using hb))

theorem class_card_ge_of_incident_weld (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    {u : ℕ} {e : Edge} {b : EdgeClass}
    (he : e ∈ G.classEdges l b) (hi : e.Incident n u) (hu : u ∈ Vweld n) :
    2 ^ (n - 2) ≤ (G.classEdges l b).card := by
  rcases class_of_incident_weld he hi hu with hb | hb | hb
  · rw [hb]
    exact left_class_card_ge hG.2 hn (G.color e)
  · rw [hb]
    exact right_class_card_ge hG.2 hn hl (G.color e)
  · rw [hb]
    apply le_trans _ (WeldClasses.weld_class_card_ge hG (by omega) (G.color e))
    exact Nat.pow_le_pow_right (by decide) (by omega)

end WeldedPath.Supplement.FirstFreeStep

namespace WeldedPath.Supplement.ReferenceSizes

open Classical LoopProof

theorem boundary_card_le {n l : ℕ} (hl : 1 ≤ l) (hln : l ≤ n) :
    (Vbd n l).card ≤ 6 * 2 ^ (n - l) := by
  let R := 2 ^ (n + 1) - 1
  have hsub : Vbd n l ⊆ Finset.range (2 ^ (n - l + 1)) ∪
      (Finset.range (2 ^ (n - l + 2))).image (fun v => R + v) := by
    intro v hv
    have hmem := Finset.mem_filter.mp hv
    have hV : IsVertex n v := Finset.mem_range.mp hmem.1
    by_cases hleft : v < R
    · apply Finset.mem_union_left
      have hcol := col_left_le n v hleft
      have hcl : col n v ≤ n - l := by
        rcases hmem.2 with h | h | h | h <;> omega
      have hd : Nat.log 2 (v + 1) ≤ n - l := by
        simpa only [col, if_pos (show v < 2 ^ (n + 1) - 1 from hleft)] using hcl
      have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (v + 1)
      have hm : 2 ^ (Nat.log 2 (v + 1) + 1) ≤ 2 ^ (n - l + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact Finset.mem_range.mpr (by omega)
    · apply Finset.mem_union_right
      have hright : R ≤ v := by omega
      have hcol := col_right_ge n v hV hright
      have hcl : n + l ≤ col n v := by
        rcases hmem.2 with h | h | h | h <;> omega
      have hd0 := log_right_le n v hV hright
      have hd : Nat.log 2 (v - R + 1) ≤ n - l + 1 := by
        simp only [col, if_neg (show ¬ v < 2 ^ (n + 1) - 1 from hleft)] at hcl
        dsimp [R] at *
        omega
      have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (v - R + 1)
      have hm : 2 ^ (Nat.log 2 (v - R + 1) + 1) ≤ 2 ^ (n - l + 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact Finset.mem_image.mpr ⟨v - R, Finset.mem_range.mpr (by omega), by omega⟩
  calc
    _ ≤ (Finset.range (2 ^ (n - l + 1)) ∪
        (Finset.range (2 ^ (n - l + 2))).image (fun v => R + v)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.range (2 ^ (n - l + 1))).card +
        ((Finset.range (2 ^ (n - l + 2))).image (fun v => R + v)).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.range (2 ^ (n - l + 1))).card +
        (Finset.range (2 ^ (n - l + 2))).card := Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by simp only [Finset.card_range, pow_add]; ring

end WeldedPath.Supplement.ReferenceSizes

namespace WeldedPath.Supplement.LocalizedClassBoundary

open Classical WeldedInstance

variable {n l : ℕ} {G : WeldedInstance n}

/-- Both structural endpoint sets of one permuted edge class. -/
def classBoundary (l : ℕ) (G : WeldedInstance n) (b : PClass n l) : Finset ℕ :=
  (G.classEdges l b.val).image Edge.tail ∪
    (G.classEdges l b.val).image (fun e => e.head n)

theorem mem_classBoundary_iff (b : PClass n l) (u : ℕ) :
    u ∈ classBoundary l G b ↔
      ∃ e ∈ G.classEdges l b.val, e.Incident n u := by
  constructor
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨e, he, Or.inl rfl⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, hi⟩
    rcases hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hi.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hi.symm⟩)

theorem classBoundary_card_le (b : PClass n l) :
    (classBoundary l G b).card ≤ 2 * classSize l G b := by
  calc
    _ ≤ ((G.classEdges l b.val).image Edge.tail).card +
        ((G.classEdges l b.val).image (fun e => e.head n)).card :=
      Finset.card_union_le _ _
    _ ≤ (G.classEdges l b.val).card + (G.classEdges l b.val).card :=
      add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = _ := by simp only [classSize]; omega

theorem classBoundary_card_real_le (b : PClass n l) :
    ((classBoundary l G b).card : ℝ) ≤ 2 * (classSize l G b : ℝ) := by
  exact_mod_cast classBoundary_card_le (G := G) b

theorem classBoundary_subset_vertices (hG : G.IsValid) (b : PClass n l) :
    classBoundary l G b ⊆ Finset.range (numV n) := by
  intro u hu
  obtain ⟨e, he, hi⟩ := (mem_classBoundary_iff b u).mp hu
  have hv := LoopProof.edge_endpoints hG (Finset.mem_filter.mp he).1
  apply Finset.mem_range.mpr
  rcases hi with rfl | rfl
  · exact hv.1
  · exact hv.2.1

/-- Any class touching a weld vertex contains at least one edge of each
color in every applicable sibling quadruple (or the stronger weld bound). -/
theorem classSize_ge_of_meets_weld (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (b : PClass n l) {u : ℕ} (hu : u ∈ classBoundary l G b)
    (hw : u ∈ Vweld n) :
    2 ^ (n - 2) ≤ classSize l G b := by
  obtain ⟨e, he, hi⟩ := (mem_classBoundary_iff b u).mp hu
  exact FirstFreeStep.class_card_ge_of_incident_weld hG hn hl he hi hw

theorem classSize_ge_quarter_of_meets_weld (hG : G.IsValid) (hn : 2 ≤ n)
    (hl : 1 ≤ l) (b : PClass n l) {u : ℕ}
    (hu : u ∈ classBoundary l G b) (hw : u ∈ Vweld n) :
    (2 : ℝ) ^ n / 4 ≤ (classSize l G b : ℝ) := by
  have hs : (2 : ℝ) ^ (n - 2) ≤ (classSize l G b : ℝ) := by
    exact_mod_cast classSize_ge_of_meets_weld hG hn hl b hu hw
  have hp : (2 : ℝ) ^ n = 4 * (2 : ℝ) ^ (n - 2) := by
    exact_mod_cast (NearWeldClasses.pow_two_levels hn).1
  rw [hp]
  linarith

theorem classBoundary_disjoint_weld_of_lt (hG : G.IsValid) (hn : 2 ≤ n)
    (hl : 1 ≤ l) (b : PClass n l)
    (hsmall : classSize l G b < 2 ^ (n - 2)) :
    Disjoint (classBoundary l G b) (Vweld n) := by
  apply Finset.disjoint_left.mpr
  intro u hu hw
  exact (not_le_of_gt hsmall) (classSize_ge_of_meets_weld hG hn hl b hu hw)

/-- The sharp cutoff supplied by the existing near-weld counting lemma is
strictly below N/4; the analytic argument may freely use N/8 or N/16. -/
theorem classBoundary_disjoint_weld_of_lt_quarter (hG : G.IsValid) (hn : 2 ≤ n)
    (hl : 1 ≤ l) (b : PClass n l)
    (hsmall : (classSize l G b : ℝ) < (2 : ℝ) ^ n / 4) :
    Disjoint (classBoundary l G b) (Vweld n) := by
  apply Finset.disjoint_left.mpr
  intro u hu hw
  exact (not_le_of_gt hsmall) (classSize_ge_quarter_of_meets_weld hG hn hl b hu hw)

theorem classBoundary_disjoint_weld_of_le_eighth (hG : G.IsValid) (hn : 2 ≤ n)
    (hl : 1 ≤ l) (b : PClass n l)
    (hsmall : (classSize l G b : ℝ) ≤ (2 : ℝ) ^ n / 8) :
    Disjoint (classBoundary l G b) (Vweld n) := by
  apply classBoundary_disjoint_weld_of_lt_quarter hG hn hl b
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  linarith

/-- The enlarged boundary used for the localized correction of class b. -/
def enlargedBoundary (l : ℕ) (G : WeldedInstance n) (b : PClass n l) : Finset ℕ :=
  Vbd n l ∪ classBoundary l G b

theorem boundary_subset_enlarged (b : PClass n l) :
    Vbd n l ⊆ enlargedBoundary l G b := Finset.subset_union_left

theorem classBoundary_subset_enlarged (b : PClass n l) :
    classBoundary l G b ⊆ enlargedBoundary l G b := Finset.subset_union_right

theorem enlargedBoundary_card_le (b : PClass n l) :
    (enlargedBoundary l G b).card ≤ (Vbd n l).card + 2 * classSize l G b :=
  (Finset.card_union_le _ _).trans (add_le_add le_rfl (classBoundary_card_le b))

theorem boundary_disjoint_weld (hl : 2 ≤ l) (hln : l ≤ n - 4) :
    Disjoint (Vbd n l) (Vweld n) := by
  apply Finset.disjoint_left.mpr
  intro u hu hw
  have hu' := (Finset.mem_filter.mp hu).2
  have hw' := (Finset.mem_filter.mp hw).2
  rcases hu' with hu' | hu' | hu' | hu' <;> rcases hw' with hw' | hw' <;> omega

theorem enlargedBoundary_disjoint_weld (hG : G.IsValid) (hn : 2 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (b : PClass n l)
    (hsmall : (classSize l G b : ℝ) ≤ (2 : ℝ) ^ n / 8) :
    Disjoint (enlargedBoundary l G b) (Vweld n) := by
  exact Finset.disjoint_union_left.mpr
    ⟨boundary_disjoint_weld hl hln,
      classBoundary_disjoint_weld_of_le_eighth hG hn (by omega) b hsmall⟩

end WeldedPath.Supplement.LocalizedClassBoundary

namespace WeldedPath.Supplement.LocalizedComparison

theorem enlarged_boundary_budget {n l q t s : ℕ} (R : Finset ℕ)
    (hl : 1 ≤ l) (hln : l ≤ n) (ht : t ≤ 6 * q) (hR : R.card ≤ 2 * s)
    (hsmall : 64 * ((t : ℝ) + 6) * (s : ℝ) ≤ (2 : ℝ) ^ n)
    (hbudget : 576 * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2) :
    8 * ((t : ℝ) + 6) * (((Vbd n l ∪ R).card : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ 1 / 2 := by
  have hbd : ((Vbd n l).card : ℝ) ≤ 6 * (2 : ℝ) ^ (n-l) := by
    exact_mod_cast ReferenceSizes.boundary_card_le hl hln
  have hR' : (R.card : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hR
  have hcard : (((Vbd n l ∪ R).card : ℕ) : ℝ) ≤ ((Vbd n l).card : ℝ) + R.card := by
    exact_mod_cast Finset.card_union_le (Vbd n l) R
  have ht' : (t : ℝ) + 6 ≤ 6 * ((q : ℝ) + 1) := by
    exact_mod_cast (show t + 6 ≤ 6 * (q + 1) by omega)
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n-l) * (2 : ℝ) ^ l := by
    rw [← pow_add, Nat.sub_add_cancel hln]
  have htail : 0 ≤ ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n := by positivity
  have hold : 8 * ((t : ℝ) + 6) * ((Vbd n l).card : ℝ) / (2 : ℝ) ^ n ≤ 1 / 4 := by
    calc
      _ ≤ 8 * (6 * ((q : ℝ) + 1)) * (6 * (2 : ℝ) ^ (n-l)) / (2 : ℝ) ^ n := by gcongr
      _ = 288 * (((q : ℝ) + 1) / (2 : ℝ) ^ l) := by rw [hpow]; field_simp <;> ring
      _ ≤ 1 / 4 := by linarith
  have hnew : 8 * ((t : ℝ) + 6) * (R.card : ℝ) / (2 : ℝ) ^ n ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hR' (show 0 ≤ 8 * ((t : ℝ) + 6) by positivity)
    linarith
  calc
    _ ≤ 8 * ((t : ℝ) + 6) * (((Vbd n l).card : ℝ) + R.card) / (2 : ℝ) ^ n := by gcongr
    _ ≤ 1 / 2 := by rw [mul_add, add_div]; linarith


end WeldedPath.Supplement.LocalizedComparison

open WeldedPath WeldedPath.Supplement

theorem solution (n l q t : ℕ) (hn : Even n) (hn16 : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (ht : t ≤ 6 * q)
    (G : WeldedInstance n) (hG : G.IsValid)
    (hrecords : 256 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n-l))
    (hboundary : 576 * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
      ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (b : PClass n l) :
    let s := classSize l G b
    let R := (G.classEdges l b.val).image Edge.tail ∪ (G.classEdges l b.val).image (Edge.head n)
    let B := Vbd n l ∪ R
    4 * (t + 16) ≤ s ∧
      (64 * ((t : ℝ) + 6) * (s : ℝ) ≤ (2 : ℝ)^n →
        Disjoint B (Vweld n) ∧ 8 * ((t : ℝ) + 6) * (B.card : ℝ) / (2 : ℝ)^n ≤ 1 / 2) := by
  dsimp only
  constructor
  · have hsize := observation_3_3 n l hn hn16 hl hln G hG b.val b.property
    change (2 : ℝ) ^ (n-l) / 4 ≤ (classSize l G b : ℝ) at hsize
    have ht' : (t : ℝ) ≤ 6 * (q : ℝ) := by exact_mod_cast ht
    exact_mod_cast (show 4 * ((t : ℝ) + 16) ≤ (classSize l G b : ℝ) by linarith)
  · intro hsmall
    have hprod : 0 ≤ (t : ℝ) * (classSize l G b : ℝ) := by positivity
    have heighth : (classSize l G b : ℝ) ≤ (2 : ℝ)^n / 8 := by nlinarith
    exact ⟨LocalizedClassBoundary.enlargedBoundary_disjoint_weld hG (by omega) hl hln b heighth,
      LocalizedComparison.enlarged_boundary_budget (LocalizedClassBoundary.classBoundary l G b)
        (by omega) (by omega) ht (LocalizedClassBoundary.classBoundary_card_le b) hsmall hboundary⟩
