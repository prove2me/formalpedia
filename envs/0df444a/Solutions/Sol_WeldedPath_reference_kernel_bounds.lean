-- Prove2me | solution 1 for WeldedPath.reference_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T20:59:18.779219+00:00
-- url     : https://prove2.me/submissions/c371148b-1b9e-4a1a-8ad9-593b5076ae5b

import Definitions.Def_WeldedPath_bEdge
import Definitions.Def_WeldedPath_Supplement_projGood
import Definitions.Def_WeldedPath_Supplement_pCross
import Definitions.Def_WeldedPath_Nb
import Definitions.Def_WeldedPath_Supplement_pWt

set_option autoImplicit false

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

-- Solutions.WeldedPathWeldClasses
section

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

end

-- Solutions.WeldedPathNearWeldClasses
section

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

end

-- Solutions.WeldedPathCrossingExclusion
section

namespace WeldedPath.Supplement.CrossingExclusion

open WeldedInstance InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma reachable_preserves {X : Type*} {J : SimpleGraph X} (P : X → Prop)
    (h : ∀ u v, J.Adj u v → (P u ↔ P v)) {u v : X} (hr : J.Reachable u v) :
    P u ↔ P v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons huv _ ih => exact (h _ _ huv).trans ih

lemma edge_adj (H : AbsForest n) (hH : H.IsValid) {p : Fin H.k × Fin H.k}
    (hp : p ∈ H.E) : H.graph.Adj p.1 p.2 := by
  exact ⟨ne_of_lt (hH.1 p hp), Or.inl hp⟩

lemma comp_root_exists (H : AbsForest n) (u : Fin H.k) :
    ∃ s, H.IsCompRoot s ∧ H.graph.Reachable s u := by
  classical
  have hu : u ∈ H.comp u := by simp [AbsForest.comp]
  let s := (H.comp u).min' ⟨u, hu⟩
  have hs : H.graph.Reachable u s := (Finset.mem_filter.mp
    (Finset.min'_mem (H.comp u) ⟨u, hu⟩)).2
  refine ⟨s, ?_, hs.symm⟩
  intro v hv
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.trans hv⟩)

lemma edge_kappa_ne_zero (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0)
    {p : Fin H.k × Fin H.k} (hp : p ∈ H.E) :
    kappa l G (H.color p) (ϕ p.1).1 (ϕ p.2).1 ≠ 0 := by
  classical
  obtain ⟨s, hs, hsu⟩ := comp_root_exists H p.1
  have hsu' : p.1 ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu⟩
  have hsv : p.2 ∈ H.comp s := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hsu.trans (edge_adj H hH hp).reachable⟩
  have hcard : (H.comp s).card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have h1 : p.1 = a := by simpa only [ha, Finset.mem_singleton] using hsu'
    have h2 : p.2 = a := by simpa only [ha, Finset.mem_singleton] using hsv
    have heq : p.1 = p.2 := h1.trans h2.symm
    exact (ne_of_lt (hH.1 p hp)) heq
  have hc : H.muComp l G s ϕ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hmu) s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  unfold AbsForest.muComp at hc
  dsimp only at hc
  rw [if_neg hcard] at hc
  split at hc
  · have hw := (mul_ne_zero_iff.mp hc).2
    exact (Finset.prod_ne_zero_iff.mp hw) p (Finset.mem_filter.mpr ⟨hp, hsu'⟩)
  · exact False.elim (hc rfl)

lemma permData_orientation {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) :
    (t = true → u = e.1.tail) ∧ (t = false → u = e.1.head n) := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        rename_i e' he' hh
        have hi := (Classical.choose_spec hh.2).2.2
        constructor
        · intro ht
          simpa using ht
        · intro ht
          have hnt : u ≠ e'.tail := by simpa using ht
          exact hi.resolve_left hnt
      · simp at h

lemma class_pair_half (hG : G.IsValid) {e e' : Edge}
    (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hc : G.bEdge l e = G.bEdge l e') (hne : G.bEdge l e ≠ none) :
    IsVertex n e.tail ∧ IsVertex n (e'.head n) ∧
      ((col n e.tail ≤ n ↔ col n (e'.head n) ≤ n) ∨
        (e.tail ∈ Vweld n ∧ e'.head n ∈ Vweld n)) := by
  have hends := LoopProof.edge_endpoints hG he
  have hends' := LoopProof.edge_endpoints hG he'
  have hcols := LoopProof.same_class_cols hG he he' hc hne
  refine ⟨hends.1, hends'.2.1, ?_⟩
  cases e with
  | tree v =>
    left
    rw [← hcols.2, LoopProof.tree_head_col he]
    simp only [Edge.tail]
    split <;> omega
  | weld u w =>
    right
    have hw := hG.1.1 (u, w) (LoopProof.weld_mem_iff.mp he)
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.1, Or.inl hw.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hends'.2.1,
        Or.inr (by simpa only [Edge.head] using hcols.2.symm.trans hw.2.2.2)⟩

lemma kappa_half (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) :
    (col n u ≤ n ↔ col n v ≤ n) ∨ (u ∈ Vweld n ∧ v ∈ Vweld n) := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := permData_orientation hpd
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (fun g => g.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    have he := Finset.mem_filter.mp e.2
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.1 ht]
      exact (class_pair_half hG he.1 he'.1 (he.2.trans he'.2.symm)
        (by simp [he.2])).2.2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.2 ht]
      rcases (class_pair_half hG he'.1 he.1 (he'.2.trans he.2.symm)
        (by simp [he'.2])).2.2 with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm

lemma tree_reachable_half (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0) {u v : Fin H.k}
    (hr : (H.treeGraph ϕ).Reachable u v) :
    col n (ϕ u).1 ≤ n ↔ col n (ϕ v).1 ≤ n := by
  apply reachable_preserves (fun u => col n (ϕ u).1 ≤ n) _ hr
  intro a b hab
  rcases hab.2 with ⟨he, hn⟩ | ⟨he, hn⟩
  · exact (kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn
  · exact ((kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn).symm

lemma recorded_adj_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) {I : Db l G} (hI : H.IsDbOf l G ϕ I)
    {a c : ℕ} (hac : (recordedGraph l G I.2).Adj a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
  have one : ∀ a c, (∃ (b : PClass n l) (j j' : Fin (classSize l G b)),
      I.2 b j = some j' ∧ a = ((edgeIdx l G b).symm j).1.tail ∧
      c = ((edgeIdx l G b).symm j').1.head n) →
      ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
    rintro a c ⟨b, j, j', hj, rfl, rfl⟩
    obtain ⟨p, hp, h⟩ := (hI.2 b j j').mp hj
    dsimp only at h
    rcases h with h | h
    · exact ⟨p.1, p.2, h.2.2.1, h.2.2.2, edge_adj H hH hp⟩
    · exact ⟨p.2, p.1, h.2.2.1, h.2.2.2, (edge_adj H hH hp).symm⟩
  rcases hac.2 with h | h
  · exact one _ _ h
  · obtain ⟨u, v, hu, hv, huv⟩ := one _ _ h
    exact ⟨v, u, hv, hu, huv.symm⟩

lemma recorded_reachable_lift_from (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ}
    (hac : (recordedGraph l G I.2).Reachable a c)
    (u : Fin H.k) (hu : (ϕ u).1 = a) :
    ∃ v, (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  induction w generalizing u with
  | nil => exact ⟨u, hu, .refl _⟩
  | cons hab w ih =>
    obtain ⟨x, y, hx, hy, hxy⟩ := recorded_adj_lift H hH ϕ hI hab
    have hux : u = x := hinj (Fin.ext (hu.trans hx.symm))
    obtain ⟨v, hv, hyv⟩ := ih y hy
    subst x
    exact ⟨v, hv, hxy.reachable.trans hyv⟩

lemma recorded_reachable_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ} (hne : a ≠ c)
    (hac : (recordedGraph l G I.2).Reachable a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons hab w =>
    obtain ⟨u, y, hu, hy, huy⟩ := recorded_adj_lift H hH ϕ hI hab
    obtain ⟨v, hv, hyv⟩ := recorded_reachable_lift_from H hH ϕ hinj hI w.reachable y hy
    exact ⟨u, v, hu, hv, huy.reachable.trans hyv⟩

lemma good_database_not_crossing (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (D : Description n) (hD : D.IsValid) (ϕ : Fin D.H.k → Label n)
    (hg : D.IsGood l G (Vbd n l) ϕ) (I : Db l G) (hI : D.H.IsDbOf l G ϕ I) :
    ¬ HasCrossing l G I.2 := by
  classical
  rintro ⟨a, c, ha, hacol, hc, hccol, hr⟩
  have hne : a ≠ c := by intro h; subst c; omega
  obtain ⟨u, v, hu, hv, huv⟩ := recorded_reachable_lift D.H hD.1 ϕ hg.2.2.2 hI hne hr
  obtain ⟨s, hs, _⟩ := hD.2 u
  have hsu := hs.2.symm
  have hsv := hsu.trans huv
  have hub : (ϕ u).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hu] using Finset.mem_range.mpr ha,
      Or.inl (by simpa only [hu] using hacol)⟩
  have hvb : (ϕ v).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hv] using Finset.mem_range.mpr hc,
      Or.inr (Or.inr (Or.inr (by simpa only [hv] using hccol)))⟩
  have hut : u ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 u hsu h hub
  have hvt : v ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 v hsv h hvb
  have htree : (D.H.treeGraph ϕ).Reachable u v :=
    (Finset.mem_filter.mp hut).2.symm.trans (Finset.mem_filter.mp hvt).2
  have hhalf := tree_reachable_half hG D.H hD.1 ϕ (ne_of_gt hg.1) htree
  rw [hu, hv, hacol, hccol] at hhalf
  omega

end WeldedPath.Supplement.CrossingExclusion

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

-- Solutions.WeldedPathKappaKernel
section

namespace WeldedPath.Supplement.KappaKernel

open WeldedInstance
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma kappa_nonneg (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u v : ℕ) :
    0 ≤ kappa l G α u v := by
  classical
  unfold kappa
  split <;> positivity

lemma sum_uniform_finset_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (S : Finset ℕ) (m : ℕ) (hSm : S.card ≤ m) :
    (∑ x, if f x ∈ S then 1 / (m : ℝ) else 0) ≤ 1 := by
  classical
  have hc : (Finset.univ.filter fun x => f x ∈ S).card ≤ m := by
    apply le_trans _ hSm
    exact Finset.card_le_card_of_injOn f
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun _ _ _ _ h => hf h)
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hcr : ((Finset.univ.filter fun x => f x ∈ S).card : ℝ) ≤ m := by
      exact_mod_cast hc
    calc
      _ = ((Finset.univ.filter fun x => f x ∈ S).card : ℝ) * (1 / (m : ℝ)) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (m : ℝ) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hcr (by positivity)
      _ = 1 := by field_simp

lemma kappa_row_sum_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u : ℕ) :
    (∑ x, kappa l G α u (f x)) ≤ 1 := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd]
  | some d =>
    obtain ⟨b, e, t⟩ := d
    cases t
    · simpa only [kappa, hpd, Bool.false_eq_true, false_and, true_and, false_or] using
        sum_uniform_finset_le_one f hf ((G.classEdges l b.1).image Edge.tail)
          (classSize l G b) (Finset.card_image_le)
    · simpa only [kappa, hpd, Bool.true_eq_false, false_and, true_and, or_false] using
        sum_uniform_finset_le_one f hf ((G.classEdges l b.1).image (Edge.head n))
          (classSize l G b) (Finset.card_image_le)

def classColor : EdgeClass → Fin 3
  | .tr _ α => α
  | .wld α => α

lemma bEdge_color {e : Edge} {b : EdgeClass} (he : G.bEdge l e = some b) :
    G.color e = classColor b := by
  cases e with
  | tree v =>
    simp only [WeldedInstance.bEdge] at he
    split at he
    · cases he
      rfl
    · simp at he
  | weld u v =>
    simp only [WeldedInstance.bEdge] at he
    cases he
    rfl

lemma class_color {b : PClass n l} {e e' : Edge}
    (he : e ∈ G.classEdges l b.1) (he' : e' ∈ G.classEdges l b.1) :
    G.color e = G.color e' :=
  (bEdge_color (Finset.mem_filter.mp he).2).trans
    (bEdge_color (Finset.mem_filter.mp he').2).symm

lemma eAlpha_spec {u : ℕ} {α : Fin 3} {e : Edge} (h : G.eAlpha u α = some e) :
    e ∈ G.edges ∧ G.color e = α ∧ e.Incident n u := by
  classical
  unfold WeldedInstance.eAlpha at h
  split at h
  · rename_i hh
    have hs := Classical.choose_spec hh
    cases h
    exact hs
  · simp at h

lemma permData_eAlpha {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) : G.eAlpha u α = some e.1 := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        assumption
      · simp at h

lemma classData_ext {b b' : PClass n l} {e : ↥(G.classEdges l b.1)}
    {e' : ↥(G.classEdges l b'.1)} {t t' : Bool} (hb : b = b')
    (he : e.1 = e'.1) (ht : t = t') :
    (⟨b, e, t⟩ : (c : PClass n l) × ↥(G.classEdges l c.1) × Bool) = ⟨b', e', t'⟩ := by
  subst b'
  have he' : e = e' := Subtype.ext he
  subst e'
  subst t'
  rfl

lemma permData_of_class_edge (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (u : ℕ) (hu : e.1.Incident n u) :
    permData l G u (G.color e.1) = some ⟨b, e, decide (u = e.1.tail)⟩ := by
  classical
  have he := Finset.mem_filter.mp e.2
  have hv : IsVertex n u := by
    rcases hu with rfl | rfl
    · exact (LoopProof.edge_endpoints hG he.1).1
    · exact (LoopProof.edge_endpoints hG he.1).2.1
  have ha := LoopProof.eAlpha_of_edge G hG.2 e.1 he.1 u hu
  unfold permData
  simp only [if_neg (not_not.mpr hv), ha]
  split
  · rename_i hh
    have hb : Classical.choose hh.2 = b.1 :=
      Option.some.inj ((Classical.choose_spec hh.2).2.1.symm.trans he.2)
    have hb' : (⟨Classical.choose hh.2, (Classical.choose_spec hh.2).1⟩ : PClass n l) = b :=
      Subtype.ext hb
    apply congrArg some
    exact classData_ext hb' rfl rfl
  · rename_i hh
    exact False.elim (hh ⟨he.1, b.1, b.2, he.2, hu⟩)

lemma class_tail_head_ne (hG : G.IsValid) {b : PClass n l}
    (e e' : ↥(G.classEdges l b.1)) : e.1.tail ≠ e'.1.head n := by
  have he := Finset.mem_filter.mp e.2
  have he' := Finset.mem_filter.mp e'.2
  have hc := LoopProof.same_class_cols hG he.1 he'.1
    (he.2.trans he'.2.symm) (by simp [he.2])
  have hd := (LoopProof.edge_endpoints hG he.1).2.2
  intro h
  have hv := congrArg (col n) h
  omega

lemma kappa_tail (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (v : ℕ) :
    kappa l G (G.color e.1) e.1.tail v =
      if v ∈ (G.classEdges l b.1).image (Edge.head n) then
        1 / (classSize l G b : ℝ) else 0 := by
  classical
  have hp := permData_of_class_edge hG e e.1.tail (Or.inl rfl)
  simp only [kappa, hp, decide_true, true_and, Bool.true_eq_false, false_and, or_false]

lemma kappa_head (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (v : ℕ) :
    kappa l G (G.color e.1) (e.1.head n) v =
      if v ∈ (G.classEdges l b.1).image Edge.tail then
        1 / (classSize l G b : ℝ) else 0 := by
  classical
  have hp := permData_of_class_edge hG e (e.1.head n) (Or.inr rfl)
  have hn : e.1.head n ≠ e.1.tail := (class_tail_head_ne hG e e).symm
  simp only [kappa, hp, decide_eq_false hn, Bool.false_eq_true, false_and,
    true_and, false_or]

lemma kappa_between_class (hG : G.IsValid) {b : PClass n l}
    (e e' : ↥(G.classEdges l b.1)) :
    kappa l G (G.color e.1) e.1.tail (e'.1.head n) =
      kappa l G (G.color e.1) (e'.1.head n) e.1.tail := by
  classical
  have hf : kappa l G (G.color e.1) e.1.tail (e'.1.head n) =
      1 / (classSize l G b : ℝ) := by
    rw [kappa_tail hG e]
    rw [if_pos (Finset.mem_image.mpr ⟨e'.1, e'.2, rfl⟩)]
  have hr : kappa l G (G.color e.1) (e'.1.head n) e.1.tail =
      1 / (classSize l G b : ℝ) := by
    rw [class_color e.2 e'.2, kappa_head hG e']
    rw [if_pos (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)]
  exact hf.trans hr.symm

lemma kappa_symm_of_ne_zero (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) : kappa l G α u v = kappa l G α v u := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := CrossingExclusion.permData_orientation hpd
    have hec := (eAlpha_spec (permData_eAlpha hpd)).2.1
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (Edge.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    rw [← hec]
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      rw [hor.1 ht]
      exact kappa_between_class hG e ⟨e', he'⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      rw [hor.2 ht, class_color e.2 he']
      exact (kappa_between_class hG ⟨e', he'⟩ e).symm

lemma kappa_symm (hG : G.IsValid) (α : Fin 3) (u v : ℕ) :
    kappa l G α u v = kappa l G α v u := by
  by_cases h : kappa l G α u v = 0
  · have hr : kappa l G α v u = 0 := by
      by_contra hn
      exact hn ((kappa_symm_of_ne_zero hG hn).trans h)
    exact h.trans hr.symm
  · exact kappa_symm_of_ne_zero hG h

lemma kappa_zero_of_not_vertex_left (l : ℕ) (G : WeldedInstance n)
    (α : Fin 3) {u : ℕ} (hu : ¬ IsVertex n u) (v : ℕ) :
    kappa l G α u v = 0 := by
  classical
  simp [kappa, permData, hu]

lemma kappa_zero_of_not_vertex_right (hG : G.IsValid) (α : Fin 3)
    (u : ℕ) {v : ℕ} (hv : ¬ IsVertex n v) : kappa l G α u v = 0 := by
  rw [kappa_symm hG α u v]
  exact kappa_zero_of_not_vertex_left l G α hv u

lemma kappa_le_inv_classSize {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (hpd : permData l G u α = some ⟨b, e, t⟩) (v : ℕ) :
    kappa l G α u v ≤ 1 / (classSize l G b : ℝ) := by
  classical
  simp only [kappa, hpd]
  split
  · exact le_rfl
  · positivity

lemma kappa_column_sum_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (hG : G.IsValid) (α : Fin 3) (v : ℕ) :
    (∑ x, kappa l G α (f x) v) ≤ 1 := by
  simp_rw [kappa_symm hG α _ v]
  exact kappa_row_sum_le_one f hf l G α v

lemma kappa_label_row_sum_le_one (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u : ℕ) :
    (∑ v : Label n, kappa l G α u v.1) ≤ 1 :=
  kappa_row_sum_le_one Fin.val Fin.val_injective l G α u

lemma kappa_label_column_sum_le_one (hG : G.IsValid) (α : Fin 3) (v : ℕ) :
    (∑ u : Label n, kappa l G α u.1 v) ≤ 1 :=
  kappa_column_sum_le_one Fin.val Fin.val_injective hG α v

lemma kappa_finset_row_sum_le_one (S : Finset ℕ) (l : ℕ) (G : WeldedInstance n)
    (α : Fin 3) (u : ℕ) : (∑ v ∈ S, kappa l G α u v) ≤ 1 := by
  simpa only [Finset.sum_coe_sort] using
    kappa_row_sum_le_one (fun v : S => v.1) Subtype.val_injective l G α u

lemma kappa_finset_column_sum_le_one (S : Finset ℕ) (hG : G.IsValid)
    (α : Fin 3) (v : ℕ) : (∑ u ∈ S, kappa l G α u v) ≤ 1 := by
  calc
    _ = ∑ u ∈ S, kappa l G α v u := by
      apply Finset.sum_congr rfl
      intro u _
      exact kappa_symm hG α u v
    _ ≤ 1 := kappa_finset_row_sum_le_one S l G α v

lemma finite_kernel_point_bound {X Y : Type*} [Fintype X]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y ≤ 1) (p : X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : Y) :
    (∑ x, p x * K x y) ≤ M := by
  calc
    _ ≤ ∑ x, M * K x y := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (hp x) (hK x y)
    _ = M * ∑ x, K x y := (Finset.mul_sum _ _ _).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (hcol y) hM
    _ = M := mul_one M

lemma finite_kernel_abs_bound {X Y : Type*} [Fintype X]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y ≤ 1) (p : X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) (y : Y) :
    |∑ x, p x * K x y| ≤ M := by
  calc
    _ ≤ ∑ x, |p x * K x y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |p x| * K x y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hK x y)]
    _ ≤ M := finite_kernel_point_bound K hK hcol (fun x => |p x|) M hM hp y

lemma finite_kernel_mass_le {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (hrow : ∀ x, ∑ y, K x y ≤ 1)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ y, ∑ x, p x * K x y) ≤ ∑ x, p x := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow x) (hp x)

lemma kappa_step_nonneg (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) (y : ℕ) :
    0 ≤ ∑ x : Label n, p x * kappa l G α x.1 y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (kappa_nonneg l G α x.1 y)

lemma kappa_step_mass_le (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ y : Label n, ∑ x : Label n, p x * kappa l G α x.1 y.1) ≤ ∑ x, p x :=
  finite_kernel_mass_le (fun x y : Label n => kappa l G α x.1 y.1)
    (fun x => kappa_label_row_sum_le_one l G α x.1) p hp

lemma kappa_propagates_point_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : ℕ) :
    (∑ x : Label n, p x * kappa l G α x.1 y) ≤ M :=
  finite_kernel_point_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y

lemma kappa_propagates_abs_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) (y : ℕ) :
    |∑ x : Label n, p x * kappa l G α x.1 y| ≤ M :=
  finite_kernel_abs_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y

end WeldedPath.Supplement.KappaKernel

end

-- Solutions.WeldedPathFirstFreeStep
section

namespace WeldedPath.Supplement.FirstFreeStep

open Classical WeldedInstance LoopProof NearWeldClasses KappaKernel

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

theorem kappa_from_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    {u : ℕ} (hu : u ∈ Vweld n) (α : Fin 3) (v : ℕ) :
    kappa l G α u v ≤ 4 / (2 : ℝ) ^ n := by
  cases hpd : permData l G u α with
  | none => simp only [kappa, hpd]; positivity
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have he := KappaKernel.eAlpha_spec (permData_eAlpha hpd)
    have hc := class_card_ge_of_incident_weld hG hn hl e.2 he.2.2 hu
    exact (kappa_le_inv_classSize hpd v).trans (reciprocal_le_four_dyadic hn hc)

theorem kappa_to_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (u : ℕ) (α : Fin 3) {v : ℕ} (hv : v ∈ Vweld n) :
    kappa l G α u v ≤ 4 / (2 : ℝ) ^ n := by
  rw [kappa_symm hG α u v]
  exact kappa_from_weld_le hG hn hl hv α u

end WeldedPath.Supplement.FirstFreeStep

end

-- Solutions.WeldedPathMidPermData
section

namespace WeldedPath.Supplement.MidPermData

open Classical WeldedInstance LoopProof NearWeldClasses KappaKernel

variable {n l : ℕ} {G : WeldedInstance n}

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem color_of_three_incident (hG : G.IsProperColoring) (u : ℕ)
    (e f g : Edge) (he : e ∈ G.edges) (hf : f ∈ G.edges) (hg : g ∈ G.edges)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hie : e.Incident n u) (hif : f.Incident n u) (hig : g.Incident n u)
    (α : Fin 3) : ∃ a ∈ G.edges, G.color a = α ∧ a.Incident n u := by
  have hcf := hG e he f hf hef ⟨u, hie, hif⟩
  have hcg := hG e he g hg heg ⟨u, hie, hig⟩
  have hcfg := hG f hf g hg hfg ⟨u, hif, hig⟩
  rcases three_colors_cover _ _ _ α hcf hcg hcfg with h | h | h
  · exact ⟨e, he, h.symm, hie⟩
  · exact ⟨f, hf, h.symm, hif⟩
  · exact ⟨g, hg, h.symm, hig⟩

theorem tree_mem_of_nonroot {u : ℕ} (hu : IsVertex n u)
    (hlo : 0 < col n u) (hhi : col n u < 2 * n + 1) : Edge.tree u ∈ G.edges := by
  apply tree_mem_iff.mpr
  refine ⟨hu, ?_⟩
  unfold parent
  split_ifs <;> simp_all <;> omega

theorem color_at_leaf (hG : G.IsValid) {u : ℕ} (hu : IsLeaf n u)
    (ht : Edge.tree u ∈ G.edges) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n u := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp (hG.1.2.1 u hu)
  have hp : p ∈ G.weld ∧ (p.1 = u ∨ p.2 = u) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hq : q ∈ G.weld ∧ (q.1 = u ∨ q.2 = u) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hep : Edge.weld p.1 p.2 ∈ G.edges := weld_mem_iff.mpr hp.1
  have heq : Edge.weld q.1 q.2 ∈ G.edges := weld_mem_iff.mpr hq.1
  have hip : (Edge.weld p.1 p.2).Incident n u := by
    rcases hp.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hiq : (Edge.weld q.1 q.2).Incident n u := by
    rcases hq.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hpq' : Edge.weld p.1 p.2 ≠ Edge.weld q.1 q.2 := by
    intro h
    exact hpq (Prod.ext (congrArg Edge.tail h) (congrArg (Edge.head n) h))
  exact color_of_three_incident hG.2 u (.tree u) (.weld p.1 p.2) (.weld q.1 q.2)
    ht hep heq (by simp) (by simp) hpq' (Or.inl rfl) hip hiq α

theorem color_at_heap_internal (hG : G.IsProperColoring) (right : Bool)
    {d w : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    (hlo : 2 ^ d - 1 ≤ w) (hhi : w < 2 ^ (d + 1) - 1) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n (heapNode n right w) := by
  have hw := heap_node_spec right hd (Nat.le_of_lt hdn) hlo hhi
  have hdp := Nat.two_pow_pos d
  have hds : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
  have hds' : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]
  have ha := heap_node_spec (n := n) (d := d + 1) (u := 2 * w + 1)
    right (by omega) (by omega) (by omega) (by omega)
  have hb := heap_node_spec (n := n) (d := d + 1) (u := 2 * w + 2)
    right (by omega) (by omega) (by omega) (by omega)
  have hpa : parent n (heapNode n right (2 * w + 1)) = some (heapNode n right w) := by
    simpa only [show (2 * w + 1 - 1) / 2 = w by omega] using ha.2.2
  have hpb : parent n (heapNode n right (2 * w + 2)) = some (heapNode n right w) := by
    simpa only [show (2 * w + 2 - 1) / 2 = w by omega] using hb.2.2
  have hwE : Edge.tree (heapNode n right w) ∈ G.edges :=
    tree_mem_iff.mpr ⟨hw.1, by simp [hw.2.2]⟩
  have haE : Edge.tree (heapNode n right (2 * w + 1)) ∈ G.edges :=
    tree_mem_iff.mpr ⟨ha.1, by simp [hpa]⟩
  have hbE : Edge.tree (heapNode n right (2 * w + 2)) ∈ G.edges :=
    tree_mem_iff.mpr ⟨hb.1, by simp [hpb]⟩
  apply color_of_three_incident hG (heapNode n right w)
    (.tree (heapNode n right w)) (.tree (heapNode n right (2 * w + 1)))
    (.tree (heapNode n right (2 * w + 2))) hwE haE hbE
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · exact Or.inl rfl
  · exact Or.inr (by simp [Edge.head, hpa])
  · exact Or.inr (by simp [Edge.head, hpb])

theorem color_at_nonroot (hG : G.IsValid) {u : ℕ} (hu : IsVertex n u)
    (hlo : 0 < col n u) (hhi : col n u < 2 * n + 1) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n u := by
  by_cases hleaf : col n u = n ∨ col n u = n + 1
  · exact color_at_leaf hG ⟨hu, hleaf⟩ (tree_mem_of_nonroot hu hlo hhi) α
  · by_cases hleft : u < 2 ^ (n + 1) - 1
    · let d := Nat.log 2 (u + 1)
      have hc : col n u = d := by simp [col, hleft, d]
      have hd : 1 ≤ d := by omega
      have hdn : d < n := by
        have hh := log_left_le n u hleft
        dsimp [d]
        omega
      have hlow := Nat.pow_log_le_self 2 (by omega : u + 1 ≠ 0)
      have hupp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (u + 1)
      have hh := color_at_heap_internal (w := u) hG.2 false hd hdn
        (by dsimp [d]; omega) (by dsimp [d]; omega) α
      simpa only [heapNode, Bool.false_eq_true, if_false, zero_add] using hh
    · let R := 2 ^ (n + 1) - 1
      let w := u - R
      let d := Nat.log 2 (w + 1)
      have hR : R ≤ u := by dsimp [R]; omega
      have heq : heapNode n true w = u := by dsimp [heapNode, w]; omega
      have hc : col n u = 2 * n + 1 - d := by
        simp only [col, if_neg hleft]
        rfl
      have hdnle : d ≤ n := log_right_le n u hu hR
      have hd : 1 ≤ d := by omega
      have hdn : d < n := by omega
      have hlow := Nat.pow_log_le_self 2 (by omega : w + 1 ≠ 0)
      have hupp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (w + 1)
      have hh := color_at_heap_internal (w := w) hG.2 true hd hdn
        (by dsimp [d]; omega) (by dsimp [d]; omega) α
      simpa only [heq] using hh

theorem incident_mid_class (hG : G.IsValid) {u : ℕ} {e : Edge}
    (he : e ∈ G.edges) (hi : e.Incident n u) (hu : u ∈ Vmid n l) :
    ∃ b : PClass n l, e ∈ G.classEdges l b.1 := by
  have hum := (Finset.mem_filter.mp hu).2
  cases e with
  | tree w =>
    have hadj := (edge_endpoints hG he).2.2
    have hm : n - l ≤ col n w ∧ col n w ≤ n + l := by
      rcases hi with hi | hi
      · change u = w at hi
        rw [hi] at hum
        omega
      · change u = (Edge.tree w).head n at hi
        rw [hi] at hum
        change col n w + 1 = col n ((Edge.tree w).head n) ∨
          col n ((Edge.tree w).head n) + 1 = col n w at hadj
        omega
    let b : PClass n l := ⟨.tr (col n w) (G.color (.tree w)), by simp [BEdge, hm]; omega⟩
    refine ⟨b, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    simp [b, WeldedInstance.bEdge, hm]
  | weld a c =>
    let b : PClass n l := ⟨.wld (G.color (.weld a c)), by simp [BEdge]⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨he, rfl⟩⟩

theorem permData_ne_none_of_mem_Vmid (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vmid n l) (α : Fin 3) :
    permData l G u α ≠ none := by
  have huv := Finset.mem_filter.mp hu
  have hv : IsVertex n u := Finset.mem_range.mp huv.1
  obtain ⟨e, he, hc, hi⟩ := color_at_nonroot hG hv (by omega) (by omega) α
  obtain ⟨b, hb⟩ := incident_mid_class hG he hi hu
  have hp := permData_of_class_edge hG (⟨e, hb⟩ : G.classEdges l b.1) u hi
  rw [hc] at hp
  rw [hp]
  simp

end WeldedPath.Supplement.MidPermData

end

open Classical WeldedPath WeldedPath.Supplement
open scoped BigOperators

theorem solution :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
      (∀ (α : Fin 3) (u v : ℕ), kappa l G α u v = kappa l G α v u) ∧
      (∀ (α : Fin 3) (u : ℕ), (∑ v : Label n, kappa l G α u v.1) ≤ 1) ∧
      (∀ (α : Fin 3) (v : ℕ), (∑ u : Label n, kappa l G α u.1 v) ≤ 1) ∧
      (∀ u ∈ Vweld n, ∀ (α : Fin 3) (v : ℕ),
        kappa l G α u v ≤ 4 / (2 : ℝ) ^ n) ∧
      (∀ u ∈ Vmid n l, ∀ α : Fin 3, permData l G u α ≠ none) := by
  intro n l hn hl hln G hG
  refine ⟨KappaKernel.kappa_symm hG, ?_, ?_, ?_, ?_⟩
  · exact fun α u => KappaKernel.kappa_label_row_sum_le_one l G α u
  · exact fun α v => KappaKernel.kappa_label_column_sum_le_one hG α v
  · intro u hu α v
    exact FirstFreeStep.kappa_from_weld_le hG (by omega) (by omega) hu α v
  · intro u hu α
    exact MidPermData.permData_ne_none_of_mem_Vmid hG hn hl hln hu α
