-- Prove2me | solution 1 for WeldedPath.reference_conditional_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T21:36:07.785203+00:00
-- url     : https://prove2.me/submissions/d36860cb-6181-44e4-9340-ef92cd567937

import Definitions.Def_WeldedPath_Supplement_projGood
import Definitions.Def_WeldedPath_Supplement_pCross
import Definitions.Def_WeldedPath_bEdge
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
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

-- Solutions.WeldedPathConnectedReference
section

namespace WeldedPath.Supplement.ConnectedReference

open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma reachable_of_connected (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (u v : Fin H.k) : H.graph.Reachable u v :=
  (hs u).symm.trans (hs v)

lemma comp_eq_univ (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (u : Fin H.k) : H.comp u = Finset.univ := by
  classical
  ext v
  simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact reachable_of_connected H s hs u v

lemma muComp_eq (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (u v : Fin H.k) (ϕ : Fin H.k → Label n) :
    H.muComp l G u ϕ = H.muComp l G v ϕ := by
  classical
  by_cases hk : H.k = 1
  · have huv : u = v := by
      apply Fin.ext
      have hu := u.isLt
      have hv := v.isLt
      omega
    rw [huv]
  · simp only [AbsForest.muComp, comp_eq_univ H s hs, Finset.card_univ,
      Fintype.card_fin, if_neg hk]

open Classical in
lemma comp_roots_eq_singleton (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (r : Fin H.k) (hr : H.IsCompRoot r) :
    (Finset.univ.filter fun u => H.IsCompRoot u) = {r} := by
  classical
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hu
    exact le_antisymm (hu r (reachable_of_connected H s hs u r))
      (hr u (reachable_of_connected H s hs r u))
  · intro h
    simpa only [h] using hr

lemma muRef_eq_muComp (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (ϕ : Fin H.k → Label n) :
    H.muRef l G ϕ = H.muComp l G s ϕ := by
  classical
  obtain ⟨r, hr, _⟩ := CrossingExclusion.comp_root_exists H s
  unfold AbsForest.muRef
  rw [comp_roots_eq_singleton H s hs r hr, Finset.prod_singleton]
  exact muComp_eq H s hs r s ϕ

lemma muComp_ne_zero_of_muRef_ne_zero (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (ϕ : Fin H.k → Label n)
    (hϕ : H.muRef l G ϕ ≠ 0) : H.muComp l G s ϕ ≠ 0 := by
  rwa [muRef_eq_muComp H s hs] at hϕ

lemma muComp_pos_of_muRef_pos (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (ϕ : Fin H.k → Label n)
    (hϕ : 0 < H.muRef l G ϕ) : 0 < H.muComp l G s ϕ := by
  rwa [muRef_eq_muComp H s hs] at hϕ

end WeldedPath.Supplement.ConnectedReference

end

-- Solutions.WeldedPathFixedData
section

namespace WeldedPath.Supplement.FixedData

variable {n : ℕ}

lemma reachable_closed {V : Type*} {J : SimpleGraph V} (P : V → Prop)
    (hstep : ∀ u v, P u → J.Adj u v → P v) {u v : V} (h : J.Reachable u v) :
    P u → P v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons huv w ih => exact fun hu => ih (hstep _ _ hu huv)

/-- Agreement of incident edges on a component suffices to preserve that
entire component; arbitrary edges wholly outside it are irrelevant. -/
lemma reachable_iff_of_adj_at_component {V : Type*} (J K : SimpleGraph V) (s : V)
    (hadj : ∀ u v, J.Reachable s u → (J.Adj u v ↔ K.Adj u v)) (v : V) :
    J.Reachable s v ↔ K.Reachable s v := by
  constructor
  · intro hv
    have h := reachable_closed (fun u => J.Reachable s u ∧ K.Reachable s u)
      (fun u v hu huv => ⟨hu.1.trans huv.reachable,
        hu.2.trans ((hadj u v hu.1).mp huv).reachable⟩) hv
        ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
    exact h.2
  · intro hv
    exact reachable_closed (fun u => J.Reachable s u)
      (fun u v hu huv => hu.trans ((hadj u v hu).mpr huv).reachable) hv
      (SimpleGraph.Reachable.refl _)

lemma ctree_subset_sfix (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k) :
    H.Ctree φ s ⊆ H.Sfix φ s := by
  classical
  exact Finset.subset_union_left

/-- Every stored edge touching the selected tree component has both its
endpoints in the recorded fixed set. -/
lemma edge_endpoints_mem_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (s : Fin H.k) (p : Fin H.k × Fin H.k) (hp : p ∈ H.E)
    (htouch : p.1 ∈ H.Ctree φ s ∨ p.2 ∈ H.Ctree φ s) :
    p.1 ∈ H.Sfix φ s ∧ p.2 ∈ H.Sfix φ s := by
  classical
  by_cases hw : H.IsWeldUnder φ p
  · rcases htouch with h₁ | h₂
    · refine ⟨ctree_subset_sfix H φ s h₁, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hw, Or.inl ⟨h₁, rfl⟩⟩)
    · refine ⟨?_, ctree_subset_sfix H φ s h₂⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hw, Or.inr ⟨h₂, rfl⟩⟩)
  · have hr : (H.treeGraph φ).Reachable p.1 p.2 :=
      SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 p hp), Or.inl ⟨hp, hw⟩⟩
    rcases htouch with h₁ | h₂
    · have h₂ : p.2 ∈ H.Ctree φ s := by
        simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ ⊢
        exact h₁.trans hr
      exact ⟨ctree_subset_sfix H φ s h₁, ctree_subset_sfix H φ s h₂⟩
    · have h₁ : p.1 ∈ H.Ctree φ s := by
        simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and] at h₂ ⊢
        exact h₂.trans hr.symm
      exact ⟨ctree_subset_sfix H φ s h₁, ctree_subset_sfix H φ s h₂⟩

lemma weld_iff_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E)
    (htouch : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s) :
    H.IsWeldUnder φ p ↔ H.IsWeldUnder φ₀ p := by
  obtain ⟨h₁, h₂⟩ := edge_endpoints_mem_sfix H hH φ₀ s p hp htouch
  simp only [AbsForest.IsWeldUnder, hφ p.1 h₁, hφ p.2 h₂]

lemma treeGraph_adj_iff_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u)
    (u v : Fin H.k) (hu : u ∈ H.Ctree φ₀ s) :
    (H.treeGraph φ).Adj u v ↔ (H.treeGraph φ₀).Adj u v := by
  have h₁ (hp : (u, v) ∈ H.E) :=
    weld_iff_of_agree_sfix H hH φ φ₀ s hφ (u, v) hp (Or.inl hu)
  have h₂ (hp : (v, u) ∈ H.E) :=
    weld_iff_of_agree_sfix H hH φ φ₀ s hφ (v, u) hp (Or.inr hu)
  constructor
  · rintro ⟨hne, ⟨hp, hn⟩ | ⟨hp, hn⟩⟩
    · exact ⟨hne, Or.inl ⟨hp, (not_congr (h₁ hp)).mp hn⟩⟩
    · exact ⟨hne, Or.inr ⟨hp, (not_congr (h₂ hp)).mp hn⟩⟩
  · rintro ⟨hne, ⟨hp, hn⟩ | ⟨hp, hn⟩⟩
    · exact ⟨hne, Or.inl ⟨hp, (not_congr (h₁ hp)).mpr hn⟩⟩
    · exact ⟨hne, Or.inr ⟨hp, (not_congr (h₂ hp)).mpr hn⟩⟩

lemma ctree_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Ctree φ s = H.Ctree φ₀ s := by
  classical
  apply Finset.ext
  intro v
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  apply (reachable_iff_of_adj_at_component (H.treeGraph φ₀) (H.treeGraph φ) s ?_ v).symm
  intro u v hu
  apply (treeGraph_adj_iff_of_agree_sfix H hH φ φ₀ s hφ u v ?_).symm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩

lemma sfix_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Sfix φ s = H.Sfix φ₀ s := by
  classical
  have hC := ctree_eq_of_agree_sfix H hH φ φ₀ s hφ
  unfold AbsForest.Sfix
  rw [hC]
  congr 1
  apply Finset.filter_congr
  intro u _
  constructor
  · rintro ⟨p, hp, hw, h⟩
    have ht : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s := by
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact ⟨p, hp, (weld_iff_of_agree_sfix H hH φ φ₀ s hφ p hp ht).mp hw, h⟩
  · rintro ⟨p, hp, hw, h⟩
    have ht : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s := by
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact ⟨p, hp, (weld_iff_of_agree_sfix H hH φ φ₀ s hφ p hp ht).mpr hw, h⟩

lemma wfix_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Wfix φ s = H.Wfix φ₀ s := by
  classical
  have hC := ctree_eq_of_agree_sfix H hH φ φ₀ s hφ
  have hS := sfix_eq_of_agree_sfix H hH φ φ₀ s hφ
  unfold AbsForest.Wfix
  rw [hC, hS]
  congr 2
  · apply Finset.image_congr
    intro u hu
    exact congrArg (fun x : Label n => (u, x.val)) (hφ u (ctree_subset_sfix H φ₀ s hu))
  · apply Finset.image_congr
    intro u hu
    exact congrArg (fun x : Label n => (u, x.val)) (hφ u (Finset.mem_sdiff.mp hu).1)

lemma eq_on_of_image_graph_eq {V X : Type*} [DecidableEq V] [DecidableEq X]
    (A B : Finset V) (f g : V → X)
    (h : A.image (fun v => (v, f v)) = B.image (fun v => (v, g v))) :
    ∀ u ∈ B, f u = g u := by
  intro u hu
  have hm : (u, g u) ∈ A.image (fun v => (v, f v)) := by
    rw [h]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
  have hvu : v = u := congrArg Prod.fst hv
  subst v
  exact congrArg Prod.snd hv

/-- Fixed data is exactly a coordinate-fixing event on its recorded fixed
set. This is valid for all assignments, including those with zero reference
weight; no probabilistic conditioning assumption is hidden in the statement. -/
theorem wfix_eq_iff_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) :
    H.Wfix φ s = H.Wfix φ₀ s ↔ ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u := by
  classical
  constructor
  · intro hw u hu
    have hC := congrArg (fun t => t.2.1) hw
    have hS := congrArg (fun t => t.2.2) hw
    apply Fin.ext
    by_cases huc : u ∈ H.Ctree φ₀ s
    · exact eq_on_of_image_graph_eq _ _ (fun v => (φ v).val) (fun v => (φ₀ v).val) hC u huc
    · exact eq_on_of_image_graph_eq _ _ (fun v => (φ v).val) (fun v => (φ₀ v).val) hS u
        (Finset.mem_sdiff.mpr ⟨hu, huc⟩)
  · exact wfix_eq_of_agree_sfix H hH φ φ₀ s

/-- The fixed-data and boundary conditions of a description are local
restrictions on individual vertex labels. Injectivity is deliberately not
included: it is the separate collision condition in the good space. -/
def coordinateCondition (D : Description n) (B : Finset ℕ) (u : Fin D.H.k)
    (x : Label n) : Prop :=
  (∀ s ∈ D.sel, u ∈ D.H.Sfix D.ϕ₀ s → x = D.ϕ₀ u) ∧
  (∀ s ∈ D.sel, D.H.graph.Reachable s u →
    u ∉ D.H.Ctree D.ϕ₀ s → x.val ∉ B)

theorem description_conditions_iff (D : Description n) (hD : D.IsValid)
    (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    ((∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s) ∧
      (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u →
        u ∉ D.H.Ctree φ s → (φ u).val ∉ B)) ↔
      ∀ u, coordinateCondition D B u (φ u) := by
  constructor
  · rintro ⟨hw, hb⟩ u
    constructor
    · intro s hs hu
      exact (wfix_eq_iff_agree_sfix D.H hD.1 φ D.ϕ₀ s).mp (hw s hs) u hu
    · intro s hs hr hu
      have hC : D.H.Ctree φ s = D.H.Ctree D.ϕ₀ s := congrArg Prod.fst (hw s hs)
      exact hb s hs u hr (hC.symm ▸ hu)
  · intro h
    have hw : ∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s := by
      intro s hs
      apply (wfix_eq_iff_agree_sfix D.H hD.1 φ D.ϕ₀ s).mpr
      intro u hu
      exact (h u).1 s hs hu
    refine ⟨hw, ?_⟩
    intro s hs u hr hu
    have hC : D.H.Ctree φ s = D.H.Ctree D.ϕ₀ s := congrArg Prod.fst (hw s hs)
    exact (h u).2 s hs hr (hC ▸ hu)

theorem isGood_iff_coordinateCondition (l : ℕ) (G : WeldedInstance n)
    (D : Description n) (hD : D.IsValid) (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    D.IsGood l G B φ ↔
      0 < D.H.muRef l G φ ∧ (∀ u, coordinateCondition D B u (φ u)) ∧
        Function.Injective φ := by
  constructor
  · rintro ⟨hμ, hw, hb, hi⟩
    exact ⟨hμ, (description_conditions_iff D hD B φ).mp ⟨hw, hb⟩, hi⟩
  · rintro ⟨hμ, hc, hi⟩
    obtain ⟨hw, hb⟩ := (description_conditions_iff D hD B φ).mpr hc
    exact ⟨hμ, hw, hb, hi⟩

end WeldedPath.Supplement.FixedData

end

-- Solutions.WeldedPathFixedAvoidance
section

namespace WeldedPath.Supplement.FixedAvoidance

variable {n : ℕ}

lemma sfix_not_ctree_weld (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k)
    {v : Fin H.k} (hv : v ∈ H.Sfix φ s) (hc : v ∉ H.Ctree φ s) :
    (φ v).1 ∈ Vweld n := by
  classical
  obtain ⟨e, _, hw, hor⟩ := (Finset.mem_filter.mp
    ((Finset.mem_union.mp hv).resolve_left hc)).2
  rcases hor with ⟨_, hev⟩ | ⟨_, hev⟩
  · exact hev ▸ hw.2
  · exact hev ▸ hw.1

lemma avoid_ctree_iff_avoid_sfix_of_agree (H : AbsForest n)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (hB : Disjoint B (Vweld n)) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    (∀ u, u ∉ H.Ctree φ₀ s → (φ u).1 ∉ B) ↔
      (∀ u, u ∉ H.Sfix φ₀ s → (φ u).1 ∉ B) := by
  classical
  constructor
  · intro h u hu
    exact h u (fun hc => hu (FixedData.ctree_subset_sfix H φ₀ s hc))
  · intro h u hu
    by_cases hs : u ∈ H.Sfix φ₀ s
    · have hw := sfix_not_ctree_weld H φ₀ s hs hu
      rw [hφ u hs]
      exact fun hb => Finset.disjoint_left.mp hB hb hw
    · exact h u hs

lemma avoid_tree_iff_avoid_free_of_wfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (hB : Disjoint B (Vweld n)) (hw : H.Wfix φ s = H.Wfix φ₀ s) :
    (∀ u, u ∉ H.Ctree φ s → (φ u).1 ∉ B) ↔
      (∀ u, u ∉ H.Sfix φ₀ s → (φ u).1 ∉ B) := by
  have hφ := (FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mp hw
  have hc : H.Ctree φ s = H.Ctree φ₀ s := congrArg Prod.fst hw
  rw [hc]
  exact avoid_ctree_iff_avoid_sfix_of_agree H φ φ₀ s B hB hφ

lemma connected_fixed_avoidance_iff (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (B : Finset ℕ) (hB : Disjoint B (Vweld n)) :
    (H.Wfix φ s = H.Wfix φ₀ s ∧
      ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).1 ∉ B) ↔
    ((∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) ∧
      ∀ u, u ∉ H.Sfix φ₀ s → (φ u).1 ∉ B) := by
  constructor
  · rintro ⟨hw, hb⟩
    refine ⟨(FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mp hw, ?_⟩
    exact (avoid_tree_iff_avoid_free_of_wfix H hH φ φ₀ s B hB hw).mp
      (fun u => hb u (hs u))
  · rintro ⟨hφ, hb⟩
    have hw := (FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mpr hφ
    refine ⟨hw, ?_⟩
    intro u _ hu
    exact (avoid_tree_iff_avoid_free_of_wfix H hH φ φ₀ s B hB hw).mpr hb u hu

end WeldedPath.Supplement.FixedAvoidance

end

-- Solutions.FiniteRankEnumeration
section

namespace FiniteRankEnumeration

/-- A finite set can be enumerated in increasing rank, with arbitrary but
consistent tie breaking. Strict rank inequalities become strict index inequalities. -/
theorem exists_rank_order {S : Type*} [Fintype S] (rank : S → ℕ) :
    ∃ order : Fin (Fintype.card S) ≃ S,
      ∀ i j, rank (order i) < rank (order j) → i < j := by
  classical
  let key : S → Lex (ℕ × Fin (Fintype.card S)) :=
    fun x => toLex (rank x, Fintype.equivFin S x)
  have hinj : Function.Injective key := by
    intro x y h
    apply (Fintype.equivFin S).injective
    exact congrArg (fun z : Lex (ℕ × Fin (Fintype.card S)) => (ofLex z).2) h
  letI : LinearOrder S := LinearOrder.lift' key hinj
  let order := Fintype.orderIsoFinOfCardEq S rfl
  refine ⟨order.toEquiv, ?_⟩
  intro i j hij
  have hlt : order i < order j := by
    change key (order i) < key (order j)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hij)
  exact order.lt_iff_lt.mp hlt

theorem exists_rank_order_of_card_eq {S : Type*} [Fintype S] (rank : S → ℕ)
    (k : ℕ) (hk : Fintype.card S = k) :
    ∃ order : Fin k ≃ S, ∀ i j, rank (order i) < rank (order j) → i < j := by
  subst k
  exact exists_rank_order rank

end FiniteRankEnumeration

end

-- Solutions.WeldedPathForestOrder
section

namespace WeldedPath.Supplement.ForestOrder

open Classical

section RootedForest

variable {V : Type*} (J : SimpleGraph V) (s : V)

theorem lower_neighbor_exists {v : V} (hr : J.Reachable s v) (hne : v ≠ s) :
    ∃ w, J.Adj v w ∧ J.dist s w + 1 = J.dist s v := by
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  cases p with
  | nil => exact (hne rfl).elim
  | @cons v w s h q =>
    refine ⟨w, h, ?_⟩
    have hq := J.dist_le q
    have ht := h.reachable.dist_triangle_left s
    have he : J.dist v w = 1 := J.dist_eq_one_iff_adj.mpr h
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [J.dist_comm (u := v) (v := s)] at hp
    rw [J.dist_comm (u := w) (v := s)] at hq
    rw [J.dist_comm (u := v) (v := s), J.dist_comm (u := w) (v := s)] at ht
    rw [he] at ht
    omega

noncomputable def rootParent (v : V) : V :=
  if h : J.Reachable s v ∧ v ≠ s then Classical.choose (lower_neighbor_exists J s h.1 h.2)
  else s

theorem rootParent_spec {v : V} (hr : J.Reachable s v) (hne : v ≠ s) :
    J.Adj v (rootParent J s v) ∧ J.dist s (rootParent J s v) + 1 = J.dist s v := by
  rw [rootParent, dif_pos ⟨hr, hne⟩]
  exact Classical.choose_spec (lower_neighbor_exists J s hr hne)

theorem lower_neighbor_unique (hJ : J.IsAcyclic) {v w w' : V}
    (hv : J.Reachable s v) (hw : J.Adj v w) (hw' : J.Adj v w')
    (hd : J.dist s w + 1 = J.dist s v) (hd' : J.dist s w' + 1 = J.dist s v) : w = w' := by
  obtain ⟨p, hp, hplen⟩ := (hv.trans hw.reachable).symm.exists_path_of_dist
  obtain ⟨q, hq, hqlen⟩ := (hv.trans hw'.reachable).symm.exists_path_of_dist
  have hpl : (p.cons hw).length = J.dist v s := by
    simp only [SimpleGraph.Walk.length_cons, hplen]
    rw [J.dist_comm (u := w) (v := s), J.dist_comm (u := v) (v := s)]
    omega
  have hql : (q.cons hw').length = J.dist v s := by
    simp only [SimpleGraph.Walk.length_cons, hqlen]
    rw [J.dist_comm (u := w') (v := s), J.dist_comm (u := v) (v := s)]
    omega
  have heq : p.cons hw = q.cons hw' := Subtype.mk.inj <|
    (hJ.subsingleton_path v s).elim
      ⟨p.cons hw, (p.cons hw).isPath_of_length_eq_dist hpl⟩
      ⟨q.cons hw', (q.cons hw').isPath_of_length_eq_dist hql⟩
  simpa only [SimpleGraph.Walk.snd_cons] using congrArg SimpleGraph.Walk.snd heq

theorem eq_rootParent_of_lower (hJ : J.IsAcyclic) {v w : V}
    (hv : J.Reachable s v) (hw : J.Adj v w)
    (hd : J.dist s w + 1 = J.dist s v) : w = rootParent J s v := by
  have hne : v ≠ s := by intro h; subst v; simp at hd
  have hs := rootParent_spec J s hv hne
  exact lower_neighbor_unique J s hJ hv hw hs.1 hd hs.2

theorem adjacent_parent_cases (hJ : J.IsAcyclic) {u v : V}
    (hu : J.Reachable s u) (h : J.Adj u v) :
    rootParent J s u = v ∨ rootParent J s v = u := by
  rcases hJ.dist_eq_dist_add_one_of_adj_of_reachable s h hu with hd | hd
  · exact Or.inl (eq_rootParent_of_lower J s hJ hu h hd.symm).symm
  · exact Or.inr (eq_rootParent_of_lower J s hJ (hu.trans h.reachable) h.symm hd.symm).symm

theorem lower_neighbor_mem_of_path (hJ : J.IsAcyclic) (S : Set V)
    {v w : V} (hv : J.Reachable s v) (hw : J.Adj v w)
    (hd : J.dist s w + 1 = J.dist s v)
    (p : J.Walk v s) (hp : p.IsPath) (hS : ∀ x ∈ p.support, x ∈ S) : w ∈ S := by
  obtain ⟨q, hq, hqlen⟩ := (hv.trans hw.reachable).symm.exists_path_of_dist
  have hlen : (q.cons hw).length = J.dist v s := by
    simp only [SimpleGraph.Walk.length_cons, hqlen]
    rw [J.dist_comm (u := w) (v := s), J.dist_comm (u := v) (v := s)]
    omega
  have heq : q.cons hw = p := Subtype.mk.inj <|
    (hJ.subsingleton_path v s).elim
      ⟨q.cons hw, (q.cons hw).isPath_of_length_eq_dist hlen⟩ ⟨p, hp⟩
  apply hS
  rw [← heq]
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
  exact Or.inr q.start_mem_support

end RootedForest

variable {n : ℕ} (H : AbsForest n) (hH : H.IsValid)
  (φ : Fin H.k → Label n) (s : Fin H.k)

lemma treeGraph_le : H.treeGraph φ ≤ H.graph := by
  rintro u v ⟨hne, h | h⟩
  · exact ⟨hne, Or.inl h.1⟩
  · exact ⟨hne, Or.inr h.1⟩

lemma root_mem_ctree : s ∈ H.Ctree φ s := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩

lemma root_mem_sfix : s ∈ H.Sfix φ s :=
  FixedData.ctree_subset_sfix H φ s (root_mem_ctree H φ s)

lemma ctree_path {v : Fin H.k} (hv : v ∈ H.Ctree φ s) :
    ∃ p : H.graph.Walk v s, p.IsPath ∧ ∀ x ∈ p.support, x ∈ H.Ctree φ s := by
  classical
  have hr : (H.treeGraph φ).Reachable s v := (Finset.mem_filter.mp hv).2
  obtain ⟨p, hp⟩ := hr.symm.exists_isPath
  refine ⟨p.mapLe (treeGraph_le H φ), hp.mapLe _, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans (p.takeUntil x hx).reachable⟩

include hH in
lemma sfix_path {v : Fin H.k} (hv : v ∈ H.Sfix φ s) :
    ∃ p : H.graph.Walk v s, p.IsPath ∧ ∀ x ∈ p.support, x ∈ H.Sfix φ s := by
  classical
  by_cases hc : v ∈ H.Ctree φ s
  · obtain ⟨p, hp, hps⟩ := ctree_path H φ s hc
    exact ⟨p, hp, fun x hx => FixedData.ctree_subset_sfix H φ s (hps x hx)⟩
  · obtain ⟨e, he, hw, hor⟩ := (Finset.mem_filter.mp
      ((Finset.mem_union.mp hv).resolve_left hc)).2
    have hegraph : H.graph.Adj e.1 e.2 :=
      ⟨ne_of_lt (hH.1 e he), Or.inl he⟩
    have hex : ∃ w, w ∈ H.Ctree φ s ∧ H.graph.Adj v w := by
      rcases hor with ⟨hec, hev⟩ | ⟨hec, hev⟩
      · exact ⟨e.1, hec, hev ▸ hegraph.symm⟩
      · exact ⟨e.2, hec, hev ▸ hegraph⟩
    obtain ⟨w, hwc, hvw⟩ := hex
    obtain ⟨p, hp, hps⟩ := ctree_path H φ s hwc
    refine ⟨p.cons hvw, (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
      ⟨hp, fun hvp => hc (hps v hvp)⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact FixedData.ctree_subset_sfix H φ s (hps x hx)

include hH in
lemma sfix_subset_comp : H.Sfix φ s ⊆ H.comp s := by
  intro v hv
  obtain ⟨p, _, _⟩ := sfix_path H hH φ s hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.reachable.symm⟩

include hH in
lemma parent_mem_sfix {v : Fin H.k} (hv : v ∈ H.Sfix φ s) :
    rootParent H.graph s v ∈ H.Sfix φ s := by
  classical
  by_cases hvs : v = s
  · subst v
    simp only [rootParent, ne_eq, not_true_eq_false, and_false, dite_false]
    exact root_mem_sfix H φ s
  · obtain ⟨p, hp, hps⟩ := sfix_path H hH φ s hv
    have hr := p.reachable.symm
    have hs := rootParent_spec H.graph s hr hvs
    exact lower_neighbor_mem_of_path H.graph s hH.2.1
      (↑(H.Sfix φ s)) hr hs.1 hs.2 p hp hps

lemma sfix_not_ctree_weld {v : Fin H.k}
    (hv : v ∈ H.Sfix φ s) (hc : v ∉ H.Ctree φ s) : (φ v).val ∈ Vweld n := by
  classical
  obtain ⟨e, he, hw, hor⟩ := (Finset.mem_filter.mp
    ((Finset.mem_union.mp hv).resolve_left hc)).2
  rcases hor with ⟨_, hev⟩ | ⟨_, hev⟩
  · exact hev ▸ hw.2
  · exact hev ▸ hw.1

include hH in
lemma free_parent_fixed_weld {v : Fin H.k}
    (hv : v ∈ H.comp s) (hf : v ∉ H.Sfix φ s)
    (hp : rootParent H.graph s v ∈ H.Sfix φ s) :
    (φ (rootParent H.graph s v)).val ∈ Vweld n := by
  have hvs : v ≠ s := by
    intro heq
    apply hf
    rw [heq]
    exact root_mem_sfix H φ s
  have hs := rootParent_spec H.graph s (Finset.mem_filter.mp hv).2 hvs
  apply sfix_not_ctree_weld H φ s hp
  intro hc
  rcases hs.1.2 with he | he
  · exact hf (FixedData.edge_endpoints_mem_sfix H hH φ s _ he (Or.inr hc)).1
  · exact hf (FixedData.edge_endpoints_mem_sfix H hH φ s _ he (Or.inl hc)).2

noncomputable def freeVertices : Finset (Fin H.k) := H.comp s \ H.Sfix φ s

noncomputable def freeEdges : Finset (Fin H.k × Fin H.k) :=
  H.E.filter (fun e => e.1 ∈ H.comp s ∧
    ¬(e.1 ∈ H.Sfix φ s ∧ e.2 ∈ H.Sfix φ s))

lemma free_vertex_spec (v : freeVertices H φ s) :
    (v : Fin H.k) ∈ H.comp s ∧ (v : Fin H.k) ∉ H.Sfix φ s :=
  Finset.mem_sdiff.mp v.property

lemma free_parent_spec (v : freeVertices H φ s) :
    H.graph.Adj v (rootParent H.graph s v) ∧
    H.graph.dist s (rootParent H.graph s v) + 1 = H.graph.dist s v := by
  apply rootParent_spec H.graph s (Finset.mem_filter.mp (free_vertex_spec H φ s v).1).2
  intro heq
  apply (free_vertex_spec H φ s v).2
  rw [heq]
  exact root_mem_sfix H φ s

lemma free_parent_mem_comp (v : freeVertices H φ s) :
    rootParent H.graph s v ∈ H.comp s := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp (free_vertex_spec H φ s v).1).2.trans
    (free_parent_spec H φ s v).1.reachable⟩

noncomputable def parentEdge (v : freeVertices H φ s) : Fin H.k × Fin H.k :=
  if (v : Fin H.k) < rootParent H.graph s v then (v, rootParent H.graph s v)
  else (rootParent H.graph s v, v)

include hH in
lemma parentEdge_mem (v : freeVertices H φ s) : parentEdge H φ s v ∈ freeEdges H φ s := by
  classical
  have hs := free_parent_spec H φ s v
  have hf := free_vertex_spec H φ s v
  have hp := free_parent_mem_comp H φ s v
  unfold parentEdge
  split_ifs with hlt
  · apply Finset.mem_filter.mpr
    refine ⟨?_, hf.1, fun hx => hf.2 hx.1⟩
    rcases hs.1.2 with he | he
    · exact he
    · have hh := hH.1 _ he; exact (not_lt_of_ge (le_of_lt hlt) hh).elim
  · apply Finset.mem_filter.mpr
    refine ⟨?_, hp, fun hx => hf.2 hx.2⟩
    rcases hs.1.2 with he | he
    · exact (hlt (hH.1 _ he)).elim
    · exact he

lemma parentEdge_injective : Function.Injective (parentEdge H φ s) := by
  classical
  intro v w heq
  have hv := (free_parent_spec H φ s v).2
  have hw := (free_parent_spec H φ s w).2
  unfold parentEdge at heq
  split_ifs at heq with h₁ h₂ h₂
  · exact Subtype.ext (congrArg Prod.fst heq)
  · have ha := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    dsimp only at ha hb
    have hra := congrArg (H.graph.dist s) ha
    have hrb := congrArg (H.graph.dist s) hb
    omega
  · have ha := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    dsimp only at ha hb
    have hra := congrArg (H.graph.dist s) ha
    have hrb := congrArg (H.graph.dist s) hb
    omega
  · exact Subtype.ext (congrArg Prod.snd heq)

noncomputable def edgeOfFree (v : freeVertices H φ s) : freeEdges H φ s :=
  ⟨parentEdge H φ s v, parentEdge_mem H hH φ s v⟩

lemma edgeOfFree_bijective : Function.Bijective (edgeOfFree H hH φ s) := by
  classical
  constructor
  · intro v w heq
    exact parentEdge_injective H φ s (congrArg Subtype.val heq)
  · intro e
    have he := Finset.mem_filter.mp e.property
    have hadj : H.graph.Adj e.val.1 e.val.2 := ⟨ne_of_lt (hH.1 _ he.1), Or.inl he.1⟩
    have hr := (Finset.mem_filter.mp he.2.1).2
    have hr' : e.val.2 ∈ H.comp s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans hadj.reachable⟩
    rcases adjacent_parent_cases H.graph s hH.2.1 hr hadj with hp | hp
    · have hf : e.val.1 ∉ H.Sfix φ s := by
        intro hc
        exact he.2.2 ⟨hc, hp ▸ parent_mem_sfix H hH φ s hc⟩
      let v : freeVertices H φ s := ⟨e.val.1, Finset.mem_sdiff.mpr ⟨he.2.1, hf⟩⟩
      refine ⟨v, Subtype.ext ?_⟩
      change parentEdge H φ s v = e.val
      have hlt := hH.1 _ he.1
      simp only [parentEdge, v, hp, if_pos hlt]
    · have hf : e.val.2 ∉ H.Sfix φ s := by
        intro hc
        exact he.2.2 ⟨hp ▸ parent_mem_sfix H hH φ s hc, hc⟩
      let v : freeVertices H φ s := ⟨e.val.2, Finset.mem_sdiff.mpr ⟨hr', hf⟩⟩
      refine ⟨v, Subtype.ext ?_⟩
      change parentEdge H φ s v = e.val
      have hlt := not_lt_of_gt (hH.1 _ he.1)
      simp only [parentEdge, v, hp, if_neg hlt]

noncomputable def freeEdgeEquiv : freeVertices H φ s ≃ freeEdges H φ s :=
  Equiv.ofBijective (edgeOfFree H hH φ s) (edgeOfFree_bijective H hH φ s)

def parentVertex {m : ℕ} (order : Fin m → Fin H.k) (fixed : Fin m → Fin H.k)
    (parent : (i : Fin m) → Option (Fin i.val)) (i : Fin m) : Fin H.k :=
  match parent i with
  | none => fixed i
  | some j => order ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- Every free vertex is enumerated after its parent. Every edge outside the
fixed set occurs once, and every fixed parent has a weld label. -/
structure ParentOrder where
  order : Fin (Fintype.card ↥(freeVertices H φ s)) ≃ freeVertices H φ s
  parent : (i : Fin (Fintype.card ↥(freeVertices H φ s))) → Option (Fin i.val)
  fixed : Fin (Fintype.card ↥(freeVertices H φ s)) → Fin H.k
  edge : Fin (Fintype.card ↥(freeVertices H φ s)) ≃ freeEdges H φ s
  edge_endpoints : ∀ i,
    (edge i).val = ((order i).val, parentVertex H (fun j => (order j).val) fixed parent i) ∨
    (edge i).val = (parentVertex H (fun j => (order j).val) fixed parent i, (order i).val)
  fixed_mem : ∀ i, parent i = none → fixed i ∈ H.Sfix φ s
  fixed_weld : ∀ i, parent i = none → (φ (fixed i)).val ∈ Vweld n

include hH in
theorem exists_parent_order : Nonempty (ParentOrder H φ s) := by
  classical
  have ho : ∃ order : Fin (Fintype.card ↥(freeVertices H φ s)) ≃ freeVertices H φ s,
      ∀ i j, H.graph.dist s (order i).val < H.graph.dist s (order j).val → i < j := by
    exact FiniteRankEnumeration.exists_rank_order
      (fun v : freeVertices H φ s => H.graph.dist s v.val)
  obtain ⟨order, hord⟩ := ho
  let fixed : Fin (Fintype.card ↥(freeVertices H φ s)) → Fin H.k :=
    fun i => rootParent H.graph s (order i)
  have hparent (i : Fin (Fintype.card ↥(freeVertices H φ s))) :
      ∃ p : Option (Fin i.val),
        (match p with
         | none => fixed i
         | some j => (order ⟨j.val, lt_trans j.isLt i.isLt⟩).val) = fixed i ∧
        (p = none → fixed i ∈ H.Sfix φ s ∧ (φ (fixed i)).val ∈ Vweld n) := by
    by_cases hp : fixed i ∈ H.Sfix φ s
    · refine ⟨none, rfl, fun _ => ⟨hp, ?_⟩⟩
      exact free_parent_fixed_weld H hH φ s (free_vertex_spec H φ s (order i)).1
        (free_vertex_spec H φ s (order i)).2 hp
    · let v : freeVertices H φ s :=
        ⟨fixed i, Finset.mem_sdiff.mpr ⟨free_parent_mem_comp H φ s (order i), hp⟩⟩
      have hlt : order.symm v < i := by
        apply hord
        simp only [Equiv.apply_symm_apply]
        have hd := (free_parent_spec H φ s (order i)).2
        change H.graph.dist s (fixed i) + 1 = H.graph.dist s (order i).val at hd
        change H.graph.dist s (fixed i) < H.graph.dist s (order i).val
        omega
      refine ⟨some ⟨(order.symm v).val, hlt⟩, ?_, by simp⟩
      change (order (order.symm v)).val = fixed i
      simp only [Equiv.apply_symm_apply]
      rfl
  let parent (i : Fin (Fintype.card ↥(freeVertices H φ s))) : Option (Fin i.val) :=
    Classical.choose (hparent i)
  have hspec i := Classical.choose_spec (hparent i)
  refine ⟨{
    order := order
    parent := parent
    fixed := fixed
    edge := order.trans (freeEdgeEquiv H hH φ s)
    edge_endpoints := ?_
    fixed_mem := fun i hi => ((hspec i).2 hi).1
    fixed_weld := fun i hi => ((hspec i).2 hi).2 }⟩
  intro i
  have hp : parentVertex H (fun j => (order j).val) fixed parent i = fixed i := by
    unfold parentVertex parent
    convert (hspec i).1 using 1
    cases Classical.choose (hparent i) <;> rfl
  change parentEdge H φ s (order i) = ((order i).val, _) ∨
    parentEdge H φ s (order i) = (_, (order i).val)
  rw [hp]
  unfold parentEdge
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end WeldedPath.Supplement.ForestOrder

end

-- Solutions.WeightedForestFactorization
section

/-! Finite weighted laws split by a separator.  All identities also cover zero
normalizers: division is the ordinary totalized division on `ℝ`. -/

namespace FiniteWeightedForest

open scoped BigOperators

section ProductLaws

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

/-- Reindexing a product of two finite weights factors its normalizer. -/
theorem sum_factor {R : Type*} [CommSemiring R]
    (e : Ω ≃ A × B) (f : A → R) (g : B → R) :
    (∑ ω, f (e ω).1 * g (e ω).2) = (∑ a, f a) * ∑ b, g b := by
  rw [Fintype.sum_equiv e _ (fun p => f p.1 * g p.2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- A centered function of one branch is orthogonal to every function of the
other branch. With `R = ℂ`, the first function may include complex conjugation. -/
theorem weighted_centered_sum {R : Type*} [CommSemiring R]
    (e : Ω ≃ A × B) (f u : A → R) (g v : B → R)
    (hu : ∑ a, f a * u a = 0) :
    (∑ ω, f (e ω).1 * g (e ω).2 * (u (e ω).1 * v (e ω).2)) = 0 := by
  calc
    _ = ∑ ω, (f (e ω).1 * u (e ω).1) * (g (e ω).2 * v (e ω).2) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = (∑ a, f a * u a) * ∑ b, g b * v b :=
      sum_factor e (fun a => f a * u a) (fun b => g b * v b)
    _ = 0 := by rw [hu, zero_mul]

/-- A constant shared factor cancels from a normalized finite law. -/
theorem normalize_scale (w : Ω → ℝ) (c : ℝ) (hc : c ≠ 0) (ω : Ω) :
    (c * w ω) / (∑ η, c * w η) = w ω / ∑ η, w η := by
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- The normalized product law is the product of the normalized branch laws. -/
theorem normalize_factor (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ) (ω : Ω) :
    (f (e ω).1 * g (e ω).2) / (∑ η, f (e η).1 * g (e η).2) =
      (f (e ω).1 / ∑ a, f a) * (g (e ω).2 / ∑ b, g b) := by
  rw [sum_factor]
  exact (div_mul_div_comm _ _ _ _).symm

/-- Conditional weights on a rectangular event remain a product law. -/
theorem conditional_factor (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ)
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] (ω : Ω) :
    (if P (e ω).1 ∧ Q (e ω).2 then f (e ω).1 * g (e ω).2 else 0) /
      (∑ η, if P (e η).1 ∧ Q (e η).2 then f (e η).1 * g (e η).2 else 0) =
      ((if P (e ω).1 then f (e ω).1 else 0) /
        ∑ a, if P a then f a else 0) *
      ((if Q (e ω).2 then g (e ω).2 else 0) /
        ∑ b, if Q b then g b else 0) := by
  have h (a : A) (b : B) :
      (if P a ∧ Q b then f a * g b else 0) =
        (if P a then f a else 0) * (if Q b then g b else 0) := by
    split_ifs <;> simp_all
  simp_rw [h]
  exact normalize_factor e (fun a => if P a then f a else 0)
    (fun b => if Q b then g b else 0) ω

/-- Fixing the two endpoints of a bridge makes its kernel a constant, so the
two sides are conditionally independent. No positivity assumptions are needed
apart from the bridge value being nonzero. -/
theorem bridge_conditional_factor {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ)
    (left : A → X) (right : B → Y) (K : X → Y → ℝ)
    (x : X) (y : Y) (hK : K x y ≠ 0) (ω : Ω) :
    (if left (e ω).1 = x ∧ right (e ω).2 = y then
        f (e ω).1 * g (e ω).2 * K (left (e ω).1) (right (e ω).2) else 0) /
      (∑ η, if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 * K (left (e η).1) (right (e η).2) else 0) =
      ((if left (e ω).1 = x then f (e ω).1 else 0) /
        ∑ a, if left a = x then f a else 0) *
      ((if right (e ω).2 = y then g (e ω).2 else 0) /
        ∑ b, if right b = y then g b else 0) := by
  have h (η : Ω) :
      (if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 * K (left (e η).1) (right (e η).2) else 0) =
      K x y * (if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 else 0) := by
    by_cases hxy : left (e η).1 = x ∧ right (e η).2 = y
    · simp [hxy, hxy.1, hxy.2, mul_comm]
    · simp [hxy]
  simp_rw [h]
  rw [normalize_scale (fun η => if left (e η).1 = x ∧ right (e η).2 = y then
    f (e η).1 * g (e η).2 else 0) _ hK]
  exact conditional_factor e f g (fun a => left a = x) (fun b => right b = y) ω

end ProductLaws

section VertexPartition

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]

/-- Restrict an assignment to the two sides of a finite vertex separator. -/
def splitAssignment (S : Finset V) :
    (V → X) ≃ (({v // v ∈ S} → X) × ({v // v ∉ S} → X)) :=
  Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => X)

@[simp] theorem splitAssignment_left (S : Finset V) (φ : V → X) (u : {v // v ∈ S}) :
    (splitAssignment S φ).1 u = φ u := rfl

@[simp] theorem splitAssignment_right (S : Finset V) (φ : V → X) (u : {v // v ∉ S}) :
    (splitAssignment S φ).2 u = φ u := rfl

theorem sum_split (S : Finset V) (f : ({v // v ∈ S} → X) → ℝ)
    (g : ({v // v ∉ S} → X) → ℝ) :
    (∑ φ : V → X, f (fun u => φ u) * g (fun u => φ u)) =
      (∑ a, f a) * ∑ b, g b :=
  sum_factor (splitAssignment S) f g

end VertexPartition

section EdgeProducts

variable {V X : Type*} [DecidableEq V]

/-- A product of possibly edge-dependent transition weights. -/
noncomputable def edgeWeight (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (φ : V → X) : ℝ := ∏ p ∈ E, K p (φ p.1) (φ p.2)

/-- Deleting one stored edge removes exactly its kernel factor. -/
theorem edgeWeight_erase (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (φ : V → X) (e : V × V) (he : e ∈ E) :
    edgeWeight E K φ = edgeWeight (E.erase e) K φ * K e (φ e.1) (φ e.2) := by
  classical
  exact (Finset.prod_erase_mul E (fun p => K p (φ p.1) (φ p.2)) he).symm

/-- The remaining product separates by the side containing the first endpoint.
For a graph separator, both endpoints of every remaining edge lie on this side. -/
theorem edgeWeight_split (E : Finset (V × V)) (S : Finset V)
    (K : (V × V) → X → X → ℝ) (φ : V → X) :
    edgeWeight E K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ S)) K φ *
      edgeWeight (E.filter (fun p => p.1 ∉ S)) K φ := by
  classical
  exact (Finset.prod_filter_mul_prod_filter_not E (fun p => p.1 ∈ S)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Exact one-edge separator factorization of an arbitrary edge-weight product. -/
theorem edgeWeight_bridge (E : Finset (V × V)) (S : Finset V)
    (K : (V × V) → X → X → ℝ) (φ : V → X) (e : V × V) (he : e ∈ E) :
    edgeWeight E K φ =
      edgeWeight ((E.erase e).filter (fun p => p.1 ∈ S)) K φ *
      edgeWeight ((E.erase e).filter (fun p => p.1 ∉ S)) K φ *
      K e (φ e.1) (φ e.2) := by
  rw [edgeWeight_erase E K φ e he, edgeWeight_split (E.erase e) S K φ]

end EdgeProducts

end FiniteWeightedForest

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

-- Solutions.WeldedPathKappaWalk
section

namespace WeldedPath.Supplement.KappaWalk

open WeldedInstance KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma class_tail_injective (hG : G.IsProperColoring) (b : PClass n l) :
    Set.InjOn Edge.tail (G.classEdges l b.1) := by
  intro e he e' he' htail
  by_contra hne
  exact (hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.tail, Or.inl rfl, Or.inl htail⟩) (class_color he he')

lemma class_head_injective (hG : G.IsProperColoring) (b : PClass n l) :
    Set.InjOn (Edge.head n) (G.classEdges l b.1) := by
  intro e he e' he' hhead
  by_contra hne
  exact (hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.head n, Or.inr rfl, Or.inr hhead⟩) (class_color he he')

lemma vertex_lt_label (hn : 2 ≤ n) {v : ℕ} (hv : IsVertex n v) :
    v < labelBound n + 1 := by
  have hp : 2 ^ (n + 2) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold IsVertex numV at hv
  unfold labelBound
  omega

lemma sum_uniform_label_eq_one (S : Finset ℕ) (m : ℕ)
    (hc : S.card = m) (hm : 0 < m) (hS : ∀ v ∈ S, v < labelBound n + 1) :
    (∑ v : Label n, if v.1 ∈ S then 1 / (m : ℝ) else 0) = 1 := by
  classical
  have hcard : (Finset.univ.filter fun v : Label n => v.1 ∈ S).card = S.card := by
    apply Finset.card_bij (fun v _ => v.1)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv w hw h
      exact Fin.ext h
    · intro v hv
      exact ⟨⟨v, hS v hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard, hc]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

lemma kappa_label_row_sum_eq_one (hG : G.IsValid) (hn : 2 ≤ n)
    {u : ℕ} {α : Fin 3} {b : PClass n l} {e : ↥(G.classEdges l b.1)} {t : Bool}
    (hpd : permData l G u α = some ⟨b, e, t⟩) :
    (∑ v : Label n, kappa l G α u v.1) = 1 := by
  classical
  have hm : 0 < classSize l G b := Finset.card_pos.mpr ⟨e.1, e.2⟩
  cases t
  · simpa only [kappa, hpd, Bool.false_eq_true, false_and, true_and, false_or] using
      sum_uniform_label_eq_one ((G.classEdges l b.1).image Edge.tail) (classSize l G b)
        (Finset.card_image_iff.mpr (class_tail_injective hG.2 b)) hm (by
          intro v hv
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
          exact vertex_lt_label hn (LoopProof.edge_endpoints hG (Finset.mem_filter.mp hf).1).1)
  · simpa only [kappa, hpd, Bool.true_eq_false, false_and, true_and, or_false] using
      sum_uniform_label_eq_one ((G.classEdges l b.1).image (Edge.head n)) (classSize l G b)
        (Finset.card_image_iff.mpr (class_head_injective hG.2 b)) hm (by
          intro v hv
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
          exact vertex_lt_label hn (LoopProof.edge_endpoints hG (Finset.mem_filter.mp hf).1).2.1)

lemma mem_region_of_col {v : ℕ} (hv : IsVertex n v)
    (hlo : n - l - 1 ≤ col n v) (hhi : col n v ≤ n + l + 1) :
    v ∈ Vmid n l ∪ Vbd n l := by
  by_cases hm : n - l < col n v ∧ col n v < n + l
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv, hm⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hv, by omega⟩))

lemma class_endpoints_region (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) :
    e.1.tail ∈ Vmid n l ∪ Vbd n l ∧ e.1.head n ∈ Vmid n l ∪ Vbd n l := by
  have he := Finset.mem_filter.mp e.2
  have hend := LoopProof.edge_endpoints hG he.1
  obtain ⟨e, hem⟩ := e
  cases e with
  | tree v =>
    dsimp only at he hend ⊢
    have hc : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      have hb := he.2
      simp only [WeldedInstance.bEdge, if_neg h] at hb
      cases hb
    simp only [Edge.tail] at hend ⊢
    constructor
    · apply mem_region_of_col hend.1 <;> omega
    · apply mem_region_of_col hend.2.1 <;> rcases hend.2.2 with h | h <;> omega
  | weld u v =>
    dsimp only at he hend ⊢
    have hw := hG.1.1 (u, v) (LoopProof.weld_mem_iff.mp he.1)
    dsimp only at hw
    simp only [Edge.tail, Edge.head] at hend ⊢
    constructor
    · apply mem_region_of_col hend.1 <;> omega
    · apply mem_region_of_col hend.2.1 <;> omega

lemma kappa_output_region (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) : v ∈ Vmid n l ∪ Vbd n l := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (Edge.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    rcases hm with ⟨_, hv⟩ | ⟨_, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      exact (class_endpoints_region hG ⟨e', he'⟩).2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      exact (class_endpoints_region hG ⟨e', he'⟩).1

lemma kappa_zero_outside_region (hG : G.IsValid) (α : Fin 3) (u v : ℕ)
    (hv : v ∉ Vmid n l ∪ Vbd n l) : kappa l G α u v = 0 := by
  by_contra h
  exact hv (kappa_output_region hG h)

noncomputable def step (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) : Label n → ℝ := fun y =>
  ∑ x : Label n, p x * kappa l G α x.1 y.1

noncomputable def walk (l : ℕ) (G : WeldedInstance n) :
    List (Fin 3) → (Label n → ℝ) → (Label n → ℝ)
  | [], p => p
  | α :: cs, p => walk l G cs (step l G α p)

lemma walk_nonneg (l : ℕ) (G : WeldedInstance n) (cs : List (Fin 3))
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) : ∀ x, 0 ≤ walk l G cs p x := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_step_nonneg l G α p hp x.1)

lemma walk_point_bound (hG : G.IsValid) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    ∀ x, walk l G cs p x ≤ M := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_propagates_point_bound hG α p M hM hp x.1)

lemma walk_abs_bound (hG : G.IsValid) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) :
    ∀ x, |walk l G cs p x| ≤ M := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_propagates_abs_bound hG α p M hM hp x.1)

lemma walk_mass_le (l : ℕ) (G : WeldedInstance n) (cs : List (Fin 3))
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ x, walk l G cs p x) ≤ ∑ x, p x := by
  induction cs generalizing p with
  | nil => exact le_rfl
  | cons α cs ih =>
    exact (ih (step l G α p) (fun x => kappa_step_nonneg l G α p hp x.1)).trans
      (kappa_step_mass_le l G α p hp)

noncomputable def kill (B : Finset ℕ) (p : Label n → ℝ) : Label n → ℝ :=
  fun x => if x.1 ∈ B then 0 else p x

noncomputable def safeWalk (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) :
    List (Fin 3) → (Label n → ℝ) → (Label n → ℝ)
  | [], p => kill B p
  | α :: cs, p => safeWalk l G B cs (step l G α (kill B p))

lemma kill_nonneg (B : Finset ℕ) (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ kill B p x := by
  intro x
  unfold kill
  split
  · exact le_rfl
  · exact hp x

lemma kill_point_bound (B : Finset ℕ) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) : ∀ x, kill B p x ≤ M := by
  intro x
  unfold kill
  split
  · exact hM
  · exact hp x

lemma kill_mass_loss (B : Finset ℕ) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    (∑ x, p x) - (B.card : ℝ) * M ≤ ∑ x, kill B p x := by
  classical
  let T := Finset.univ.filter fun x : Label n => x.1 ∈ B
  have hcard : T.card ≤ B.card := Finset.card_le_card_of_injOn Fin.val
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun _ _ _ _ h => Fin.ext h)
  have hbad : (∑ x : Label n, if x.1 ∈ B then p x else 0) ≤ (B.card : ℝ) * M := by
    calc
      _ ≤ ∑ x : Label n, if x.1 ∈ B then M else 0 := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs
        · exact hp x
        · exact le_rfl
      _ = (T.card : ℝ) * M := by
        rw [← Finset.sum_filter]
        simp [T]
      _ ≤ (B.card : ℝ) * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  have hid : (∑ x, p x) = (∑ x, kill B p x) + ∑ x, if x.1 ∈ B then p x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    unfold kill
    split_ifs <;> simp
  linarith

lemma safeWalk_nonneg (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (cs : List (Fin 3)) (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ safeWalk l G B cs p x := by
  induction cs generalizing p with
  | nil => exact kill_nonneg B p hp
  | cons α cs ih =>
    exact ih _ (fun x => kappa_step_nonneg l G α _ (kill_nonneg B p hp) x.1)

lemma safeWalk_point_bound (hG : G.IsValid) (B : Finset ℕ) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    ∀ x, safeWalk l G B cs p x ≤ M := by
  induction cs generalizing p with
  | nil => exact kill_point_bound B p M hM hp
  | cons α cs ih =>
    exact ih _ (fun x => kappa_propagates_point_bound hG α _ M hM
      (kill_point_bound B p M hM hp) x.1)

lemma step_mass_eq_of_support (α : Fin 3) (p : Label n → ℝ) (S : Finset ℕ)
    (hp : ∀ x, x.1 ∉ S → p x = 0)
    (hrow : ∀ x : Label n, x.1 ∈ S → (∑ y : Label n, kappa l G α x.1 y.1) = 1) :
    (∑ x, step l G α p x) = ∑ x, p x := by
  unfold step
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : x.1 ∈ S
  · rw [hrow x hx, mul_one]
  · rw [hp x hx, zero_mul]

lemma safeWalk_mass_lower (hG : G.IsValid) (S B : Finset ℕ)
    (hstay : ∀ α : Fin 3, ∀ x y : Label n, y.1 ∉ S → kappa l G α x.1 y.1 = 0)
    (hrow : ∀ α : Fin 3, ∀ x : Label n, x.1 ∈ S → x.1 ∉ B →
      (∑ y : Label n, kappa l G α x.1 y.1) = 1)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (hsupp : ∀ x, x.1 ∉ S → p x = 0) :
    (∑ x, p x) - ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * M ≤
      ∑ x, safeWalk l G B cs p x := by
  classical
  induction cs generalizing p with
  | nil => simpa [safeWalk] using kill_mass_loss B p M hM hp
  | cons α cs ih =>
    have hcap : ∀ x, step l G α (kill B p) x ≤ M :=
      fun x => kappa_propagates_point_bound hG α _ M hM
        (kill_point_bound B p M hM hp) x.1
    have hs : ∀ x, x.1 ∉ S → step l G α (kill B p) x = 0 := by
      intro y hy
      unfold step
      apply Finset.sum_eq_zero
      intro x _
      rw [hstay α x y hy, mul_zero]
    have heq : (∑ x, step l G α (kill B p) x) = ∑ x, kill B p x := by
      apply step_mass_eq_of_support α _ (S \ B)
      · intro x hx
        by_cases hb : x.1 ∈ B
        · simp [kill, hb]
        · have hns : x.1 ∉ S := by simpa [Finset.mem_sdiff, hb] using hx
          simp [kill, hb, hsupp x hns]
      · intro x hx
        exact hrow α x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
    have hi := ih _ hcap hs
    have hloss := kill_mass_loss B p M hM hp
    rw [heq] at hi
    simp only [safeWalk, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    nlinarith

lemma safeWalk_conditioned_point_bound (hG : G.IsValid) (B : Finset ℕ)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M)
    (hsurv : (1 / 2 : ℝ) ≤ ∑ x, safeWalk l G B cs p x) (y : Label n) :
    safeWalk l G B cs p y / (∑ x, safeWalk l G B cs p x) ≤ 2 * M := by
  have hz : 0 < ∑ x, safeWalk l G B cs p x := by linarith
  apply (div_le_iff₀ hz).mpr
  have hy := safeWalk_point_bound (l := l) hG B cs p M hM hp y
  nlinarith

lemma kappa_mid_row_sum_eq_one (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vmid n l) (α : Fin 3) :
    (∑ y : Label n, kappa l G α u y.1) = 1 := by
  have hne := MidPermData.permData_ne_none_of_mem_Vmid hG hn hl hln hu α
  cases hpd : permData l G u α with
  | none => exact False.elim (hne hpd)
  | some d =>
    obtain ⟨b, e, t⟩ := d
    exact kappa_label_row_sum_eq_one hG (by omega) hpd

lemma weld_mem_mid (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    {u : ℕ} (hu : u ∈ Vweld n) : u ∈ Vmid n l := by
  obtain ⟨hv, hc⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hv, by rcases hc with hc | hc <;> omega⟩

lemma kappa_weld_row_sum_eq_one (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vweld n) (α : Fin 3) :
    (∑ y : Label n, kappa l G α u y.1) = 1 :=
  kappa_mid_row_sum_eq_one hG hn hl hln (weld_mem_mid hn hl hln hu) α

lemma safeWalk_region_mass_lower (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M)
    (hsupp : ∀ x, x.1 ∉ Vmid n l ∪ Vbd n l → p x = 0) :
    (∑ x, p x) - ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * M ≤
      ∑ x, safeWalk l G B cs p x := by
  apply safeWalk_mass_lower hG (Vmid n l ∪ Vbd n l) B
    (fun α x y hy => kappa_zero_outside_region hG α x.1 y.1 hy) _ cs p M hM hp hsupp
  intro α x hx hb
  have hmid : x.1 ∈ Vmid n l := (Finset.mem_union.mp hx).resolve_right (fun h => hb (hB h))
  exact kappa_mid_row_sum_eq_one hG hn hl hln hmid α

lemma safeWalk_region_normalized_bound (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (cs : List (Fin 3)) (p : Label n → ℝ)
    (hp : ∀ x, p x ≤ 4 / (2 : ℝ) ^ n) (hmass : (∑ x, p x) = 1)
    (hsupp : ∀ x, x.1 ∉ Vmid n l ∪ Vbd n l → p x = 0)
    (hsmall : ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (y : Label n) :
    safeWalk l G B cs p y / (∑ x, safeWalk l G B cs p x) ≤ 8 / (2 : ℝ) ^ n := by
  have hs := safeWalk_region_mass_lower hG hn hl hln B hB cs p _ (by positivity) hp hsupp
  rw [hmass] at hs
  have hsurv : (1 / 2 : ℝ) ≤ ∑ x, safeWalk l G B cs p x := by linarith
  have hb := safeWalk_conditioned_point_bound hG B cs p _ (by positivity) hp hsurv y
  convert hb using 1 <;> ring

end WeldedPath.Supplement.KappaWalk

end

-- Solutions.WeldedPathKappaForest
section

namespace WeldedPath.Supplement.KappaForest

open scoped BigOperators

variable {X : Type*} [Fintype X]
variable {m : ℕ}

noncomputable def prefixLaw (K : (i : ℕ) → (Fin i → X) → X → ℝ) :
    (m : ℕ) → (Fin m → X) → ℝ
  | 0, _ => 1
  | m + 1, z => prefixLaw K m (Fin.init z) * K m (Fin.init z) (z (Fin.last m))

lemma sum_snoc (m : ℕ) (f : (Fin (m + 1) → X) → ℝ) :
    (∑ z, f z) = ∑ p : Fin m → X, ∑ y : X, f (Fin.snoc p y) := by
  classical
  calc
    _ = ∑ q : X × (Fin m → X), f (Fin.snoc q.2 q.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m + 1) => X)).symm _ _
        (fun z => by simp)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

omit [Fintype X] in
lemma prefixLaw_snoc (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (p : Fin m → X) (y : X) :
    prefixLaw K (m + 1) (Fin.snoc p y) = prefixLaw K m p * K m p y := by
  simp [prefixLaw]

omit [Fintype X] in
lemma prefixLaw_nonneg (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i p y, 0 ≤ K i p y) (m : ℕ) (z : Fin m → X) :
    0 ≤ prefixLaw K m z := by
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih => exact mul_nonneg (ih _) (hK _ _ _)

def before (z : Fin m → X) (i : Fin m) : Fin i.1 → X :=
  fun j => z ⟨j.1, lt_trans j.2 i.2⟩

omit [Fintype X] in
lemma prefixLaw_eq_prod (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (z : Fin m → X) :
    prefixLaw K m z = ∏ i : Fin m, K i.1 (before z i) (z i) := by
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih =>
    rw [prefixLaw, ih, Fin.prod_univ_castSucc]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro i _
      rfl
    · rfl

lemma prefixLaw_mass_le_one (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i p y, 0 ≤ K i p y) (hrow : ∀ i p, ∑ y, K i p y ≤ 1)
    (m : ℕ) : (∑ z, prefixLaw K m z) ≤ 1 := by
  classical
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih =>
    rw [sum_snoc]
    simp_rw [prefixLaw_snoc]
    calc
      _ = ∑ p, prefixLaw K m p * ∑ y, K m p y := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ p, prefixLaw K m p := Finset.sum_le_sum fun p _ => by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow m p)
          (prefixLaw_nonneg K hK m p)
      _ ≤ 1 := ih

open Classical in
noncomputable def marginal (w : (Fin m → X) → ℝ) (j : Fin m) (x : X) : ℝ :=
  ∑ z, if z j = x then w z else 0

lemma prefixLaw_old_marginal_le (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i p y, 0 ≤ K i p y) (hrow : ∀ i p, ∑ y, K i p y ≤ 1)
    (m : ℕ) (j : Fin m) (x : X) :
    marginal (prefixLaw K (m + 1)) j.castSucc x ≤ marginal (prefixLaw K m) j x := by
  classical
  unfold marginal
  rw [sum_snoc]
  simp only [prefixLaw_snoc, Fin.snoc_castSucc]
  apply Finset.sum_le_sum
  intro p _
  by_cases hpx : p j = x
  · simp only [hpx, if_true]
    rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow m p)
      (prefixLaw_nonneg K hK m p)
  · simp [hpx]

lemma prefixLaw_new_marginal (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (x : X) :
    marginal (prefixLaw K (m + 1)) (Fin.last m) x =
      ∑ p : Fin m → X, prefixLaw K m p * K m p x := by
  classical
  unfold marginal
  rw [sum_snoc]
  simp [prefixLaw_snoc]

lemma marginal_pushforward (w : (Fin m → X) → ℝ) (j : Fin m) (f : X → ℝ) :
    (∑ p, w p * f (p j)) = ∑ x, marginal w j x * f x := by
  classical
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp

omit [Fintype X] in
lemma prefixLaw_mono (K L : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hL : ∀ i z y, 0 ≤ L i z y) (hLK : ∀ i z y, L i z y ≤ K i z y)
    (m : ℕ) (z : Fin m → X) : prefixLaw L m z ≤ prefixLaw K m z := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact mul_le_mul (ih _) (hLK _ _ _) (hL _ _ _)
      (le_trans (prefixLaw_nonneg L hL m _) (ih _))

lemma marginal_mono (w v : (Fin m → X) → ℝ) (h : ∀ z, w z ≤ v z)
    (j : Fin m) (x : X) : marginal w j x ≤ marginal v j x := by
  classical
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact h z
  · exact le_rfl

open Classical in
noncomputable def maskKernel (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (i : ℕ) (z : Fin i → X) (y : X) : ℝ := if y ∈ B then 0 else K i z y

omit [Fintype X] in
lemma maskKernel_nonneg (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) : ∀ i z y, 0 ≤ maskKernel K B i z y := by
  intro i z y
  unfold maskKernel
  split
  · exact le_rfl
  · exact hK i z y

omit [Fintype X] in
lemma maskKernel_le (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) : ∀ i z y, maskKernel K B i z y ≤ K i z y := by
  intro i z y
  unfold maskKernel
  split
  · exact hK i z y
  · exact le_rfl

omit [Fintype X] in
lemma masked_prefixLaw_le (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) (m : ℕ) (z : Fin m → X) :
    prefixLaw (maskKernel K B) m z ≤ prefixLaw K m z :=
  prefixLaw_mono K _ (maskKernel_nonneg K B hK) (maskKernel_le K B hK) m z

lemma masked_mass_step (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (m : ℕ)
    (hrow : ∀ z, prefixLaw (maskKernel K B) m z ≠ 0 → ∑ y, K m z y = 1) :
    (∑ z, prefixLaw (maskKernel K B) (m + 1) z) =
      (∑ z, prefixLaw (maskKernel K B) m z) -
        ∑ y ∈ B, ∑ z, prefixLaw (maskKernel K B) m z * K m z y := by
  classical
  rw [sum_snoc]
  simp only [prefixLaw_snoc]
  rw [Finset.sum_comm (s := B)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hz : prefixLaw (maskKernel K B) m z * (∑ y, K m z y) =
      prefixLaw (maskKernel K B) m z := by
    by_cases h : prefixLaw (maskKernel K B) m z = 0
    · simp [h]
    · rw [hrow z h, mul_one]
  have htot : (∑ y, prefixLaw (maskKernel K B) m z * K m z y) =
      prefixLaw (maskKernel K B) m z := by
    rw [← Finset.mul_sum]
    exact hz
  have hid : (∑ y, prefixLaw (maskKernel K B) m z * K m z y) =
      (∑ y, prefixLaw (maskKernel K B) m z * maskKernel K B m z y) +
        ∑ y ∈ B, prefixLaw (maskKernel K B) m z * K m z y := by
    have hb : (∑ y ∈ B, prefixLaw (maskKernel K B) m z * K m z y) =
        ∑ y, if y ∈ B then prefixLaw (maskKernel K B) m z * K m z y else 0 := by
      rw [← Finset.sum_filter]
      simp
    rw [hb]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ B <;> simp [maskKernel, hy]
  linarith

lemma masked_mass_lower (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) (M : ℝ) (m : ℕ)
    (hrow : ∀ i < m, ∀ z, prefixLaw (maskKernel K B) i z ≠ 0 → ∑ y, K i z y = 1)
    (hcap : ∀ i < m, ∀ y, marginal (prefixLaw K (i + 1)) (Fin.last i) y ≤ M) :
    1 - (m : ℝ) * (B.card : ℝ) * M ≤ ∑ z, prefixLaw (maskKernel K B) m z := by
  classical
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih =>
    have ih' := ih (fun i hi => hrow i (by omega)) (fun i hi => hcap i (by omega))
    rw [masked_mass_step K B m (hrow m (Nat.lt_succ_self m))]
    have hb : (∑ y ∈ B, ∑ z, prefixLaw (maskKernel K B) m z * K m z y) ≤
        (B.card : ℝ) * M := by
      calc
        _ ≤ ∑ y ∈ B, marginal (prefixLaw K (m + 1)) (Fin.last m) y := by
          apply Finset.sum_le_sum
          intro y _
          rw [prefixLaw_new_marginal]
          exact Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_right (masked_prefixLaw_le K B hK m z) (hK m z y)
        _ ≤ ∑ _y ∈ B, M := Finset.sum_le_sum fun y _ => hcap m (Nat.lt_succ_self m) y
        _ = _ := by simp
    push_cast
    nlinarith

omit [Fintype X] in
lemma prefixLaw_support (K : (i : ℕ) → (Fin i → X) → X → ℝ) (P : X → Prop)
    (hK : ∀ i z y, K i z y ≠ 0 → P y) (m : ℕ) (z : Fin m → X)
    (hz : prefixLaw K m z ≠ 0) : ∀ j, P (z j) := by
  rw [prefixLaw_eq_prod] at hz
  intro j
  exact hK _ _ _ ((Finset.prod_ne_zero_iff.mp hz) j (Finset.mem_univ j))

omit [Fintype X] in
open Classical in
lemma masked_prefixLaw_eq (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (m : ℕ) (z : Fin m → X) :
    prefixLaw (maskKernel K B) m z =
      if ∀ j, z j ∉ B then prefixLaw K m z else 0 := by
  classical
  by_cases h : ∀ j, z j ∉ B
  · rw [if_pos h]
    simp only [prefixLaw_eq_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact if_neg (h j)
  · rw [if_neg h, prefixLaw_eq_prod]
    obtain ⟨j, hj⟩ := not_forall.mp h
    have hj' : z j ∈ B := not_not.mp hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [maskKernel, hj'])

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def forestKernel (l : ℕ) (G : WeldedInstance n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (i : ℕ) (z : Fin i → Label n) (y : Label n) : ℝ :=
  kappa l G (color i) (match parent i with | none => (root i).1 | some j => (z j).1) y.1

lemma forestKernel_nonneg (l : ℕ) (G : WeldedInstance n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (i : ℕ) (z : Fin i → Label n) (y : Label n) :
    0 ≤ forestKernel l G parent root color i z y :=
  KappaKernel.kappa_nonneg _ _ _ _ _

lemma forestKernel_row_le (l : ℕ) (G : WeldedInstance n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (i : ℕ) (z : Fin i → Label n) :
    (∑ y, forestKernel l G parent root color i z y) ≤ 1 :=
  KappaKernel.kappa_label_row_sum_le_one _ _ _ _

lemma forestLaw_marginal_cap (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n) :
    ∀ (j : Fin m) (y : Label n),
      marginal (prefixLaw (forestKernel l G parent root color) m) j y ≤ 4 / (2 : ℝ) ^ n := by
  classical
  let K := forestKernel l G parent root color
  have hK : ∀ i z y, 0 ≤ K i z y := forestKernel_nonneg l G parent root color
  have hrow : ∀ i z, ∑ y, K i z y ≤ 1 := forestKernel_row_le l G parent root color
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  induction m with
  | zero => intro j; exact Fin.elim0 j
  | succ m ih =>
    have hr : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n :=
      fun i hi => hroot i (by omega)
    intro j y
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [prefixLaw_new_marginal]
      cases hpar : parent m with
      | none =>
        have hc := FirstFreeStep.kappa_from_weld_le hG hn hl
          (hroot m (Nat.lt_succ_self m) hpar) (color m) y.1
        calc
          _ ≤ ∑ z, prefixLaw K m z * (4 / (2 : ℝ) ^ n) := by
            apply Finset.sum_le_sum
            intro z _
            apply mul_le_mul_of_nonneg_left _ (prefixLaw_nonneg K hK m z)
            simpa only [K, forestKernel, hpar] using hc
          _ = (∑ z, prefixLaw K m z) * (4 / (2 : ℝ) ^ n) :=
            (Finset.sum_mul _ _ _).symm
          _ ≤ 1 * (4 / (2 : ℝ) ^ n) := mul_le_mul_of_nonneg_right
            (prefixLaw_mass_le_one K hK hrow m) hM
          _ = _ := one_mul _
      | some a =>
        change (∑ z, prefixLaw K m z * K m z y) ≤ _
        have he (z : Fin m → Label n) : K m z y = kappa l G (color m) (z a).1 y.1 := by
          simp only [K, forestKernel, hpar]
        simp_rw [he]
        rw [marginal_pushforward (prefixLaw K m) a
          (fun v : Label n => kappa l G (color m) v.1 y.1)]
        exact KappaKernel.kappa_propagates_point_bound hG (color m)
          (marginal (prefixLaw K m) a) _ hM (fun x => ih hr a x) y.1
    · exact (prefixLaw_old_marginal_le K hK hrow m j y).trans (ih hr j y)

open Classical in
noncomputable def labelBoundary (n : ℕ) (B : Finset ℕ) : Finset (Label n) :=
  Finset.univ.filter fun x => x.1 ∈ B

lemma labelBoundary_card_le (B : Finset ℕ) : (labelBoundary n B).card ≤ B.card := by
  apply Finset.card_le_card_of_injOn Fin.val
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy h
    exact Fin.ext h

lemma forestLaw_survival (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) :
    1 - (m : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤
      ∑ z, prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m z := by
  classical
  let K := forestKernel l G parent root color
  let C := labelBoundary n B
  have hK : ∀ i z y, 0 ≤ K i z y := forestKernel_nonneg l G parent root color
  have hsafe : ∀ i z y, maskKernel K C i z y ≠ 0 →
      y.1 ∈ Vmid n l ∪ Vbd n l ∧ y.1 ∉ B := by
    intro i z y hy
    have hc : y ∉ C := by intro h; exact hy (if_pos h)
    have hk : K i z y ≠ 0 := by simpa only [maskKernel, if_neg hc] using hy
    exact ⟨KappaWalk.kappa_output_region hG hk,
      fun h => hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
  have hrows : ∀ i < m, ∀ z, prefixLaw (maskKernel K C) i z ≠ 0 →
      (∑ y, K i z y) = 1 := by
    intro i hi z hz
    have hs := prefixLaw_support (maskKernel K C) _ hsafe i z hz
    cases hpar : parent i with
    | none =>
      simpa only [K, forestKernel, hpar] using
        KappaWalk.kappa_weld_row_sum_eq_one hG hn hl hln (hroot i hi hpar) (color i)
    | some j =>
      have hmid : (z j).1 ∈ Vmid n l :=
        (Finset.mem_union.mp (hs j).1).resolve_right (fun h => (hs j).2 (hB h))
      simpa only [K, forestKernel, hpar] using
        KappaWalk.kappa_mid_row_sum_eq_one hG hn hl hln hmid (color i)
  have hcaps : ∀ i < m, ∀ y,
      marginal (prefixLaw K (i + 1)) (Fin.last i) y ≤ 4 / (2 : ℝ) ^ n := by
    intro i hi y
    exact forestLaw_marginal_cap hG (by omega) (by omega) parent root color (i + 1)
      (fun j hj => hroot j (by omega)) (Fin.last i) y
  have hh := masked_mass_lower K C hK (4 / (2 : ℝ) ^ n) m hrows hcaps
  have hc : (C.card : ℝ) ≤ B.card := by exact_mod_cast (labelBoundary_card_le (n := n) B)
  have hn0 : 0 ≤ (m : ℝ) := by positivity
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hn0) hM
  exact (sub_le_sub_left hmul 1).trans hh

lemma forestLaw_conditioned_marginal_cap (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (hsmall : (m : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (j : Fin m) (y : Label n) :
    marginal (prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m) j y /
      (∑ z, prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m z)
        ≤ 8 / (2 : ℝ) ^ n := by
  let K := forestKernel l G parent root color
  let C := labelBoundary n B
  have hs := forestLaw_survival hG hn hl hln parent root color m hroot B hB
  have hz : (1 / 2 : ℝ) ≤ ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hzpos : 0 < ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hle := marginal_mono _ _
    (masked_prefixLaw_le K C (forestKernel_nonneg l G parent root color) m) j y
  have hcap := forestLaw_marginal_cap (l := l) hG (by omega) (by omega)
    parent root color m hroot j y
  apply (div_le_iff₀ hzpos).mpr
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hh := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * (4 / (2 : ℝ) ^ n))
  calc
    _ ≤ 4 / (2 : ℝ) ^ n := hle.trans hcap
    _ ≤ _ := by convert hh using 1 <;> first | rfl | ring

end WeldedPath.Supplement.KappaForest

end

-- Solutions.WeightedForestProcess
section

namespace FiniteWeightedForest

open scoped BigOperators
open Classical

variable {V X : Type*} [DecidableEq V]

/-- Under coordinate fixing on `F`, the weights of all edges entirely in `F`
are a common constant. The other edges are exactly the sampling steps. -/
theorem edgeWeight_fixed_split (E : Finset (V × V)) (F : Finset V)
    (K : (V × V) → X → X → ℝ) (φ φ₀ : V → X)
    (hφ : ∀ v ∈ F, φ v = φ₀ v) :
    edgeWeight E K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ F ∧ p.2 ∈ F)) K φ₀ *
      edgeWeight (E.filter (fun p => ¬(p.1 ∈ F ∧ p.2 ∈ F))) K φ := by
  have hfixed :
      edgeWeight (E.filter (fun p => p.1 ∈ F ∧ p.2 ∈ F)) K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ F ∧ p.2 ∈ F)) K φ₀ := by
    apply Finset.prod_congr rfl
    intro p hp
    have hf := (Finset.mem_filter.mp hp).2
    exact congrArg₂ (K p) (hφ p.1 hf.1) (hφ p.2 hf.2)
  rw [← hfixed]
  exact (Finset.prod_filter_mul_prod_filter_not E (fun p => p.1 ∈ F ∧ p.2 ∈ F)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Enumerating the edges and orienting each one away from its parent turns
the undirected edge product into the product of parent-to-child kernels. -/
theorem edgeWeight_eq_oriented_prod {m : ℕ} (E : Finset (V × V))
    (K : (V × V) → X → X → ℝ)
    (hK : ∀ p ∈ E, ∀ x y, K p x y = K p y x)
    (edges : Fin m ≃ {p // p ∈ E}) (parent child : Fin m → V)
    (horient : ∀ i, (edges i).val = (parent i, child i) ∨
      (edges i).val = (child i, parent i)) (φ : V → X) :
    edgeWeight E K φ = ∏ i : Fin m, K (edges i).val (φ (parent i)) (φ (child i)) := by
  calc
    _ = ∏ p : {p // p ∈ E}, K p.val (φ p.val.1) (φ p.val.2) :=
      (Finset.prod_coe_sort E _).symm
    _ = ∏ i : Fin m, K (edges i).val (φ (edges i).val.1) (φ (edges i).val.2) :=
      (Equiv.prod_comp edges _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rcases horient i with hi | hi
      · simp only [hi]
      · simpa only [hi] using hK (edges i).val (edges i).property (φ (child i)) (φ (parent i))

/-- Exact product-to-process adapter. The hypothesis identifies each local
sampling step; graph construction and the finite change of coordinates can
be proved separately without another probabilistic assumption. -/
theorem edgeWeight_eq_prefixLaw [Fintype X] {m : ℕ} (E : Finset (V × V))
    (K : (V × V) → X → X → ℝ)
    (hK : ∀ p ∈ E, ∀ x y, K p x y = K p y x)
    (edges : Fin m ≃ {p // p ∈ E}) (parent child : Fin m → V)
    (horient : ∀ i, (edges i).val = (parent i, child i) ∨
      (edges i).val = (child i, parent i))
    (step : (i : ℕ) → (Fin i → X) → X → ℝ) (φ : V → X)
    (hstep : ∀ i : Fin m,
      step i.val (WeldedPath.Supplement.KappaForest.before (fun j => φ (child j)) i)
        (φ (child i)) = K (edges i).val (φ (parent i)) (φ (child i))) :
    edgeWeight E K φ =
      WeldedPath.Supplement.KappaForest.prefixLaw step m (fun i => φ (child i)) := by
  rw [edgeWeight_eq_oriented_prod E K hK edges parent child horient φ,
    WeldedPath.Supplement.KappaForest.prefixLaw_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (hstep i).symm

end FiniteWeightedForest

end

-- Solutions.WeightedFixedAssignments
section

namespace FiniteWeightedForest

open scoped BigOperators
open Classical

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]

def glueFixed (F : Finset V) (φ₀ : V → X) (z : {v // v ∉ F} → X) (v : V) : X :=
  if h : v ∈ F then φ₀ v else z ⟨v, h⟩

@[simp] theorem glueFixed_on (F : Finset V) (φ₀ : V → X) (z : {v // v ∉ F} → X)
    (v : V) (hv : v ∈ F) : glueFixed F φ₀ z v = φ₀ v := by
  simp [glueFixed, hv]

@[simp] theorem glueFixed_off (F : Finset V) (φ₀ : V → X) (z : {v // v ∉ F} → X)
    (v : {v // v ∉ F}) : glueFixed F φ₀ z v = z v := by
  simp [glueFixed, v.property]

/-- Coordinate fixing leaves precisely one independent coordinate for every
vertex outside the fixed set. -/
def fixedAssignmentEquiv (F : Finset V) (φ₀ : V → X) :
    {φ : V → X // ∀ v ∈ F, φ v = φ₀ v} ≃ ({v // v ∉ F} → X) where
  toFun φ v := φ.val v
  invFun z := ⟨glueFixed F φ₀ z, fun v hv => glueFixed_on F φ₀ z v hv⟩
  left_inv φ := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ F
    · simp [glueFixed, hv, φ.property v hv]
    · simp [glueFixed, hv]
  right_inv z := by
    funext v
    exact glueFixed_off F φ₀ z v

/-- Exact finite change of variables on a coordinate-fixing event. -/
theorem sum_fixed_assignments {R : Type*} [AddCommMonoid R]
    (F : Finset V) (φ₀ : V → X) (w : (V → X) → R) :
    (∑ φ : V → X, if ∀ v ∈ F, φ v = φ₀ v then w φ else 0) =
      ∑ z : {v // v ∉ F} → X, w (glueFixed F φ₀ z) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun φ : V → X => ∀ v ∈ F, φ v = φ₀ v)
    (Finset.univ.filter (fun φ : V → X => ∀ v ∈ F, φ v = φ₀ v))
    (fun φ => by simp) w]
  exact Fintype.sum_equiv (fixedAssignmentEquiv F φ₀) _ _ (fun φ => by
    congr 1
    exact congrArg Subtype.val ((fixedAssignmentEquiv F φ₀).left_inv φ).symm)

theorem sum_fixed_restrictions {R : Type*} [AddCommMonoid R]
    (F : Finset V) (φ₀ : V → X) (w : ({v // v ∉ F} → X) → R) :
    (∑ φ : V → X, if ∀ v ∈ F, φ v = φ₀ v then w (fun v => φ v) else 0) =
      ∑ z : {v // v ∉ F} → X, w z := by
  rw [sum_fixed_assignments F φ₀ (fun φ => w (fun v => φ v))]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  funext v
  exact glueFixed_off F φ₀ z v

/-- If a full-assignment law is a common factor times a free-coordinate
law, its normalizer has exactly the same common factor. -/
theorem sum_of_fixed_weight (F : Finset V) (φ₀ : V → X) (w : (V → X) → ℝ)
    (v : ({u // u ∉ F} → X) → ℝ) (c : ℝ)
    (hw : ∀ φ, w φ = if ∀ u ∈ F, φ u = φ₀ u then c * v (fun u => φ u) else 0) :
    (∑ φ, w φ) = c * ∑ z, v z := by
  simp_rw [hw]
  rw [sum_fixed_restrictions F φ₀ (fun z => c * v z), Finset.mul_sum]

/-- The corresponding normalized laws agree pointwise, including assignments
outside the fixed-coordinate event and zero free normalizers. -/
theorem normalize_fixed_weight (F : Finset V) (φ₀ : V → X) (w : (V → X) → ℝ)
    (v : ({u // u ∉ F} → X) → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hw : ∀ φ, w φ = if ∀ u ∈ F, φ u = φ₀ u then c * v (fun u => φ u) else 0)
    (φ : V → X) :
    w φ / (∑ ψ, w ψ) =
      if ∀ u ∈ F, φ u = φ₀ u then v (fun u => φ u) / (∑ z, v z) else 0 := by
  rw [sum_of_fixed_weight F φ₀ w v c hw, hw φ]
  split_ifs
  · exact mul_div_mul_left _ _ hc
  · exact zero_div _

/-- Marginal probabilities of a free vertex transfer without an additional
cardinality factor. -/
theorem fixed_weight_marginal (F : Finset V) (φ₀ : V → X) (w : (V → X) → ℝ)
    (v : ({u // u ∉ F} → X) → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hw : ∀ φ, w φ = if ∀ u ∈ F, φ u = φ₀ u then c * v (fun u => φ u) else 0)
    (u : {u // u ∉ F}) (x : X) :
    (∑ φ, if φ u = x then w φ else 0) / (∑ φ, w φ) =
      (∑ z, if z u = x then v z else 0) / (∑ z, v z) := by
  have hevent (φ : V → X) :
      (if φ u = x then w φ else 0) =
        if ∀ a ∈ F, φ a = φ₀ a then
          c * (if (fun a : {a // a ∉ F} => φ a) u = x then v (fun a => φ a) else 0) else 0 := by
    rw [hw φ]
    split_ifs <;> simp_all
  have hnum := sum_of_fixed_weight F φ₀ (fun φ => if φ u = x then w φ else 0)
    (fun z => if z u = x then v z else 0) c hevent
  rw [hnum, sum_of_fixed_weight F φ₀ w v c hw]
  exact mul_div_mul_left _ _ hc

end FiniteWeightedForest

end

-- Solutions.WeightedForestSeparator
section

namespace FiniteWeightedForest

open scoped BigOperators

section BranchWeights

variable {V X : Type*} [DecidableEq V] [Zero X]

/-- Extend a branch assignment by zero off that branch. Off-branch values do
not affect the branch weight when all its edges stay in the branch. -/
def extendAssignment (P : V → Prop) [DecidablePred P] (a : {v // P v} → X) (v : V) : X :=
  if h : P v then a ⟨v, h⟩ else 0

noncomputable def branchWeight (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (a : {v // P v} → X) : ℝ :=
  edgeWeight (E.filter (fun p => P p.1)) K (extendAssignment P a)

theorem branchWeight_restrict (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (φ : V → X)
    (hclosed : ∀ p ∈ E, P p.1 ↔ P p.2) :
    branchWeight E P K (fun v => φ v) =
      edgeWeight (E.filter (fun p => P p.1)) K φ := by
  classical
  unfold branchWeight edgeWeight
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hpE, hpP⟩ := Finset.mem_filter.mp hp
  simp [extendAssignment, hpP, (hclosed p hpE).mp hpP]

/-- An edge product on a graph with a one-edge separator is a product of its
two branch weights and the separating edge kernel. -/
theorem edgeWeight_bridge_branches (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (φ : V → X)
    (e : V × V) (he : e ∈ E)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2) :
    edgeWeight E K φ =
      branchWeight (E.erase e) P K (fun v => φ v) *
      branchWeight (E.erase e) (fun v => ¬P v) K (fun v => φ v) *
      K e (φ e.1) (φ e.2) := by
  classical
  rw [branchWeight_restrict _ P _ _ hclosed,
    branchWeight_restrict _ (fun v => ¬P v) _ _ (fun p hp => not_congr (hclosed p hp)),
    edgeWeight_erase E K φ e he]
  congr 1
  exact (Finset.prod_filter_mul_prod_filter_not (E.erase e) (fun p => P p.1)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Exact conditional independence of the branches of a weighted tree after
the values of the two endpoints of a deleted edge are fixed. -/
theorem tree_bridge_conditional_factor [Fintype V] [Fintype X] [DecidableEq X]
    (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (e : V × V) (he : e ∈ E)
    (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (x y : X) (hK : K e x y ≠ 0) (φ : V → X) :
    (if φ e.1 = x ∧ φ e.2 = y then edgeWeight E K φ else 0) /
      (∑ ψ : V → X, if ψ e.1 = x ∧ ψ e.2 = y then edgeWeight E K ψ else 0) =
      ((if φ e.1 = x then branchWeight (E.erase e) P K (fun v => φ v) else 0) /
        ∑ a : {v // P v} → X,
          if a ⟨e.1, hleft⟩ = x then branchWeight (E.erase e) P K a else 0) *
      ((if φ e.2 = y then branchWeight (E.erase e) (fun v => ¬P v) K
          (fun v => φ v) else 0) /
        ∑ b : {v // ¬P v} → X,
          if b ⟨e.2, hright⟩ = y then branchWeight (E.erase e) (fun v => ¬P v) K b else 0) := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (ψ : V → X) := edgeWeight_bridge_branches E P K ψ e he hclosed
  simp_rw [hfactor]
  exact bridge_conditional_factor split
    (branchWeight (E.erase e) P K) (branchWeight (E.erase e) (fun v => ¬P v) K)
    (fun a => a ⟨e.1, hleft⟩) (fun b => b ⟨e.2, hright⟩) (K e) x y hK φ

end BranchWeights

section SupportedWeights

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Zero X]

/-- Edge-product weight with arbitrary restrictions at individual vertices. -/
noncomputable def forestWeight (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (allowed : V → X → Prop) (φ : V → X) : ℝ := by
  classical
  exact if ∀ v, allowed v (φ v) then edgeWeight E K φ else 0

noncomputable def supportedBranchWeight (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (a : {v // P v} → X) : ℝ := by
  classical
  exact if ∀ v : {v // P v}, allowed v.val (a v) then branchWeight E P K a else 0

theorem forestWeight_bridge_branches (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (φ : V → X) (e : V × V) (he : e ∈ E)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2) :
    forestWeight E K allowed φ =
      supportedBranchWeight (E.erase e) P K allowed (fun v => φ v) *
      supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed (fun v => φ v) *
      K e (φ e.1) (φ e.2) := by
  classical
  have hall : (∀ v, allowed v (φ v)) ↔
      (∀ v : {v // P v}, allowed v (φ v)) ∧
        (∀ v : {v // ¬P v}, allowed v (φ v)) := by
    constructor
    · intro h
      exact ⟨fun v => h v, fun v => h v⟩
    · rintro ⟨hl, hr⟩ v
      by_cases hv : P v
      · exact hl ⟨v, hv⟩
      · exact hr ⟨v, hv⟩
  unfold forestWeight supportedBranchWeight
  simp only [hall, edgeWeight_bridge_branches E P K φ e he hclosed,
    ite_and, mul_ite, ite_mul, mul_zero, zero_mul]
  split_ifs <;> rfl

/-- The separator law remains exact after imposing any local vertex support
conditions, including the allowed physical vertex set in `AbsForest.muComp`. -/
theorem supported_tree_bridge_conditional_factor [DecidableEq X]
    (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (e : V × V) (he : e ∈ E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (x y : X) (hK : K e x y ≠ 0) (φ : V → X) :
    (if φ e.1 = x ∧ φ e.2 = y then forestWeight E K allowed φ else 0) /
      (∑ ψ : V → X, if ψ e.1 = x ∧ ψ e.2 = y then forestWeight E K allowed ψ else 0) =
      ((if φ e.1 = x then supportedBranchWeight (E.erase e) P K allowed
          (fun v => φ v) else 0) /
        ∑ a : {v // P v} → X,
          if a ⟨e.1, hleft⟩ = x then supportedBranchWeight (E.erase e) P K allowed a else 0) *
      ((if φ e.2 = y then supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed
          (fun v => φ v) else 0) /
        ∑ b : {v // ¬P v} → X,
          if b ⟨e.2, hright⟩ = y then
            supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed b else 0) := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (ψ : V → X) := forestWeight_bridge_branches E P K allowed ψ e he hclosed
  simp_rw [hfactor]
  exact bridge_conditional_factor split
    (supportedBranchWeight (E.erase e) P K allowed)
    (supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed)
    (fun a => a ⟨e.1, hleft⟩) (fun b => b ⟨e.2, hright⟩) (K e) x y hK φ

end SupportedWeights

section ForestCuts

variable {V : Type*} [LinearOrder V]

def edgeGraph (E : Finset (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ E)

/-- With one increasing orientation per edge, erasing a stored pair deletes
the corresponding undirected edge. -/
theorem edgeGraph_erase_le_delete (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) (he : e ∈ E) :
    edgeGraph (E.erase e) ≤ (edgeGraph E).deleteEdges {s(e.1, e.2)} := by
  intro u v huv
  obtain ⟨hne, huv | hvu⟩ := huv
  · obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp huv
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨hne, Or.inl hmem⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact hneq (Prod.ext hu hv)
    · have h := horder (u, v) hmem
      have heo := horder e he
      simp only [hu, hv] at h
      exact (lt_asymm h heo)
  · obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp hvu
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨hne, Or.inr hmem⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · have h := horder (v, u) hmem
      have heo := horder e he
      simp only [hu, hv] at h
      exact (lt_asymm h heo)
    · exact hneq (Prod.ext hv hu)

/-- The endpoints of a forest edge belong to different components after it
is erased. -/
theorem forest_cut_not_reachable (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) (hforest : (edgeGraph E).IsAcyclic)
    (he : e ∈ E) : ¬(edgeGraph (E.erase e)).Reachable e.1 e.2 := by
  have hadj : (edgeGraph E).Adj e.1 e.2 := ⟨ne_of_lt (horder e he), Or.inl he⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hforest) hadj
  intro hr
  exact hb (hr.mono (edgeGraph_erase_le_delete E e horder he))

/-- No remaining edge crosses the component cut, so its kernel depends only
on the coordinates of one branch. -/
theorem forest_cut_closed (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) :
    ∀ p ∈ E.erase e,
      (edgeGraph (E.erase e)).Reachable e.1 p.1 ↔
        (edgeGraph (E.erase e)).Reachable e.1 p.2 := by
  intro p hp
  have hpE := (Finset.mem_erase.mp hp).2
  have hr : (edgeGraph (E.erase e)).Reachable p.1 p.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (horder p hpE), Or.inl hp⟩
  exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

end ForestCuts

end FiniteWeightedForest

end

-- Solutions.WeldedPathForestFactorization
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest

variable {n : ℕ}

noncomputable def componentEdges (H : AbsForest n) (s : Fin H.k) :
    Finset (Fin H.k × Fin H.k) := by
  classical
  exact H.E.filter (fun p => p.1 ∈ H.comp s)

noncomputable def componentKernel (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (p : Fin H.k × Fin H.k) (x y : Label n) : ℝ :=
  kappa l G (H.color p) x.val y.val

def componentAllowed (l : ℕ) (H : AbsForest n) (s u : Fin H.k) (x : Label n) : Prop :=
  u ∈ H.comp s → x.val ∈ Vmid n l ∪ Vbd n l

/-- The assignment-independent prefactor in the canonical definition of
`muComp` for a component with at least one edge. -/
noncomputable def componentScale (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) : ℝ := by
  classical
  let V := Vmid n l ∪ Vbd n l
  let Z := (1 / (V.card : ℝ)) *
    ∑ ψ ∈ Finset.univ.filter (fun ψ : Fin H.k → Label n =>
      (∀ u ∈ H.comp s, (ψ u).val ∈ V) ∧ (∀ u, u ∉ H.comp s → ψ u = 0)),
        edgeWeight (componentEdges H s) (componentKernel l G H) ψ
  exact (1 / Z) * (1 / (V.card : ℝ))

/-- The canonical reference component measure is exactly a common scalar
times the edge-product law with its local vertex support restrictions. -/
theorem muComp_eq_scale_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ : Fin H.k → Label n) :
    H.muComp l G s φ = componentScale l G H s *
      forestWeight (componentEdges H s) (componentKernel l G H) (componentAllowed l H s) φ := by
  classical
  unfold AbsForest.muComp
  simp only [hsize, ite_false]
  unfold componentScale forestWeight componentAllowed componentEdges componentKernel edgeWeight
  simp only [mul_ite, mul_zero]

theorem componentScale_ne_zero (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ₀ : Fin H.k → Label n)
    (hμ : H.muComp l G s φ₀ ≠ 0) : componentScale l G H s ≠ 0 := by
  rw [muComp_eq_scale_forestWeight l G H s hsize φ₀] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

/-- Conditioning the reference component measure cancels its global
normalizer. The resulting finite law is precisely the conditioned supported
edge-product law. -/
theorem muComp_condition_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ₀ : Fin H.k → Label n)
    (hμ : H.muComp l G s φ₀ ≠ 0) (T : (Fin H.k → Label n) → Prop)
    [DecidablePred T] (φ : Fin H.k → Label n) :
    (if T φ then H.muComp l G s φ else 0) /
      (∑ ψ, if T ψ then H.muComp l G s ψ else 0) =
    (if T φ then forestWeight (componentEdges H s) (componentKernel l G H)
        (componentAllowed l H s) φ else 0) /
      (∑ ψ, if T ψ then forestWeight (componentEdges H s) (componentKernel l G H)
        (componentAllowed l H s) ψ else 0) := by
  have h (ψ : Fin H.k → Label n) :
      (if T ψ then H.muComp l G s ψ else 0) =
      componentScale l G H s *
        (if T ψ then forestWeight (componentEdges H s) (componentKernel l G H)
          (componentAllowed l H s) ψ else 0) := by
    rw [muComp_eq_scale_forestWeight l G H s hsize ψ]
    split_ifs <;> simp
  simp_rw [h]
  exact normalize_scale (fun ψ => if T ψ then
    forestWeight (componentEdges H s) (componentKernel l G H) (componentAllowed l H s) ψ else 0)
    _ (componentScale_ne_zero l G H s hsize φ₀ hμ) φ

theorem componentEdges_ordered (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    ∀ p ∈ componentEdges H s, p.1 < p.2 := by
  classical
  intro p hp
  exact hH.1 p (Finset.mem_filter.mp hp).1

theorem componentEdges_acyclic (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    (edgeGraph (componentEdges H s)).IsAcyclic := by
  apply hH.2.1.anti
  intro u v h
  rcases h with ⟨hne, h | h⟩
  · exact ⟨hne, Or.inl (Finset.mem_filter.mp h).1⟩
  · exact ⟨hne, Or.inr (Finset.mem_filter.mp h).1⟩

theorem component_card_ne_one_of_edge (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) : (H.comp s).card ≠ 1 := by
  classical
  obtain ⟨heE, he₁⟩ := Finset.mem_filter.mp he
  have hr : H.graph.Reachable e.1 e.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 e heE), Or.inl heE⟩
  have he₂ : e.2 ∈ H.comp s := by
    simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ ⊢
    exact he₁.trans hr
  intro hsize
  exact (ne_of_lt (hH.1 e heE)) ((Finset.card_le_one.mp hsize.le) e.1 he₁ e.2 he₂)

def componentCut (H : AbsForest n) (s : Fin H.k) (e : Fin H.k × Fin H.k)
    (u : Fin H.k) : Prop := (edgeGraph ((componentEdges H s).erase e)).Reachable e.1 u

/-- Every forest edge supplies a genuine separator for the factorization
theorems, with no additional graph assumption left to discharge. -/
theorem componentCut_spec (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) :
    componentCut H s e e.1 ∧ ¬componentCut H s e e.2 ∧
      ∀ p ∈ (componentEdges H s).erase e,
        componentCut H s e p.1 ↔ componentCut H s e p.2 := by
  refine ⟨SimpleGraph.Reachable.refl _, ?_, ?_⟩
  · exact forest_cut_not_reachable _ _ (componentEdges_ordered H hH s)
      (componentEdges_acyclic H hH s) he
  · exact forest_cut_closed _ _ (componentEdges_ordered H hH s)

/-- Unnormalized branch factorization of the actual canonical `muComp`.
Together with `muComp_condition_eq_forestWeight` and
`supported_tree_bridge_conditional_factor`, this gives its exact normalized
endpoint-conditioned independence law. -/
theorem muComp_bridge_factor (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (e : Fin H.k × Fin H.k)
    (he : e ∈ componentEdges H s) (φ : Fin H.k → Label n) :
    let P := componentCut H s e
    letI : DecidablePred P := Classical.decPred P
    H.muComp l G s φ = componentScale l G H s *
      (supportedBranchWeight ((componentEdges H s).erase e) P
        (componentKernel l G H) (componentAllowed l H s) (fun v => φ v) *
      supportedBranchWeight ((componentEdges H s).erase e) (fun v => ¬P v)
        (componentKernel l G H) (componentAllowed l H s) (fun v => φ v) *
      kappa l G (H.color e) (φ e.1).val (φ e.2).val) := by
  classical
  dsimp only
  rw [muComp_eq_scale_forestWeight l G H s (component_card_ne_one_of_edge H hH s e he) φ]
  congr 1
  exact forestWeight_bridge_branches _ _ _ _ _ _ he (componentCut_spec H hH s e he).2.2

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathComponentProcess
section

namespace WeldedPath.Supplement.ComponentProcess

open scoped BigOperators
open Classical FiniteWeightedForest ForestOrder ForestFactorization KappaForest

variable {n : ℕ} (H : AbsForest n) (φ₀ : Fin H.k → Label n) (s : Fin H.k)

noncomputable abbrev stages := Fintype.card ↥(freeVertices H φ₀ s)

variable (C : ParentOrder H φ₀ s)

noncomputable def processParent (i : ℕ) : Option (Fin i) :=
  if hi : i < stages H φ₀ s then C.parent ⟨i, hi⟩ else none

noncomputable def processRoot (i : ℕ) : Label n :=
  if hi : i < stages H φ₀ s then φ₀ (C.fixed ⟨i, hi⟩) else 0

noncomputable def processColor (i : ℕ) : Fin 3 :=
  if hi : i < stages H φ₀ s then H.color (C.edge ⟨i, hi⟩).val else 0

noncomputable def processKernel (l : ℕ) (G : WeldedInstance n) :=
  forestKernel l G (processParent H φ₀ s C) (processRoot H φ₀ s C)
    (processColor H φ₀ s C)

lemma process_root_weld (i : ℕ) (hi : i < stages H φ₀ s)
    (hp : processParent H φ₀ s C i = none) :
    (processRoot H φ₀ s C i).val ∈ Vweld n := by
  simp only [processParent, dif_pos hi] at hp
  simpa only [processRoot, dif_pos hi] using C.fixed_weld ⟨i, hi⟩ hp

lemma free_edge_weight_eq_process (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (φ : Fin H.k → Label n) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    edgeWeight (freeEdges H φ₀ s) (componentKernel l G H) φ =
      prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
        (fun i => φ (C.order i).val) := by
  apply edgeWeight_eq_prefixLaw (freeEdges H φ₀ s) (componentKernel l G H)
    (fun _ _ x y => KappaKernel.kappa_symm hG _ _ _)
    C.edge (parentVertex H (fun i => (C.order i).val) C.fixed C.parent)
    (fun i => (C.order i).val) (fun i => (C.edge_endpoints i).symm)
  intro i
  unfold processKernel forestKernel processParent processRoot processColor
  simp only [dif_pos i.isLt, componentKernel]
  cases hp : C.parent i with
  | none =>
    simp only [hp, parentVertex, hφ _ (C.fixed_mem i hp)]
  | some j =>
    simp only [hp, parentVertex, before]

noncomputable def fixedEdges : Finset (Fin H.k × Fin H.k) :=
  (componentEdges H s).filter (fun e => e.1 ∈ H.Sfix φ₀ s ∧ e.2 ∈ H.Sfix φ₀ s)

lemma component_nonfixed_edges :
    (componentEdges H s).filter (fun e => ¬(e.1 ∈ H.Sfix φ₀ s ∧ e.2 ∈ H.Sfix φ₀ s)) =
      freeEdges H φ₀ s := by
  ext e
  simp only [componentEdges, freeEdges, Finset.mem_filter, and_assoc]

lemma component_edge_weight_split (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (φ : Fin H.k → Label n) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    edgeWeight (componentEdges H s) (componentKernel l G H) φ =
      edgeWeight (fixedEdges H φ₀ s) (componentKernel l G H) φ₀ *
        prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
          (fun i => φ (C.order i).val) := by
  rw [edgeWeight_fixed_split _ (H.Sfix φ₀ s) _ _ φ₀ hφ,
    component_nonfixed_edges H φ₀ s,
    free_edge_weight_eq_process H φ₀ s C l G hG φ hφ]
  rfl

lemma reference_region (l : ℕ) (G : WeldedInstance n)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muComp l G s φ₀ ≠ 0) :
    ∀ u ∈ H.comp s, (φ₀ u).val ∈ Vmid n l ∪ Vbd n l := by
  intro u hu
  rw [muComp_eq_scale_forestWeight l G H s hsize φ₀] at hμ
  have hw := (mul_ne_zero_iff.mp hμ).2
  unfold forestWeight at hw
  split_ifs at hw with ha
  · exact ha u hu
  · exact (hw rfl).elim

lemma process_support (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (z : Fin (stages H φ₀ s) → Label n)
    (hz : prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s) z ≠ 0) :
    ∀ i, (z i).val ∈ Vmid n l ∪ Vbd n l := by
  exact prefixLaw_support (processKernel H φ₀ s C l G)
    (fun y : Label n => y.val ∈ Vmid n l ∪ Vbd n l)
    (fun _ _ _ hy => KappaWalk.kappa_output_region hG hy) _ z hz

noncomputable def processScale (l : ℕ) (G : WeldedInstance n) : ℝ :=
  componentScale l G H s * edgeWeight (fixedEdges H φ₀ s) (componentKernel l G H) φ₀

lemma muComp_eq_process_on_fixed (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muComp l G s φ₀ ≠ 0)
    (φ : Fin H.k → Label n) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    H.muComp l G s φ = processScale H φ₀ s l G *
      prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
        (fun i => φ (C.order i).val) := by
  rw [muComp_eq_scale_forestWeight l G H s hsize φ]
  have he := component_edge_weight_split H φ₀ s C l G hG φ hφ
  unfold forestWeight
  split_ifs with ha
  · rw [he]
    exact (mul_assoc _ _ _).symm
  · have hz : prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
        (fun i => φ (C.order i).val) = 0 := by
      by_contra hnz
      apply ha
      intro u hu
      by_cases hf : u ∈ H.Sfix φ₀ s
      · rw [hφ u hf]
        exact reference_region H φ₀ s l G hsize hμ u hu
      · let v : freeVertices H φ₀ s := ⟨u, Finset.mem_sdiff.mpr ⟨hu, hf⟩⟩
        have h := process_support H φ₀ s C l G hG _ hnz (C.order.symm v)
        simpa only [Equiv.apply_symm_apply] using h
    simp only [hz, mul_zero]

include C in
lemma processScale_ne_zero (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muComp l G s φ₀ ≠ 0) :
    processScale H φ₀ s l G ≠ 0 := by
  rw [muComp_eq_process_on_fixed H φ₀ s C l G hG hsize hμ φ₀ (fun _ _ => rfl)] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

noncomputable def freeComplementEquiv (hconn : H.comp s = Finset.univ) :
    freeVertices H φ₀ s ≃ {u : Fin H.k // u ∉ H.Sfix φ₀ s} where
  toFun v := ⟨v.val, (free_vertex_spec H φ₀ s v).2⟩
  invFun v := ⟨v.val, Finset.mem_sdiff.mpr ⟨by rw [hconn]; exact Finset.mem_univ _, v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def coordinateEquiv (hconn : H.comp s = Finset.univ) :
    ({u : Fin H.k // u ∉ H.Sfix φ₀ s} → Label n) ≃ (Fin (stages H φ₀ s) → Label n) :=
  Equiv.arrowCongr (C.order.trans (freeComplementEquiv H φ₀ s hconn)).symm (Equiv.refl _)

lemma sum_fixed_coordinates (hconn : H.comp s = Finset.univ)
    (f : (Fin (stages H φ₀ s) → Label n) → ℝ) :
    (∑ φ : Fin H.k → Label n, if ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u then
      f (fun i => φ (C.order i).val) else 0) = ∑ z, f z := by
  have hh := sum_fixed_restrictions (H.Sfix φ₀ s) φ₀
    (fun z => f (coordinateEquiv H φ₀ s C hconn z))
  calc
    _ = ∑ z, f (coordinateEquiv H φ₀ s C hconn z) := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro φ _
      split_ifs <;> rfl
    _ = _ := Equiv.sum_comp (coordinateEquiv H φ₀ s C hconn) f

lemma free_avoid_iff_order (hconn : H.comp s = Finset.univ)
    (B : Finset ℕ) (φ : Fin H.k → Label n) :
    (∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B) ↔
      ∀ i, (φ (C.order i).val).val ∉ B := by
  constructor
  · intro h i
    exact h _ (free_vertex_spec H φ₀ s (C.order i)).2
  · intro h u hu
    let v : freeVertices H φ₀ s :=
      ⟨u, Finset.mem_sdiff.mpr ⟨by rw [hconn]; exact Finset.mem_univ _, hu⟩⟩
    have hh := h (C.order.symm v)
    simpa only [Equiv.apply_symm_apply] using hh

noncomputable def fixedAvoidWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (φ : Fin H.k → Label n) : ℝ :=
  if (∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) ∧
    (∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B) then H.muComp l G s φ else 0

noncomputable def maskedLaw (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) :=
  prefixLaw (maskKernel (processKernel H φ₀ s C l G) (labelBoundary n B))
    (stages H φ₀ s)

lemma fixedAvoidWeight_eq_process (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hconn : H.comp s = Finset.univ) (hsize : (H.comp s).card ≠ 1)
    (hμ : H.muComp l G s φ₀ ≠ 0) (B : Finset ℕ) (φ : Fin H.k → Label n) :
    fixedAvoidWeight H φ₀ s l G B φ =
      if ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u then processScale H φ₀ s l G *
        maskedLaw H φ₀ s C l G B (fun i => φ (C.order i).val) else 0 := by
  have hm : maskedLaw H φ₀ s C l G B (fun i => φ (C.order i).val) =
      if ∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B then
        prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
          (fun i => φ (C.order i).val) else 0 := by
    unfold maskedLaw
    rw [masked_prefixLaw_eq]
    simp only [labelBoundary, Finset.mem_filter, Finset.mem_univ, true_and,
      free_avoid_iff_order H φ₀ s C hconn B φ]
  by_cases ha : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u
  · rw [if_pos ha, hm]
    unfold fixedAvoidWeight
    by_cases hb : ∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B
    · rw [if_pos ⟨ha, hb⟩, if_pos hb]
      exact muComp_eq_process_on_fixed H φ₀ s C l G hG hsize hμ φ ha
    · simp only [ha, hb, and_false, if_false, mul_zero]
  · simp only [fixedAvoidWeight, ha, false_and, if_false]

lemma conditional_event_eq_process (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hconn : H.comp s = Finset.univ) (hsize : (H.comp s).card ≠ 1)
    (hμ : H.muComp l G s φ₀ ≠ 0) (B : Finset ℕ)
    (event : (Fin (stages H φ₀ s) → Label n) → Prop) :
    (∑ φ : Fin H.k → Label n, if event (fun i => φ (C.order i).val) then
      fixedAvoidWeight H φ₀ s l G B φ else 0) /
      (∑ φ, fixedAvoidWeight H φ₀ s l G B φ) =
    (∑ z, if event z then maskedLaw H φ₀ s C l G B z else 0) /
      (∑ z, maskedLaw H φ₀ s C l G B z) := by
  classical
  let c := processScale H φ₀ s l G
  let L := maskedLaw H φ₀ s C l G B
  have hc : c ≠ 0 := processScale_ne_zero H φ₀ s C l G hG hsize hμ
  have hden : (∑ φ, fixedAvoidWeight H φ₀ s l G B φ) = c * ∑ z, L z := by
    simp_rw [fixedAvoidWeight_eq_process H φ₀ s C l G hG hconn hsize hμ B]
    rw [sum_fixed_coordinates H φ₀ s C hconn (fun z => c * L z), Finset.mul_sum]
  have he (φ : Fin H.k → Label n) :
      (if event (fun i => φ (C.order i).val) then fixedAvoidWeight H φ₀ s l G B φ else 0) =
      if ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u then
        c * (if event (fun i => φ (C.order i).val) then L (fun i => φ (C.order i).val) else 0)
      else 0 := by
    rw [fixedAvoidWeight_eq_process H φ₀ s C l G hG hconn hsize hμ B φ]
    split_ifs <;> simp_all [c, L]
  simp_rw [he]
  rw [sum_fixed_coordinates H φ₀ s C hconn
    (fun z => c * (if event z then L z else 0)), ← Finset.mul_sum, hden]
  exact mul_div_mul_left _ _ hc

end WeldedPath.Supplement.ComponentProcess

end

-- Solutions.WeldedPathReciprocalClasses
section

namespace WeldedPath.Supplement.ReciprocalClasses

open scoped BigOperators
open Classical KappaKernel

variable {n l : ℕ} (G : WeldedInstance n)

/-- The reciprocal class size at the first edge, zero for an undefined transition. -/
noncomputable def firstEdgeCap (α : Fin 3) (u : ℕ) : ℝ :=
  match permData l G u α with
  | none => 0
  | some ⟨b, _, _⟩ => 1 / (classSize l G b : ℝ)

theorem firstEdgeCap_nonneg (α : Fin 3) (u : ℕ) : 0 ≤ firstEdgeCap (l := l) G α u := by
  unfold firstEdgeCap
  split <;> positivity

theorem kappa_le_firstEdgeCap (α : Fin 3) (u v : ℕ) :
    kappa l G α u v ≤ firstEdgeCap (l := l) G α u := by
  cases hpd : permData l G u α with
  | none => simp [kappa, firstEdgeCap, hpd]
  | some d =>
    obtain ⟨b, e, t⟩ := d
    simpa only [firstEdgeCap, hpd] using kappa_le_inv_classSize hpd v

noncomputable def endpointCap (b : PClass n l) (u : ℕ) : ℝ :=
  if u ∈ (G.classEdges l b.1).image Edge.tail ∨
      u ∈ (G.classEdges l b.1).image (Edge.head n) then
    1 / (classSize l G b : ℝ) else 0

theorem firstEdgeCap_le_endpoint_sum (α : Fin 3) (u : ℕ) :
    firstEdgeCap (l := l) G α u ≤ ∑ b : PClass n l, endpointCap G b u := by
  cases hpd : permData l G u α with
  | none =>
    simp only [firstEdgeCap, hpd]
    apply Finset.sum_nonneg
    intro b _
    unfold endpointCap
    split_ifs <;> positivity
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hi := (eAlpha_spec (permData_eAlpha hpd)).2.2
    have hm : u ∈ (G.classEdges l b.1).image Edge.tail ∨
        u ∈ (G.classEdges l b.1).image (Edge.head n) := by
      rcases hi with hi | hi
      · exact Or.inl (Finset.mem_image.mpr ⟨e.1, e.2, hi.symm⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨e.1, e.2, hi.symm⟩)
    have he : firstEdgeCap (l := l) G α u = endpointCap G b u := by
      simp only [firstEdgeCap, hpd, endpointCap, if_pos hm]
    rw [he]
    apply Finset.single_le_sum _ (Finset.mem_univ b)
    intro c _
    unfold endpointCap
    split_ifs <;> positivity

theorem endpointCap_sum_le_two (b : PClass n l) :
    (∑ u : Label n, endpointCap G b u.1) ≤ 2 := by
  have htail := sum_uniform_finset_le_one (X := Label n) Fin.val Fin.val_injective
    ((G.classEdges l b.1).image Edge.tail) (classSize l G b) Finset.card_image_le
  have hhead := sum_uniform_finset_le_one (X := Label n) Fin.val Fin.val_injective
    ((G.classEdges l b.1).image (Edge.head n)) (classSize l G b) Finset.card_image_le
  calc
    _ ≤ ∑ u : Label n,
        ((if u.1 ∈ (G.classEdges l b.1).image Edge.tail then
          1 / (classSize l G b : ℝ) else 0) +
        (if u.1 ∈ (G.classEdges l b.1).image (Edge.head n) then
          1 / (classSize l G b : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      unfold endpointCap
      split_ifs <;> simp_all <;> positivity
    _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith

theorem class_count_le (hln : l ≤ n) : (BEdge n l).card ≤ 6 * (n + 1) := by
  unfold BEdge
  have h₁ := Finset.card_image_le (s :=
    (Finset.Icc (n - l) (n + l)) ×ˢ (Finset.univ : Finset (Fin 3)))
    (f := fun p => EdgeClass.tr p.1 p.2)
  have h₂ := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)))
    (f := EdgeClass.wld)
  have h₃ := Finset.card_union_le
    (((Finset.Icc (n - l) (n + l)) ×ˢ (Finset.univ : Finset (Fin 3))).image
      (fun p => EdgeClass.tr p.1 p.2))
    ((Finset.univ : Finset (Fin 3)).image EdgeClass.wld)
  simp only [Finset.card_product, Nat.card_Icc, Finset.card_univ, Fintype.card_fin] at h₁ h₂
  omega

/-- Summing reciprocal class sizes costs only the number of columns: each
class is charged at most once by its tails and once by its heads. -/
theorem firstEdgeCap_sum_le (hln : l ≤ n) (α : Fin 3) :
    (∑ u : Label n, firstEdgeCap (l := l) G α u.1) ≤ 12 * ((n : ℝ) + 1) := by
  calc
    _ ≤ ∑ u : Label n, ∑ b : PClass n l, endpointCap G b u.1 :=
      Finset.sum_le_sum fun u _ => firstEdgeCap_le_endpoint_sum G α u.1
    _ = ∑ b : PClass n l, ∑ u : Label n, endpointCap G b u.1 := Finset.sum_comm
    _ ≤ ∑ b : PClass n l, (2 : ℝ) :=
      Finset.sum_le_sum fun b _ => endpointCap_sum_le_two G b
    _ = (Fintype.card (PClass n l) : ℝ) * 2 := by simp
    _ ≤ (6 * ((n : ℝ) + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h := class_count_le hln
      simpa only [PClass, Fintype.card_coe, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_one] using (Nat.cast_le.mpr h : ((BEdge n l).card : ℝ) ≤ (6 * (n + 1) : ℕ))
    _ = _ := by ring

/-- This is the class-counting part of the lowest-common-ancestor collision
estimate: a parent with point mass at most M pays only O(n) M in total. -/
theorem expected_firstEdgeCap_le (hln : l ≤ n) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ u, p u ≤ M) :
    (∑ u, p u * firstEdgeCap (l := l) G α u.1) ≤ 12 * ((n : ℝ) + 1) * M := by
  calc
    _ ≤ ∑ u, M * firstEdgeCap (l := l) G α u.1 := Finset.sum_le_sum
      fun u _ => mul_le_mul_of_nonneg_right (hp u) (firstEdgeCap_nonneg G α u.1)
    _ = M * ∑ u : Label n, firstEdgeCap (l := l) G α u.1 := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (12 * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left (firstEdgeCap_sum_le G hln α) hM
    _ = _ := by ring

end WeldedPath.Supplement.ReciprocalClasses

end

-- Solutions.WeldedPathBranchCollision
section

namespace WeldedPath.Supplement.BranchCollision

open scoped BigOperators
open Classical KappaKernel KappaWalk ReciprocalClasses

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def pointMass (u : Label n) : Label n → ℝ := fun y => if y = u then 1 else 0

theorem pointMass_nonneg (u y : Label n) : 0 ≤ pointMass u y := by
  unfold pointMass
  split_ifs <;> positivity

theorem pointMass_sum (u : Label n) : (∑ y, pointMass u y) = 1 := by
  simp [pointMass]

theorem step_pointMass (α : Fin 3) (u y : Label n) :
    step l G α (pointMass u) y = kappa l G α u.1 y.1 := by
  simp [step, pointMass]

/-- The walk is linear in its initial law, written in the point-mass basis. -/
theorem walk_matrix (cs : List (Fin 3)) (p : Label n → ℝ) (y : Label n) :
    walk l G cs p y = ∑ u, p u * walk l G cs (pointMass u) y := by
  induction cs generalizing p with
  | nil => simp [walk, pointMass]
  | cons α cs ih =>
    have hc (u : Label n) : walk l G (α :: cs) (pointMass u) y =
        ∑ x, kappa l G α u.1 x.1 * walk l G cs (pointMass x) y := by
      rw [walk, ih]
      simp_rw [step_pointMass]
    rw [walk, ih]
    simp only [step, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

theorem walk_cons_matrix (α : Fin 3) (cs : List (Fin 3)) (u y : Label n) :
    walk l G (α :: cs) (pointMass u) y =
      ∑ x, kappa l G α u.1 x.1 * walk l G cs (pointMass x) y := by
  rw [walk, walk_matrix]
  simp_rw [step_pointMass]

noncomputable def meet (cs ds : List (Fin 3)) (u v : Label n) : ℝ :=
  ∑ y, walk l G cs (pointMass u) y * walk l G ds (pointMass v) y

theorem meet_nonneg (cs ds : List (Fin 3)) (u v : Label n) :
    0 ≤ meet (l := l) (G := G) cs ds u v := by
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (walk_nonneg l G cs _ (pointMass_nonneg u) y)
    (walk_nonneg l G ds _ (pointMass_nonneg v) y)

theorem meet_symm (cs ds : List (Fin 3)) (u v : Label n) :
    meet (l := l) (G := G) cs ds u v = meet (l := l) (G := G) ds cs v u := by
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

theorem meet_cons_left (α : Fin 3) (cs ds : List (Fin 3)) (u v : Label n) :
    meet (l := l) (G := G) (α :: cs) ds u v =
      ∑ x, kappa l G α u.1 x.1 * meet (l := l) (G := G) cs ds x v := by
  unfold meet
  simp_rw [walk_cons_matrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem meet_cons_right (α : Fin 3) (cs ds : List (Fin 3)) (u v : Label n) :
    meet (l := l) (G := G) cs (α :: ds) u v =
      ∑ x, kappa l G α v.1 x.1 * meet (l := l) (G := G) cs ds u x := by
  rw [meet_symm, meet_cons_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [meet_symm ds cs x u]

theorem meet_nil_nil (u v : Label n) :
    meet (l := l) (G := G) [] [] u v = if u = v then 1 else 0 := by
  simp [meet, walk, pointMass, eq_comm]

theorem meet_from_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (α : Fin 3) (cs ds : List (Fin 3)) (u v : Label n) (hu : u.1 ∈ Vweld n) :
    meet (l := l) (G := G) (α :: cs) ds u v ≤ 4 / (2 : ℝ) ^ n := by
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hc : ∀ y, walk l G (α :: cs) (pointMass u) y ≤ 4 / (2 : ℝ) ^ n := by
    apply walk_point_bound hG cs (step l G α (pointMass u)) _ hM
    intro y
    rw [step_pointMass]
    exact FirstFreeStep.kappa_from_weld_le hG hn hl hu α y.1
  calc
    _ ≤ ∑ y, (4 / (2 : ℝ) ^ n) * walk l G ds (pointMass v) y := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (hc y) (walk_nonneg l G ds _ (pointMass_nonneg v) y)
    _ = (4 / (2 : ℝ) ^ n) * ∑ y, walk l G ds (pointMass v) y := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 / (2 : ℝ) ^ n) * 1 := by
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only [pointMass_sum] using walk_mass_le l G ds _ (pointMass_nonneg v)
    _ = _ := mul_one _

/-- After the first edge, every further symmetric substochastic transition
preserves the reciprocal-class point bound. -/
theorem walk_firstEdgeCap (hG : G.IsValid) (α : Fin 3) (cs : List (Fin 3))
    (u y : Label n) :
    walk l G (α :: cs) (pointMass u) y ≤ firstEdgeCap (l := l) G α u.1 := by
  apply walk_point_bound hG cs (step l G α (pointMass u)) _
    (firstEdgeCap_nonneg G α u.1) _ y
  intro z
  rw [step_pointMass]
  exact kappa_le_firstEdgeCap G α u.1 z.1

/-- The coincidence mass of two independent branches from one parent is
bounded by the reciprocal class size of either nonempty branch's first edge. -/
theorem two_branch_collision_le (hG : G.IsValid) (α : Fin 3)
    (cs ds : List (Fin 3)) (u : Label n) :
    (∑ y, walk l G (α :: cs) (pointMass u) y *
      walk l G ds (pointMass u) y) ≤ firstEdgeCap (l := l) G α u.1 := by
  calc
    _ ≤ ∑ y, firstEdgeCap (l := l) G α u.1 * walk l G ds (pointMass u) y := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (walk_firstEdgeCap hG α cs u y)
        (walk_nonneg l G ds (pointMass u) (pointMass_nonneg u) y)
    _ = firstEdgeCap (l := l) G α u.1 * ∑ y, walk l G ds (pointMass u) y :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ firstEdgeCap (l := l) G α u.1 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (firstEdgeCap_nonneg G α u.1)
      simpa only [pointMass_sum] using
        walk_mass_le l G ds (pointMass u) (pointMass_nonneg u)
    _ = _ := mul_one _

/-- Averaging over a free lowest common ancestor costs O(n) times its point
mass bound. Both branches may have arbitrary length; one may be empty. -/
theorem averaged_branch_collision_le (hG : G.IsValid) (hln : l ≤ n)
    (α : Fin 3) (cs ds : List (Fin 3)) (p : Label n → ℝ)
    (hp : ∀ u, 0 ≤ p u) (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ u, p u ≤ M) :
    (∑ u, p u * ∑ y, walk l G (α :: cs) (pointMass u) y *
      walk l G ds (pointMass u) y) ≤ 12 * ((n : ℝ) + 1) * M := by
  calc
    _ ≤ ∑ u, p u * firstEdgeCap (l := l) G α u.1 := Finset.sum_le_sum
      fun u _ => mul_le_mul_of_nonneg_left (two_branch_collision_le hG α cs ds u) (hp u)
    _ ≤ _ := expected_firstEdgeCap_le G hln α p M hM hcap

end WeldedPath.Supplement.BranchCollision

end

-- Solutions.WeldedPathForestCollision
section

namespace WeldedPath.Supplement.ForestCollision

open KappaForest KappaKernel KappaWalk BranchCollision
open scoped BigOperators

variable {X : Type*} [Fintype X] {m : ℕ}

noncomputable def pairExpectation (w : (Fin m → X) → ℝ) (a b : Fin m)
    (F : X → X → ℝ) : ℝ := ∑ z, w z * F (z a) (z b)

lemma pairExpectation_old_le (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i z y, 0 ≤ K i z y) (hrow : ∀ i z, ∑ y, K i z y ≤ 1)
    (m : ℕ) (a b : Fin m) (F : X → X → ℝ) (hF : ∀ x y, 0 ≤ F x y) :
    pairExpectation (prefixLaw K (m + 1)) a.castSucc b.castSucc F ≤
      pairExpectation (prefixLaw K m) a b F := by
  unfold pairExpectation
  rw [sum_snoc]
  simp only [prefixLaw_snoc, Fin.snoc_castSucc]
  apply Finset.sum_le_sum
  intro z _
  calc
    _ = (prefixLaw K m z * F (z a) (z b)) * ∑ y, K m z y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ (prefixLaw K m z * F (z a) (z b)) * 1 :=
      mul_le_mul_of_nonneg_left (hrow m z)
        (mul_nonneg (prefixLaw_nonneg K hK m z) (hF _ _))
    _ = _ := mul_one _

lemma pairExpectation_new (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (b : Fin m) (F : X → X → ℝ) :
    pairExpectation (prefixLaw K (m + 1)) (Fin.last m) b.castSucc F =
      ∑ z : Fin m → X, prefixLaw K m z * ∑ y, K m z y * F y (z b) := by
  unfold pairExpectation
  rw [sum_snoc]
  simp only [prefixLaw_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma pairExpectation_diagonal (w : (Fin m → X) → ℝ) (a : Fin m)
    (F : X → X → ℝ) :
    pairExpectation w a a F = ∑ x, marginal w a x * F x x :=
  marginal_pushforward w a (fun x => F x x)

lemma marginal_nonneg (w : (Fin m → X) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (j : Fin m) (x : X) : 0 ≤ marginal w j x := by
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact hw z
  · exact le_rfl

variable {n l : ℕ} {G : WeldedInstance n}

lemma pairExpectation_meet_symm (w : (Fin m → Label n) → ℝ) (a b : Fin m)
    (cs ds : List (Fin 3)) :
    pairExpectation w a b (meet (l := l) (G := G) cs ds) =
      pairExpectation w b a (meet (l := l) (G := G) ds cs) := by
  apply Finset.sum_congr rfl
  intro z _
  rw [meet_symm cs ds]

lemma pairExpectation_new_meet (K : (i : ℕ) → (Fin i → Label n) → Label n → ℝ)
    (m : ℕ) (b : Fin m) (α : Fin 3) (u : (Fin m → Label n) → Label n)
    (hK : ∀ z y, K m z y = kappa l G α (u z).1 y.1) (cs ds : List (Fin 3)) :
    pairExpectation (prefixLaw K (m + 1)) (Fin.last m) b.castSucc
        (meet (l := l) (G := G) cs ds) =
      ∑ z : Fin m → Label n, prefixLaw K m z * meet (l := l) (G := G) (α :: cs) ds (u z) (z b) := by
  rw [pairExpectation_new]
  simp_rw [hK, ← meet_cons_left]

lemma diagonal_meet_bound (hG : G.IsValid) (hln : l ≤ n)
    (w : (Fin m → Label n) → ℝ) (hw : ∀ z, 0 ≤ w z) (a : Fin m)
    (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ x, marginal w a x ≤ M)
    (cs ds : List (Fin 3)) (hne : cs ≠ [] ∨ ds ≠ []) :
    pairExpectation w a a (meet (l := l) (G := G) cs ds) ≤
      12 * ((n : ℝ) + 1) * M := by
  classical
  cases cs with
  | nil =>
    cases ds with
    | nil => simp at hne
    | cons α ds =>
      rw [pairExpectation_meet_symm, pairExpectation_diagonal]
      exact averaged_branch_collision_le hG hln α ds [] (marginal w a)
        (marginal_nonneg w hw a) M hM hcap
  | cons α cs =>
    rw [pairExpectation_diagonal]
    exact averaged_branch_collision_le hG hln α cs ds (marginal w a)
      (marginal_nonneg w hw a) M hM hcap

lemma forest_meet_bound (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l) (hln : l ≤ n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n) :
    ∀ (a b : Fin m) (cs ds : List (Fin 3)), a ≠ b ∨ cs ≠ [] ∨ ds ≠ [] →
      pairExpectation (prefixLaw (forestKernel l G parent root color) m) a b
          (meet (l := l) (G := G) cs ds) ≤
        12 * ((n : ℝ) + 1) * (4 / (2 : ℝ) ^ n) := by
  classical
  let K := forestKernel l G parent root color
  have hK : ∀ i z y, 0 ≤ K i z y := forestKernel_nonneg l G parent root color
  have hrow : ∀ i z, ∑ y, K i z y ≤ 1 := forestKernel_row_le l G parent root color
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hCM : 4 / (2 : ℝ) ^ n ≤ 12 * ((n : ℝ) + 1) * (4 / (2 : ℝ) ^ n) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  induction m with
  | zero => intro a; exact Fin.elim0 a
  | succ m ih =>
    have hr : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n :=
      fun i hi => hroot i (by omega)
    intro a b cs ds hne
    by_cases hab : a = b
    · subst b
      apply diagonal_meet_bound hG hln _ (prefixLaw_nonneg K hK (m + 1)) a _ hM
        (fun x => forestLaw_marginal_cap hG hn hl parent root color (m + 1) hroot a x) cs ds
      exact hne.resolve_left (not_not.mpr rfl)
    · have hnew : ∀ (b : Fin m) (cs ds : List (Fin 3)),
          pairExpectation (prefixLaw K (m + 1)) (Fin.last m) b.castSucc
              (meet (l := l) (G := G) cs ds) ≤
            12 * ((n : ℝ) + 1) * (4 / (2 : ℝ) ^ n) := by
        intro b cs ds
        cases hpar : parent m with
        | none =>
          rw [pairExpectation_new_meet K m b (color m) (fun _ => root m)
            (fun z y => by simp only [K, forestKernel, hpar]) cs ds]
          calc
            _ ≤ ∑ z, prefixLaw K m z * (4 / (2 : ℝ) ^ n) := by
              apply Finset.sum_le_sum
              intro z _
              exact mul_le_mul_of_nonneg_left
                (meet_from_weld_le hG hn hl (color m) cs ds (root m) (z b)
                  (hroot m (Nat.lt_succ_self m) hpar)) (prefixLaw_nonneg K hK m z)
            _ = (∑ z, prefixLaw K m z) * (4 / (2 : ℝ) ^ n) :=
              (Finset.sum_mul _ _ _).symm
            _ ≤ 1 * (4 / (2 : ℝ) ^ n) := mul_le_mul_of_nonneg_right
              (prefixLaw_mass_le_one K hK hrow m) hM
            _ ≤ _ := by simpa only [one_mul] using hCM
        | some p =>
          rw [pairExpectation_new_meet K m b (color m) (fun z => z p)
            (fun z y => by simp only [K, forestKernel, hpar]) cs ds]
          exact ih hr p b (color m :: cs) ds (Or.inr (Or.inl (by simp)))
      by_cases ha : a = Fin.last m
      · subst a
        have hb : b ≠ Fin.last m := Ne.symm hab
        obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hb
        exact hnew b' cs ds
      · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha
        by_cases hb : b = Fin.last m
        · subst b
          rw [pairExpectation_meet_symm]
          exact hnew a' ds cs
        · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hb
          apply (pairExpectation_old_le K hK hrow m a' b'
            (meet (l := l) (G := G) cs ds) (meet_nonneg cs ds)).trans
          apply ih hr a' b' cs ds
          exact Or.inl (fun h => hab (congrArg Fin.castSucc h))

open Classical in
noncomputable def coincidence (w : (Fin m → X) → ℝ) (a b : Fin m) : ℝ :=
  ∑ z, if z a = z b then w z else 0

lemma coincidence_mono (w v : (Fin m → X) → ℝ) (h : ∀ z, w z ≤ v z)
    (a b : Fin m) : coincidence w a b ≤ coincidence v a b := by
  classical
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact h z
  · exact le_rfl

lemma coincidence_eq_meet (w : (Fin m → Label n) → ℝ) (a b : Fin m) :
    coincidence w a b = pairExpectation w a b (meet (l := l) (G := G) [] []) := by
  classical
  simp only [coincidence, pairExpectation, meet_nil_nil, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

lemma forestLaw_collision_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l) (hln : l ≤ n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (a b : Fin m) (hab : a ≠ b) :
    coincidence (prefixLaw (forestKernel l G parent root color) m) a b ≤
      48 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  rw [coincidence_eq_meet (l := l) (G := G)]
  have hh := forest_meet_bound hG hn hl hln parent root color m hroot a b [] [] (Or.inl hab)
  convert hh using 1 <;> first | rfl | ring

lemma forestLaw_conditioned_collision_le (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (hsmall : (m : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (a b : Fin m) (hab : a ≠ b) :
    coincidence (prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m) a b /
      (∑ z, prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m z)
        ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  let K := forestKernel l G parent root color
  let C := labelBoundary n B
  have hs := forestLaw_survival hG hn hl hln parent root color m hroot B hB
  have hz : (1 / 2 : ℝ) ≤ ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hzpos : 0 < ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hle := coincidence_mono _ _
    (masked_prefixLaw_le K C (forestKernel_nonneg l G parent root color) m) a b
  have hcap := forestLaw_collision_le (l := l) hG (by omega) (by omega) (by omega)
    parent root color m hroot a b hab
  apply (div_le_iff₀ hzpos).mpr
  calc
    _ ≤ 48 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := hle.trans hcap
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hz
        (by positivity : 0 ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n)
      convert hh using 1 <;> first | rfl | ring

end WeldedPath.Supplement.ForestCollision

end

-- Solutions.WeldedPathConnectedConcentration
section

namespace WeldedPath.Supplement.ConnectedConcentration

open Classical ConnectedReference FixedAvoidance ForestOrder ComponentProcess KappaForest ForestCollision
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def sourceWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ) (φ : Fin H.k → Label n) : ℝ :=
  if H.Wfix φ s = H.Wfix φ₀ s ∧
      (∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).1 ∉ B)
  then H.muRef l G φ else 0

lemma sourceWeight_eq_fixedAvoidWeight (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (B : Finset ℕ) (hB : Disjoint B (Vweld n)) (φ : Fin H.k → Label n) :
    sourceWeight l G H φ₀ s B φ = fixedAvoidWeight H φ₀ s l G B φ := by
  unfold sourceWeight fixedAvoidWeight
  simp only [connected_fixed_avoidance_iff H hH φ φ₀ s hs B hB,
    muRef_eq_muComp H s hs φ]

lemma stages_le_vertices (H : AbsForest n) (φ₀ : Fin H.k → Label n) (s : Fin H.k) :
    stages H φ₀ s ≤ H.k := by
  have h := Fintype.card_le_of_injective
    (fun u : freeVertices H φ₀ s => u.val) Subtype.val_injective
  simpa only [stages, Fintype.card_fin] using h

lemma comp_card_ne_one_of_free (H : AbsForest n) (φ₀ : Fin H.k → Label n)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u) (u : Fin H.k)
    (hu : u ∉ H.Sfix φ₀ s) : (H.comp s).card ≠ 1 := by
  intro hc
  have hk : H.k = 1 := by
    simpa only [comp_eq_univ H s hs s, Finset.card_univ, Fintype.card_fin] using hc
  have hus : u = s := by
    apply Fin.ext
    have hi := u.isLt
    have hj := s.isLt
    omega
  subst u
  exact hu (FixedData.ctree_subset_sfix H φ₀ s (by simp [AbsForest.Ctree]))

lemma stages_budget (H : AbsForest n) (φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (B : Finset ℕ)
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2) :
    (stages H φ₀ s : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 := by
  have hk : (stages H φ₀ s : ℝ) ≤ H.k := by exact_mod_cast stages_le_vertices H φ₀ s
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hk (by positivity)) (by positivity)).trans hsmall

lemma conditional_source_event_eq_process (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (C : ParentOrder H φ₀ s) (hG : G.IsValid)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muRef l G φ₀ ≠ 0)
    (B : Finset ℕ) (hB : Disjoint B (Vweld n))
    (event : (Fin (stages H φ₀ s) → Label n) → Prop) :
    (∑ φ, if event (fun i => φ (C.order i).val) then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) =
    (∑ z, if event z then maskedLaw H φ₀ s C l G B z else 0) /
      (∑ z, maskedLaw H φ₀ s C l G B z) := by
  simp_rw [sourceWeight_eq_fixedAvoidWeight H hH φ₀ s hs B hB]
  exact conditional_event_eq_process H φ₀ s C l G hG (comp_eq_univ H s hs s) hsize
    (muComp_ne_zero_of_muRef_ne_zero H s hs φ₀ hμ) B event

theorem conditional_free_point_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (u : Fin H.k) (hu : u ∉ H.Sfix φ₀ s) (x : Label n) :
    (∑ φ, if φ u = x then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 8 / (2 : ℝ) ^ n := by
  obtain ⟨C⟩ := exists_parent_order H hH φ₀ s
  let v : freeVertices H φ₀ s := ⟨u, Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs u⟩, hu⟩⟩
  let j := C.order.symm v
  have he := conditional_source_event_eq_process H hH φ₀ s hs C hG
    (comp_card_ne_one_of_free H φ₀ s hs u hu) hμ B hBw (fun z => z j = x)
  have hb := forestLaw_conditioned_marginal_cap hG hn hl hln
    (processParent H φ₀ s C) (processRoot H φ₀ s C) (processColor H φ₀ s C)
    (stages H φ₀ s) (process_root_weld H φ₀ s C) B hB
    (stages_budget H φ₀ s B hsmall) j x
  have h := he.trans_le hb
  simpa only [j, Equiv.apply_symm_apply, v] using h

theorem conditional_free_pair_collision_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (u v : Fin H.k) (hu : u ∉ H.Sfix φ₀ s) (hv : v ∉ H.Sfix φ₀ s) (huv : u ≠ v) :
    (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  obtain ⟨C⟩ := exists_parent_order H hH φ₀ s
  let a : freeVertices H φ₀ s := ⟨u, Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs u⟩, hu⟩⟩
  let b : freeVertices H φ₀ s := ⟨v, Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs v⟩, hv⟩⟩
  let i := C.order.symm a
  let j := C.order.symm b
  have hij : i ≠ j := by
    intro h
    have hh := congrArg (fun k => (C.order k).val) h
    simp only [i, j, Equiv.apply_symm_apply] at hh
    exact huv hh
  have he := conditional_source_event_eq_process H hH φ₀ s hs C hG
    (comp_card_ne_one_of_free H φ₀ s hs u hu) hμ B hBw (fun z => z i = z j)
  have hb := forestLaw_conditioned_collision_le hG hn hl hln
    (processParent H φ₀ s C) (processRoot H φ₀ s C) (processColor H φ₀ s C)
    (stages H φ₀ s) (process_root_weld H φ₀ s C) B hB
    (stages_budget H φ₀ s B hsmall) i j hij
  have h := he.trans_le hb
  simpa only [i, j, Equiv.apply_symm_apply, a, b] using h

end WeldedPath.Supplement.ConnectedConcentration

end


open Classical WeldedPath WeldedPath.Supplement
open scoped BigOperators

theorem solution :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ H : AbsForest n, H.IsValid →
    ∀ (φ₀ : Fin H.k → Label n) (s : Fin H.k),
      (∀ u, H.graph.Reachable s u) → H.muRef l G φ₀ ≠ 0 →
    ∀ B : Finset ℕ, Vbd n l ⊆ B → Disjoint B (Vweld n) →
      (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 →
    let weight : (Fin H.k → Label n) → ℝ := fun φ =>
      if H.Wfix φ s = H.Wfix φ₀ s ∧
          (∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).1 ∉ B)
      then H.muRef l G φ else 0
    (∀ (u : Fin H.k), u ∉ H.Sfix φ₀ s → ∀ x : Label n,
      (∑ φ, if φ u = x then weight φ else 0) / (∑ φ, weight φ) ≤
        8 / (2 : ℝ) ^ n) ∧
    (∀ (u v : Fin H.k), u ∉ H.Sfix φ₀ s → v ∉ H.Sfix φ₀ s → u ≠ v →
      (∑ φ, if φ u = φ v then weight φ else 0) / (∑ φ, weight φ) ≤
        96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) := by
  intro n l hn hl hln G hG H hH φ₀ s hs hμ B hB hBw hsmall
  dsimp only
  constructor
  · intro u hu x
    exact ConnectedConcentration.conditional_free_point_bound H hH φ₀ s hs
      hG hn hl hln hμ B hB hBw hsmall u hu x
  · intro u v hu hv huv
    exact ConnectedConcentration.conditional_free_pair_collision_bound H hH φ₀ s hs
      hG hn hl hln hμ B hB hBw hsmall u v hu hv huv

