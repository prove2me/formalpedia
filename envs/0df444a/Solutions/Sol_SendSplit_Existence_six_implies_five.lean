-- Prove2me | solution 1 for SendSplit.Existence.six_implies_five
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:22:50.777584+00:00
-- url     : https://prove2.me/submissions/7d481635-3525-4759-9ea3-5c6e94417cc5

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

open SendSplit.Existence
open Fin.NatCast


namespace SSChainAux

variable {n : ℕ}

lemma cc_nil (w : Option (Fin n) → Option (Fin n) → EReal) : chainCost w [] = 0 := by
  simp [chainCost]

lemma cc_single (w : Option (Fin n) → Option (Fin n) → EReal) (a : Option (Fin n)) :
    chainCost w [a] = 0 := by
  simp [chainCost]

lemma cc_cons_cons (w : Option (Fin n) → Option (Fin n) → EReal) (a b : Option (Fin n))
    (l : List (Option (Fin n))) : chainCost w (a :: b :: l) = w a b + chainCost w (b :: l) := by
  simp [chainCost]

lemma cc_split (w : Option (Fin n) → Option (Fin n) → EReal) (l1 : List (Option (Fin n)))
    (a : Option (Fin n)) (l2 : List (Option (Fin n))) :
    chainCost w (l1 ++ a :: l2) = chainCost w (l1 ++ [a]) + chainCost w (a :: l2) := by
  induction l1 with
  | nil => simp [cc_single]
  | cons x t ih =>
    cases t with
    | nil => simp [cc_cons_cons, cc_single]
    | cons y t' =>
      simp only [List.cons_append] at ih ⊢
      rw [cc_cons_cons, cc_cons_cons, ih, add_assoc]

lemma cc_range (w : Option (Fin n) → Option (Fin n) → EReal) (f : ℕ → Option (Fin n)) (N : ℕ) :
    chainCost w ((List.range (N + 1)).map f) = ∑ k ∈ Finset.range N, w (f k) (f (k + 1)) := by
  induction N with
  | zero => simp [cc_single]
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [List.append_assoc, List.singleton_append, cc_split, ← List.map_singleton (f := f),
      ← List.map_append, ← List.range_succ, ih, Finset.sum_range_succ, cc_cons_cons, cc_single,
      add_zero]

lemma exists_cycle_split {α : Type} [DecidableEq α] (l : List α) (h : ¬ l.Nodup) :
    ∃ p a q s, l = p ++ a :: (q ++ a :: s) ∧ (a :: q).Nodup := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
    by_cases ht : t.Nodup
    · have hx : x ∈ t := by
        by_contra hx; exact h (List.nodup_cons.2 ⟨hx, ht⟩)
      obtain ⟨q, s, rfl⟩ := List.append_of_mem hx
      refine ⟨[], x, q, s, rfl, ?_⟩
      rw [List.nodup_append] at ht
      refine List.nodup_cons.2 ⟨fun hxq => ?_, ht.1⟩
      exact ht.2.2 x hxq x (List.mem_cons_self) rfl
    · obtain ⟨p, a, q, s, rfl, hn⟩ := ih ht
      exact ⟨x :: p, a, q, s, by simp, hn⟩

lemma head?_split {α : Type} (p : List α) (a : α) (X Y : List α) :
    (p ++ a :: X).head? = (p ++ a :: Y).head? := by
  cases p <;> simp

lemma getLast?_split {α : Type} (p : List α) (a : α) (X : List α) :
    (p ++ a :: X).getLast? = (a :: X).getLast? := by
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]

/-- Every chain can be shortened to a chain without repeated nodes, with the same ends. -/
lemma nodup_chain {α : Type} [DecidableEq α] (R : α → α → Prop) :
    ∀ (l : List α), List.IsChain R l → ∃ l', List.IsChain R l' ∧ l'.Nodup ∧
      l'.head? = l.head? ∧ l'.getLast? = l.getLast? := by
  intro l
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    intro hl
    by_cases hn : l.Nodup
    · exact ⟨l, hl, hn, rfl, rfl⟩
    obtain ⟨p, a, q, s, rfl, -⟩ := exists_cycle_split l hn
    have h1 := List.isChain_split.1 hl
    have h2 : List.IsChain R (p ++ a :: s) :=
      List.isChain_split.2 ⟨h1.1, (List.isChain_split.1 (show List.IsChain R ((a :: q) ++ a :: s)
        from by simpa using h1.2)).2⟩
    obtain ⟨l', hl', hn', hh, ht⟩ := ih (p ++ a :: s).length (by simp at h ⊢; omega) _ rfl h2
    refine ⟨l', hl', hn', ?_, ?_⟩
    · rw [hh]; exact head?_split _ _ _ _
    · rw [ht, getLast?_split, getLast?_split p a (q ++ a :: s)]
      simp [List.getLast?_cons]

end SSChainAux



namespace SSChainAux

variable {n : ℕ}

lemma reach_refl (G : ArcGraph n) (i : Fin n) : Reach G i i := Relation.ReflTransGen.refl

lemma reach_trans (G : ArcGraph n) {i j k : Fin n} (h1 : Reach G i j) (h2 : Reach G j k) :
    Reach G i k := Relation.ReflTransGen.trans h1 h2

lemma reach_arc (G : ArcGraph n) {i j : Fin n} (h : (i, j) ∈ G.A) : Reach G i j :=
  Relation.ReflTransGen.single h

lemma reach_cycle (G : ArcGraph n) {m : ℕ} (v : Fin (m + 2) → Fin n)
    (hA : ∀ k, (v k, v (k + 1)) ∈ G.A) (j : Fin (m + 2)) :
    ∀ d : ℕ, Reach G (v j) (v (j + (Nat.cast d : Fin (m + 2)))) := by
  intro d
  induction d with
  | zero => simpa using reach_refl G (v j)
  | succ d ih =>
    have := hA (j + (Nat.cast d : Fin (m + 2)))
    rw [Nat.cast_succ, ← add_assoc]
    exact Relation.ReflTransGen.tail ih this

lemma same_comp_cycle (G : ArcGraph n) {m : ℕ} (v : Fin (m + 2) → Fin n)
    (hA : ∀ k, (v k, v (k + 1)) ∈ G.A) (j : Fin (m + 2)) :
    SameComponent G (v j) (v (j + 1)) := by
  refine ⟨reach_arc G (hA j), ?_⟩
  have := reach_cycle G v hA (j + 1) (m + 1)
  have e : j + 1 + (Nat.cast (m + 1) : Fin (m + 2)) = j := by
    rw [add_assoc]
    have : (1 : Fin (m + 2)) + (Nat.cast (m + 1) : Fin (m + 2)) = 0 := by
      have h2 : (Nat.cast (m + 2) : Fin (m + 2)) = 0 := Fin.natCast_self (m + 2)
      have h3 : (Nat.cast (m + 2) : Fin (m + 2)) = Nat.cast (m + 1) + 1 := Nat.cast_succ (m + 1)
      exact (add_comm _ _).trans (h3.symm.trans h2)
    rw [this, add_zero]
  rwa [e] at this

lemma cast_succ_fin {m : ℕ} (k : ℕ) : (Nat.cast (k + 1) : Fin (m + 2)) = (Nat.cast k : Fin (m + 2)) + 1 := by
  push_cast; rfl

lemma cycle_chain (G : ArcGraph n) (S : Finset (Fin n)) {m : ℕ} (v : Fin (m + 2) → Fin n)
    (hA : ∀ k, (v k, v (k + 1)) ∈ G.A) :
    List.IsChain (AugArc G S) ((List.range (m + 3)).map (fun k : ℕ => some (v (Nat.cast k : Fin (m + 2))))) := by
  rw [List.isChain_map]
  show List.IsChain _ (List.range (m + 2).succ)
  rw [List.isChain_range_succ]
  intro k _
  show (v k, v (Nat.cast (k + 1) : Fin (m + 2))) ∈ G.A
  rw [cast_succ_fin]
  exact hA _

lemma cycle_cost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (b : Fin n → Fin n → ℝ)
    (bν : Fin n → ℝ) {m : ℕ} (v : Fin (m + 2) → Fin n) (hv : Function.Injective v)
    (hA : ∀ k, (v k, v (k + 1)) ∈ G.A) :
    chainCost (augCost G c b bν) ((List.range (m + 3)).map (fun k : ℕ => some (v (Nat.cast k : Fin (m + 2))))) =
      ∑ p ∈ Finset.univ.image (fun k => (v k, v (k + 1))), slopeAtInfty (c p.1 p.2) := by
  rw [cc_range, ← Fin.sum_univ_eq_sum_range
    (fun k => augCost G c b bν (some (v (Nat.cast k : Fin (m + 2)))) (some (v (Nat.cast (k + 1) : Fin (m + 2)))))]
  rw [Finset.sum_image (fun x _ y _ h => hv (Prod.mk.inj h).1)]
  apply Finset.sum_congr rfl
  intro j _
  rw [cast_succ_fin, Fin.cast_val_eq_self]
  simp only [augCost, if_pos (same_comp_cycle G v hA j)]

lemma slope_ne_top (f : ℝ → ℝ) : slopeAtInfty f ≠ ⊤ := by
  have : slopeAtInfty f ≤ ((derivWithin f (Set.Ioi 1) 1 : ℝ) : EReal) :=
    iInf₂_le (f := fun (t : ℝ) (_ : 0 < t) => ((derivWithin f (Set.Ioi t) t : ℝ) : EReal)) 1
      one_pos
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this

/-- A nonempty list without repeats whose closing is a chain is a simple circuit. -/
lemma list_circuit (G : ArcGraph n) (L : List (Fin n)) (hL : L.Nodup) (hne : L ≠ [])
    (hch : List.IsChain (fun a b => (a, b) ∈ G.A) (L ++ [L.head hne])) :
    ∃ (m : ℕ) (v : Fin (m + 2) → Fin n), Function.Injective v ∧ (∀ k, (v k, v (k + 1)) ∈ G.A) ∧
      L ++ [L.head hne] = (List.range (m + 3)).map (fun k : ℕ => v (Nat.cast k : Fin (m + 2))) ∧
      v 0 = L.head hne ∧ v (Fin.last (m + 1)) = L.getLast hne := by
  have hlen : 2 ≤ L.length := by
    rcases L with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact absurd rfl hne
    · exfalso
      simp only [List.head_cons, List.cons_append, List.nil_append] at hch
      exact G.loopless _ (List.isChain_pair.1 hch) rfl
    · simp
  obtain ⟨m, hm⟩ : ∃ m, L.length = m + 2 := ⟨L.length - 2, by omega⟩
  let v : Fin (m + 2) → Fin n := fun k => L[k.val]'(by omega)
  have heq : L ++ [L.head hne] = (List.range (m + 3)).map (fun k : ℕ => v (Nat.cast k : Fin (m + 2))) := by
    apply List.ext_getElem
    · simp [hm]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, v, Fin.val_natCast]
      rcases Nat.lt_or_ge i (m + 2) with hi | hi
      · rw [List.getElem_append_left (by omega)]
        congr 1; rw [Nat.mod_eq_of_lt hi]
      · have hi' : i = m + 2 := by simp [hm] at h1; omega
        rw [List.getElem_append_right (by omega)]
        simp only [List.getElem_singleton, List.head_eq_getElem]
        congr 1; subst hi'; simp
  refine ⟨m, v, ?_, ?_, heq, ?_, ?_⟩
  · intro j j' h
    exact Fin.ext ((hL.getElem_inj_iff).1 h)
  · rw [heq, List.isChain_map] at hch
    have hch' : List.IsChain _ (List.range (m + 2).succ) := hch
    rw [List.isChain_range_succ] at hch'
    intro k
    have := hch' k.val k.isLt
    rwa [cast_succ_fin, Fin.cast_val_eq_self] at this
  · simp [v, List.head_eq_getElem]
  · simp only [v, Fin.val_last, List.getLast_eq_getElem]
    congr 1; omega

lemma ereal_sum_bot {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → EReal) (i : ι) (hi : i ∈ s)
    (h : f i = ⊥) : ∑ j ∈ s, f j = ⊥ := by
  rw [← Finset.add_sum_erase s f hi, h, EReal.bot_add]

/-- Under 5°, the slope of an arc inside a strong component is not `-∞`. -/
lemma arc_slope_ne_bot (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h5 : ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2))
    (i j : Fin n) (hp : (i, j) ∈ G.A) (hs : SameComponent G i j) :
    slopeAtInfty (c i j) ≠ ⊥ := by
  intro hbot
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hs.2
  obtain ⟨L, hLc, hLn, hLh, hLt⟩ := nodup_chain _ (j :: l) hl
  have hne : L ≠ [] := by intro h; simp [h] at hLh
  have hhead : L.head hne = j := by
    rw [List.head?_eq_some_head hne] at hLh; simpa using hLh
  have hglast : L.getLast hne = i := by
    rw [List.getLast?_eq_some_getLast hne, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast] at hLt
    simpa using hLt
  have hch : List.IsChain (fun a b => (a, b) ∈ G.A) (L ++ [L.head hne]) := by
    refine List.IsChain.append hLc (List.isChain_singleton _) ?_
    intro x hx y hy
    rw [List.getLast?_eq_some_getLast hne] at hx
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
    rw [← hx, ← hy, hglast, hhead]; exact hp
  obtain ⟨m, v, hv, hA, -, h0, hl'⟩ := list_circuit G L hLn hne hch
  have hC := h5 _ ⟨m, v, hv, hA, rfl⟩
  have hmem : (i, j) ∈ Finset.univ.image (fun k => (v k, v (k + 1))) := by
    rw [Finset.mem_image]
    refine ⟨Fin.last (m + 1), Finset.mem_univ _, ?_⟩
    rw [Fin.last_add_one, h0, hl', hhead, hglast]
  rw [ereal_sum_bot _ _ _ hmem hbot] at hC
  exact absurd hC (by simp)

end SSChainAux



namespace SSChainAux

variable {n : ℕ}

lemma lift_some {α : Type} (l : List (Option α)) (h : ∀ x ∈ l, x ≠ none) :
    ∃ L : List α, l = L.map some := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x t ih =>
    obtain ⟨L, hL⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.1 (h x List.mem_cons_self)
    exact ⟨a :: L, by simp [hL]⟩

lemma augArc_src (G : ArcGraph n) (S : Finset (Fin n)) {x y : Option (Fin n)}
    (h : AugArc G S x y) : x ≠ none := by
  rintro rfl
  cases y <;> exact h

lemma closed_nonneg (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h5 : ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2))
    (S : Finset (Fin n)) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (a : Option (Fin n)) (q : List (Option (Fin n))) (hn : (a :: q).Nodup)
    (hch : List.IsChain (AugArc G S) (a :: (q ++ [a]))) :
    0 ≤ chainCost (augCost G c b bν) (a :: (q ++ [a])) := by
  have hsome : ∀ x ∈ a :: q, x ≠ none := by
    intro x hx
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem hx
    have e : a :: (q ++ [a]) = l1 ++ x :: (l2 ++ [a]) := by
      rw [← List.cons_append, hl]; simp
    obtain ⟨y, rest, hy⟩ : ∃ y rest, l2 ++ [a] = y :: rest := by
      cases l2 with
      | nil => exact ⟨a, [], rfl⟩
      | cons z l2' => exact ⟨z, l2' ++ [a], rfl⟩
    rw [e, hy] at hch
    exact augArc_src G S (List.isChain_append_cons_cons.1 hch).2.1
  obtain ⟨L, hL⟩ := lift_some _ hsome
  cases L with
  | nil => simp at hL
  | cons a0 L' =>
    simp only [List.map_cons, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    have hLn : (a0 :: L').Nodup := by
      have : ((a0 :: L').map some).Nodup := by simpa using hn
      exact this.of_map _
    have eq : some a0 :: (L'.map some ++ [some a0]) = (a0 :: L' ++ [a0]).map some := by simp
    have hch' : List.IsChain (fun a b => (a, b) ∈ G.A)
        ((a0 :: L') ++ [(a0 :: L').head (List.cons_ne_nil _ _)]) := by
      rw [eq, List.isChain_map] at hch
      simp only [List.head_cons, List.cons_append] at hch ⊢
      exact hch
    obtain ⟨m, v, hv, hA, heq, -, -⟩ := list_circuit G (a0 :: L') hLn (List.cons_ne_nil _ _) hch'
    rw [eq]
    have : (a0 :: L' ++ [a0]).map some =
        (List.range (m + 3)).map (fun k : ℕ => some (v (Nat.cast k : Fin (m + 2)))) := by
      have heq' : a0 :: L' ++ [a0] =
          (List.range (m + 3)).map (fun k : ℕ => v (Nat.cast k : Fin (m + 2))) := by
        simpa using heq
      rw [heq', List.map_map]; rfl
    rw [this, cycle_cost G c b bν v hv hA]
    exact h5 _ ⟨m, v, hv, hA, rfl⟩

/-- Deleting closed subwalks of nonnegative cost: every chain can be replaced by one without
repeated nodes, with the same ends and no larger cost. -/
lemma reduce_cost (G : ArcGraph n) (S : Finset (Fin n))
    (w : Option (Fin n) → Option (Fin n) → EReal)
    (hcyc : ∀ a q, (a :: q).Nodup → List.IsChain (AugArc G S) (a :: (q ++ [a])) →
      0 ≤ chainCost w (a :: (q ++ [a]))) :
    ∀ (l : List (Option (Fin n))), List.IsChain (AugArc G S) l → ∃ l', List.IsChain (AugArc G S) l' ∧
      l'.Nodup ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧ chainCost w l' ≤ chainCost w l := by
  intro l
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    intro hl
    by_cases hn : l.Nodup
    · exact ⟨l, hl, hn, rfl, rfl, le_rfl⟩
    obtain ⟨p, a, q, s, rfl, hnq⟩ := exists_cycle_split l hn
    have h1 := List.isChain_split.1 hl
    have h1' := List.isChain_split.1 (show List.IsChain (AugArc G S) ((a :: q) ++ a :: s)
        from by simpa using h1.2)
    have h2 : List.IsChain (AugArc G S) (p ++ a :: s) := List.isChain_split.2 ⟨h1.1, h1'.2⟩
    have hY := hcyc a q hnq (by simpa using h1'.1)
    obtain ⟨l', hl', hn', hh, ht, hc⟩ := ih (p ++ a :: s).length (by simp at h ⊢; omega) _ rfl h2
    refine ⟨l', hl', hn', ?_, ?_, ?_⟩
    · rw [hh]; exact head?_split _ _ _ _
    · rw [ht, getLast?_split, getLast?_split p a (q ++ a :: s)]
      simp [List.getLast?_cons]
    · refine hc.trans ?_
      rw [cc_split, cc_split w p a (q ++ a :: s),
        show a :: (q ++ a :: s) = (a :: q) ++ a :: s by simp, cc_split w (a :: q) a s]
      have : chainCost w (a :: q ++ [a]) = chainCost w (a :: (q ++ [a])) := by simp
      rw [this]
      exact add_le_add_right (le_add_of_nonneg_left hY) _

lemma arc_real (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h5 : ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2))
    (S : Finset (Fin n)) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ) (x y : Option (Fin n))
    (h : AugArc G S x y) : ∃ r : ℝ, augCost G c b bν x y = r := by
  rcases x with _ | i
  · exact absurd rfl (augArc_src G S h)
  rcases y with _ | j
  · exact ⟨bν i, rfl⟩
  have hA : (i, j) ∈ G.A := h
  by_cases hs : SameComponent G i j
  · refine ⟨(slopeAtInfty (c i j)).toReal, ?_⟩
    simp only [augCost, if_pos hs]
    exact (EReal.coe_toReal (slope_ne_top _) (arc_slope_ne_bot G c h5 i j hA hs)).symm
  · exact ⟨b i j, by simp only [augCost, if_neg hs]⟩

lemma chain_cost_real (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h5 : ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2))
    (S : Finset (Fin n)) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ) :
    ∀ l : List (Option (Fin n)), List.IsChain (AugArc G S) l →
      ∃ r : ℝ, chainCost (augCost G c b bν) l = r := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp [cc_nil]⟩
  | cons a t ih =>
    intro hl
    cases t with
    | nil => exact ⟨0, by simp [cc_single]⟩
    | cons b' t' =>
      rw [List.isChain_cons_cons] at hl
      obtain ⟨r1, hr1⟩ := arc_real G c h5 S b bν a b' hl.1
      obtain ⟨r2, hr2⟩ := ih hl.2
      exact ⟨r1 + r2, by rw [cc_cons_cons, hr1, hr2]; norm_cast⟩

lemma reach_sink (G : ArcGraph n) (i : Fin n) : ∃ j, Reach G i j ∧ InSinkComponent G j := by
  classical
  obtain ⟨j, hj, hmin⟩ := (Finset.univ.filter (fun j => Reach G i j)).exists_min_image
    (fun j => (Finset.univ.filter (fun k => Reach G j k)).card) ⟨i, by simp [reach_refl]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hmin
  refine ⟨j, hj, fun k hk => ?_⟩
  have hsub : Finset.univ.filter (fun x => Reach G k x) ⊆ Finset.univ.filter (fun x => Reach G j x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact reach_trans G hk hx
  have heq := Finset.eq_of_subset_of_card_le hsub (hmin k (reach_trans G hj hk))
  have : j ∈ Finset.univ.filter (fun x => Reach G k x) := by rw [heq]; simp [reach_refl]
  simpa using this

lemma chain_exists (G : ArcGraph n) (S : Finset (Fin n)) (hS : IsSinkSelection G S)
    (u : Option (Fin n)) : ∃ l, IsAugChain G S u none l := by
  rcases u with _ | i
  · exact ⟨[none], List.isChain_singleton _, rfl, rfl⟩
  obtain ⟨j, hij, hj⟩ := reach_sink G i
  obtain ⟨s, ⟨hsS, hjs⟩, -⟩ := hS.2 j hj
  have his := reach_trans G hij hjs.1
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen his
  refine ⟨(i :: l).map some ++ [none], ?_, by simp,
    List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)⟩
  refine List.IsChain.append ((List.isChain_map _).2 hl) (List.isChain_singleton _) ?_
  intro x hx y hy
  rw [List.getLast?_map, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast] at hx
  simp only [Option.map_some, Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
  subst hx; subst hy
  exact hsS

theorem five_implies_six_proof (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h5 : ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2))
    (S : Finset (Fin n)) (hS : IsSinkSelection G S) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (u : Option (Fin n)) :
    HasMinCostChain G S (augCost G c b bν) u := by
  classical
  have hcyc := closed_nonneg G c h5 S b bν
  have hred := reduce_cost G S (augCost G c b bν) hcyc
  let T := {l : List (Option (Fin n)) | IsAugChain G S u none l ∧ l.Nodup}
  have hfin : T.Finite := by
    refine (List.finite_length_le (Option (Fin n)) (n + 1)).subset ?_
    intro l hl
    have := hl.2.length_le_card
    simpa using this
  obtain ⟨l0, hl0⟩ := chain_exists G S hS u
  obtain ⟨l1, hl1c, hl1n, hl1h, hl1t, -⟩ := hred l0 hl0.1
  have hne : T.Nonempty := ⟨l1, ⟨hl1c, hl1h.trans hl0.2.1, hl1t.trans hl0.2.2⟩, hl1n⟩
  obtain ⟨lm, hlmT, hlmin⟩ := Set.exists_min_image T (chainCost (augCost G c b bν)) hfin hne
  obtain ⟨r, hr⟩ := chain_cost_real G c h5 S b bν lm hlmT.1.1
  refine ⟨lm, hlmT.1, by rw [hr]; exact EReal.coe_ne_bot r, by rw [hr]; exact EReal.coe_ne_top r,
    fun l' hl' => ?_⟩
  obtain ⟨l'', hc, hn, hh, ht, hle⟩ := hred l' hl'.1
  exact (hlmin l'' ⟨⟨hc, hh.trans hl'.2.1, ht.trans hl'.2.2⟩, hn⟩).trans hle

end SSChainAux



namespace SSChainAux

variable {n : ℕ}

lemma same_refl (G : ArcGraph n) (i : Fin n) : SameComponent G i i := ⟨reach_refl G i, reach_refl G i⟩

lemma same_symm (G : ArcGraph n) {i j : Fin n} (h : SameComponent G i j) : SameComponent G j i :=
  ⟨h.2, h.1⟩

lemma same_trans (G : ArcGraph n) {i j k : Fin n} (h1 : SameComponent G i j)
    (h2 : SameComponent G j k) : SameComponent G i k :=
  ⟨reach_trans G h1.1 h2.1, reach_trans G h2.2 h1.2⟩

open Classical in
/-- A canonical representative (the least node) of the strong component of `i`. -/
noncomputable def rep (G : ArcGraph n) (i : Fin n) : Fin n :=
  (Finset.univ.filter (SameComponent G i)).min' ⟨i, by simp [same_refl]⟩

lemma rep_same (G : ArcGraph n) (i : Fin n) : SameComponent G i (rep G i) := by
  classical
  have := Finset.min'_mem (Finset.univ.filter (SameComponent G i)) ⟨i, by simp [same_refl]⟩
  unfold rep
  convert (Finset.mem_filter.1 this).2

lemma rep_eq (G : ArcGraph n) {i j : Fin n} (h : SameComponent G i j) : rep G i = rep G j := by
  unfold rep
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hk => same_trans G (same_symm G h) hk, fun hk => same_trans G h hk⟩

lemma sink_selection_exists (G : ArcGraph n) : ∃ S, IsSinkSelection G S := by
  classical
  refine ⟨(Finset.univ.filter (InSinkComponent G)).image (rep G), ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    intro k hk
    have hir := rep_same G i
    exact reach_trans G (hi k (reach_trans G hir.1 hk)) hir.1
  · intro i hi
    refine ⟨rep G i, ⟨?_, rep_same G i⟩, ?_⟩
    · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hi, rfl⟩
    · rintro s ⟨hs, his⟩
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨i', -, rfl⟩ := hs
      exact (rep_eq G (same_trans G his (same_symm G (rep_same G i')))).symm

theorem six_implies_five_proof (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h6 : ∀ S, IsSinkSelection G S → ∀ (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
      ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2) := by
  intro C hC
  obtain ⟨m, v, hv, hA, rfl⟩ := hC
  by_contra hneg
  push Not at hneg
  obtain ⟨S, hS⟩ := sink_selection_exists G
  obtain ⟨l, ⟨hch, hhd, hlast⟩, hb, ht, hmin⟩ := h6 S hS 0 0 (some (v 0))
  obtain ⟨t, rfl⟩ : ∃ t, l = some (v 0) :: t := by
    cases l with
    | nil => simp at hhd
    | cons x t => simp only [List.head?_cons, Option.some.injEq] at hhd; exact ⟨t, by rw [hhd]⟩
  let cyc := (List.range (m + 2)).map (fun k : ℕ => some (v (Nat.cast k : Fin (m + 2))))
  have hcyc_eq : cyc ++ [some (v 0)] =
      (List.range (m + 3)).map (fun k : ℕ => some (v (Nat.cast k : Fin (m + 2)))) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, cyc]
    rw [Fin.natCast_self (m + 2)]
  have hnew : IsAugChain G S (some (v 0)) none (cyc ++ some (v 0) :: t) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [List.isChain_split, hcyc_eq]; exact ⟨cycle_chain G S v hA, hch⟩
    · simp only [cyc, List.range_succ_eq_map, List.map_cons, List.cons_append, List.head?_cons]
      simp
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]; exact hlast
  have hcost := hmin _ hnew
  rw [cc_split, hcyc_eq, cycle_cost G c 0 0 v hv hA] at hcost
  rw [← EReal.coe_toReal ht hb] at hcost
  generalize (chainCost (augCost G c 0 0) (some (v 0) :: t)).toReal = X at hcost
  generalize ∑ p ∈ Finset.univ.image (fun k => (v k, v (k + 1))), slopeAtInfty (c p.1 p.2) = s
    at hcost hneg
  induction s using EReal.rec with
  | bot => simp at hcost
  | top => simp at hneg
  | coe s =>
    have h1 : X ≤ s + X := by exact_mod_cast hcost
    have h2 : s < 0 := by exact_mod_cast hneg
    linarith

end SSChainAux


theorem solution {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h6 : ∀ S, IsSinkSelection G S → ∀ (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
      ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2) :=
  SSChainAux.six_implies_five_proof G c h6
