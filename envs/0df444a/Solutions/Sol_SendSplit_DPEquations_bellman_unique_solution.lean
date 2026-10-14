-- Prove2me | solution 1 for SendSplit.DPEquations.bellman_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:05:17.122156+00:00
-- url     : https://prove2.me/submissions/10daa74e-823f-4112-9e28-1987c5d1ddf7

import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_SendSplit_DPEquations_Bellman



namespace SendSplit.DPEquations

theorem ereal_le_add_iInf {ι : Sort*} (M : EReal) (s : ℝ) (f : ι → EReal)
    (h : ∀ i, M ≤ (s:EReal) + f i) : M ≤ (s:EReal) + ⨅ i, f i := by
  have h2 : ∀ i, M - s ≤ f i := fun i => EReal.sub_le_of_le_add' (h i)
  have := le_iInf h2
  have h3 := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s)) (Or.inl (EReal.coe_ne_top s))).1 this
  rwa [add_comm] at h3

section bel
variable {V : Type} [Fintype V] [DecidableEq V]

def bwl (G : BertsekasSPGraph V) : List V → ℝ
  | a :: b :: t => G.length a b + bwl G (b :: t)
  | _ => 0

lemma bwl_eq (G : BertsekasSPGraph V) (l : List V) : BertsekasWalkLength G l = bwl G l := by
  induction l with
  | nil => simp [BertsekasWalkLength, bwl]
  | cons a t ih =>
    cases t with
    | nil => simp [BertsekasWalkLength, bwl]
    | cons b t =>
      simp only [BertsekasWalkLength, bwl] at ih ⊢
      simp only [List.tail_cons] at ih
      simp [List.zip_cons_cons, ih]

lemma bwl_glue (G : BertsekasSPGraph V) (u : List V) (a : V) (v : List V) :
    bwl G (u ++ a :: v) = bwl G (u ++ [a]) + bwl G (a :: v) := by
  induction u with
  | nil => simp [bwl]
  | cons x u ih =>
    cases u with
    | nil => simp [bwl]
    | cons y u' =>
      have := ih
      simp only [List.cons_append] at this ⊢
      simp only [bwl]
      rw [this]; ring

lemma decomp_nodup (l : List V) (h : ¬ l.Nodup) :
    ∃ (p : List V) (a : V) (c' w : List V), l = p ++ a :: c' ++ a :: w ∧ (a :: c').Nodup := by
  induction l with
  | nil => exact absurd List.nodup_nil h
  | cons x l ih =>
    by_cases hl : l.Nodup
    · have hx : x ∈ l := by
        by_contra hx; exact h (List.nodup_cons.2 ⟨hx, hl⟩)
      obtain ⟨u, w, rfl⟩ := List.append_of_mem hx
      refine ⟨[], x, u, w, by simp, ?_⟩
      have := List.nodup_append'.1 hl
      refine List.nodup_cons.2 ⟨?_, this.1⟩
      intro hxu
      exact List.disjoint_left.1 this.2.2 hxu List.mem_cons_self
    · obtain ⟨p, a, c', w, rfl, hn⟩ := ih hl
      exact ⟨x :: p, a, c', w, by simp, hn⟩


lemma cycle_split (G : BertsekasSPGraph V) (hloop : ∀ i, (i, i) ∉ G.arcs)
    (p : List V) (a : V) (c' w : List V)
    (hch : List.IsChain (fun x y => (x, y) ∈ G.arcs) (p ++ a :: c' ++ a :: w))
    (hn : (a :: c').Nodup) :
    IsSimpleCircuit G (a :: c') ∧
    List.IsChain (fun x y => (x, y) ∈ G.arcs) (p ++ a :: w) ∧
    bwl G (p ++ a :: c' ++ a :: w) = bwl G (p ++ a :: w) + circuitLength G (a :: c') := by
  have e1 : p ++ a :: c' ++ a :: w = p ++ a :: (c' ++ a :: w) := by simp
  rw [e1] at hch
  rw [List.isChain_split] at hch
  obtain ⟨h1, h2⟩ := hch
  rw [List.isChain_cons_split] at h2
  obtain ⟨h2, h3⟩ := h2
  have hcirc : List.IsChain (fun x y => (x, y) ∈ G.arcs) ((a :: c') ++ (a :: c').take 1) := by
    simpa using h2
  refine ⟨⟨hn, ?_, hcirc⟩, ?_, ?_⟩
  · rcases c' with _ | ⟨b, c''⟩
    · exfalso
      have : (a, a) ∈ G.arcs := by
        simpa using h2
      exact hloop a this
    · simp
  · exact List.isChain_split.2 ⟨h1, h3⟩
  · rw [e1, bwl_glue, ← List.cons_append, bwl_glue G (a :: c') a w, bwl_glue G p a w]
    unfold circuitLength
    rw [bwl_eq]
    simp
    ring

lemma nodup_walk_exists (G : BertsekasSPGraph V) (hloop : ∀ i, (i, i) ∉ G.arcs)
    (hcirc : ∀ l, IsSimpleCircuit G l → 0 ≤ circuitLength G l) (a b : V) :
    ∀ (n : ℕ) (l : List V), l.length ≤ n → BertsekasIsWalkFrom G a b l →
      ∃ l', l'.Nodup ∧ BertsekasIsWalkFrom G a b l' ∧ bwl G l' ≤ bwl G l := by
  intro n
  induction n with
  | zero =>
    intro l hl hw
    exact absurd (List.length_pos_iff.2 hw.1) (by omega)
  | succ n ih =>
    intro l hl hw
    by_cases hnd : l.Nodup
    · exact ⟨l, hnd, hw, le_rfl⟩
    · obtain ⟨p, x, c', w, rfl, hn⟩ := decomp_nodup l hnd
      obtain ⟨hne, hch, hh, hlast⟩ := hw
      obtain ⟨hsc, hch', hlen⟩ := cycle_split G hloop p x c' w hch hn
      have hcl := hcirc _ hsc
      have hlt : (p ++ x :: w).length ≤ n := by
        simp at hl ⊢; omega
      refine ih _ hlt ⟨by simp, hch', ?_, ?_⟩ |>.imp fun l' hl' => ⟨hl'.1, hl'.2.1, ?_⟩
      · cases p with
        | nil => simpa using hh
        | cons y p' => simpa using hh
      · have h1 := hlast
        have e1 : p ++ x :: c' ++ x :: w = (p ++ x :: c') ++ x :: w := rfl
        rw [e1, List.getLast?_append_of_ne_nil _ (by simp)] at h1
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        exact h1
      · linarith [hl'.2.2]

lemma dist_attained (G : BertsekasSPGraph V) (hloop : ∀ i, (i, i) ∉ G.arcs)
    (hcirc : ∀ l, IsSimpleCircuit G l → 0 ≤ circuitLength G l) (k : V) :
    BertsekasShortestDistance G k G.t = ⊤ ∨
      ∃ l, BertsekasIsWalkFrom G k G.t l ∧
        ((BertsekasWalkLength G l : ℝ) : EReal) = BertsekasShortestDistance G k G.t := by
  set S : Set (List V) := {l | l.Nodup ∧ BertsekasIsWalkFrom G k G.t l} with hS
  have hfin : S.Finite := by
    refine (List.finite_length_le V (Fintype.card V)).subset ?_
    intro l hl
    exact hl.1.length_le_card
  have reduce : ∀ l, BertsekasIsWalkFrom G k G.t l → ∃ l' ∈ S, BertsekasWalkLength G l' ≤
      BertsekasWalkLength G l := by
    intro l hl
    obtain ⟨l', h1, h2, h3⟩ := nodup_walk_exists G hloop hcirc k G.t l.length l le_rfl hl
    exact ⟨l', ⟨h1, h2⟩, by rw [bwl_eq, bwl_eq]; exact h3⟩
  by_cases hne : S.Nonempty
  · right
    obtain ⟨l0, hl0, hmin⟩ := Set.exists_min_image S (BertsekasWalkLength G) hfin hne
    refine ⟨l0, hl0.2, le_antisymm ?_ ?_⟩
    · refine le_iInf fun ⟨l, hl⟩ => ?_
      obtain ⟨l', hl', hle⟩ := reduce l hl
      exact EReal.coe_le_coe_iff.2 ((hmin l' hl').trans hle)
    · exact iInf_le (fun l : {l : List V // BertsekasIsWalkFrom G k G.t l} =>
        ((BertsekasWalkLength G l.1 : ℝ) : EReal)) ⟨l0, hl0.2⟩
  · left
    refine eq_top_iff.2 (le_iInf fun ⟨l, hl⟩ => ?_)
    obtain ⟨l', hl', _⟩ := reduce l hl
    exact absurd ⟨l', hl'⟩ hne

lemma sol_le_walk (G : BertsekasSPGraph V) (hout : ∀ j, (G.t, j) ∉ G.arcs) (C : V → EReal)
    (hC : IsBellmanSolution G C) :
    ∀ l : List V, List.IsChain (fun x y => (x, y) ∈ G.arcs) l → l.getLast? = some G.t →
      ∀ a, l.head? = some a → C a ≤ ((bwl G l : ℝ) : EReal) := by
  intro l
  induction l with
  | nil => intro _ _ a h; simp at h
  | cons x l' ih =>
    intro hch hlast a ha
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    cases l' with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp [hC.2.1, bwl]
    | cons y l'' =>
      rw [List.isChain_cons_cons] at hch
      obtain ⟨hxy, hch'⟩ := hch
      have hxt : x ≠ G.t := fun h => hout y (h ▸ hxy)
      have hlast' : (y :: l'').getLast? = some G.t := by
        simpa [List.getLast?_cons_cons] using hlast
      have h1 := ih hch' hlast' y rfl
      rw [hC.2.2 x hxt]
      refine (Finset.inf_le (f := fun j => ((G.length x j : ℝ) : EReal) + C j)
        (Finset.mem_filter.2 ⟨Finset.mem_univ y, hxy⟩)).trans ?_
      show ((G.length x y : ℝ) : EReal) + C y ≤ ((bwl G (x :: y :: l'') : ℝ) : EReal)
      simp only [bwl]
      rw [EReal.coe_add]
      exact add_le_add le_rfl h1

lemma sol_le_dist (G : BertsekasSPGraph V) (hout : ∀ j, (G.t, j) ∉ G.arcs) (C : V → EReal)
    (hC : IsBellmanSolution G C) (k : V) : C k ≤ BertsekasShortestDistance G k G.t := by
  refine le_iInf fun ⟨l, hl⟩ => ?_
  obtain ⟨hne, hch, hh, hlast⟩ := hl
  have := sol_le_walk G hout C hC l hch hlast k hh
  rwa [bwl_eq]

lemma walk_tt (G : BertsekasSPGraph V) (hout : ∀ j, (G.t, j) ∉ G.arcs) (l : List V)
    (hw : BertsekasIsWalkFrom G G.t G.t l) : bwl G l = 0 := by
  obtain ⟨hne, hch, hh, hlast⟩ := hw
  cases l with
  | nil => exact absurd rfl hne
  | cons x rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil => simp [bwl]
    | cons y r =>
      rw [List.isChain_cons_cons] at hch
      exact absurd hch.1 (hout y)

lemma dist_isSolution (G : BertsekasSPGraph V) (hloop : ∀ i, (i, i) ∉ G.arcs)
    (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hcirc : ∀ l, IsSimpleCircuit G l → 0 ≤ circuitLength G l) :
    IsBellmanSolution G (fun k => BertsekasShortestDistance G k G.t) := by
  have hatt := dist_attained G hloop hcirc
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rcases hatt k with h | ⟨l, _, h⟩
    · simp [h]
    · simp only; rw [← h]; exact EReal.coe_ne_bot _
  · show BertsekasShortestDistance G G.t G.t = 0
    apply le_antisymm
    · have hw : BertsekasIsWalkFrom G G.t G.t [G.t] := ⟨by simp, by simp, by simp, by simp⟩
      have := iInf_le (fun l : {l : List V // BertsekasIsWalkFrom G G.t G.t l} =>
        ((BertsekasWalkLength G l.1 : ℝ) : EReal)) ⟨[G.t], hw⟩
      refine this.trans ?_
      simp [bwl_eq, bwl]
    · refine le_iInf fun ⟨l, hl⟩ => ?_
      rw [bwl_eq, walk_tt G hout l hl]; simp
  · intro k hk
    show BertsekasShortestDistance G k G.t = _
    apply le_antisymm
    · refine Finset.le_inf fun j hj => ?_
      have hjA : (k, j) ∈ G.arcs := (Finset.mem_filter.1 hj).2
      have : BertsekasShortestDistance G k G.t ≤
          ((G.length k j : ℝ) : EReal) + BertsekasShortestDistance G j G.t := by
        unfold BertsekasShortestDistance
        apply ereal_le_add_iInf
        rintro ⟨l', hl'⟩
        obtain ⟨hne, hch, hh, hlast⟩ := hl'
        cases l' with
        | nil => exact absurd rfl hne
        | cons y r =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          have hw : BertsekasIsWalkFrom G k G.t (k :: y :: r) := by
            refine ⟨by simp, ?_, by simp, ?_⟩
            · rw [List.isChain_cons_cons]; exact ⟨hjA, hch⟩
            · simpa [List.getLast?_cons_cons] using hlast
          have := iInf_le (fun l : {l : List V // BertsekasIsWalkFrom G k G.t l} =>
            ((BertsekasWalkLength G l.1 : ℝ) : EReal)) ⟨k :: y :: r, hw⟩
          refine this.trans ?_
          simp only [bwl_eq, bwl]
          rw [EReal.coe_add]
      exact this
    · rcases hatt k with h | ⟨l, hw, h⟩
      · rw [h]; exact le_top
      · obtain ⟨hne, hch, hh, hlast⟩ := hw
        cases l with
        | nil => exact absurd rfl hne
        | cons x rest =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          cases rest with
          | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hlast
            exact absurd hlast hk
          | cons y r =>
            rw [List.isChain_cons_cons] at hch
            obtain ⟨hxy, hch'⟩ := hch
            have hw' : BertsekasIsWalkFrom G y G.t (y :: r) :=
              ⟨by simp, hch', by simp, by simpa [List.getLast?_cons_cons] using hlast⟩
            have h1 : BertsekasShortestDistance G y G.t ≤ ((bwl G (y :: r) : ℝ) : EReal) := by
              refine (iInf_le (fun l : {l : List V // BertsekasIsWalkFrom G y G.t l} =>
                ((BertsekasWalkLength G l.1 : ℝ) : EReal)) ⟨y :: r, hw'⟩).trans ?_
              rw [bwl_eq]
            have hmem : y ∈ Finset.univ.filter (fun j => (x, j) ∈ G.arcs) :=
              Finset.mem_filter.2 ⟨Finset.mem_univ y, hxy⟩
            rw [← h]
            refine (Finset.inf_le (f := fun j => ((G.length x j : ℝ) : EReal) +
              BertsekasShortestDistance G j G.t) hmem).trans ?_
            rw [bwl_eq]
            simp only [bwl]
            rw [EReal.coe_add]
            exact add_le_add le_rfl h1

lemma bwl_mono (G G' : BertsekasSPGraph V) (harcs : G'.arcs ⊆ G.arcs)
    (hlen : ∀ p ∈ G'.arcs, G.length p.1 p.2 ≤ G'.length p.1 p.2) :
    ∀ l : List V, List.IsChain (fun x y => (x, y) ∈ G'.arcs) l → bwl G l ≤ bwl G' l := by
  intro l
  induction l with
  | nil => intro _; simp [bwl]
  | cons x l' ih =>
    intro hch
    cases l' with
    | nil => simp [bwl]
    | cons y r =>
      rw [List.isChain_cons_cons] at hch
      simp only [bwl]
      exact add_le_add (hlen (x, y) hch.1) (ih hch.2)

lemma dist_mono (G G' : BertsekasSPGraph V) (ht : G'.t = G.t) (harcs : G'.arcs ⊆ G.arcs)
    (hlen : ∀ p ∈ G'.arcs, G.length p.1 p.2 ≤ G'.length p.1 p.2) (k : V) :
    BertsekasShortestDistance G k G.t ≤ BertsekasShortestDistance G' k G'.t := by
  refine le_iInf fun ⟨l, hl⟩ => ?_
  obtain ⟨hne, hch, hh, hlast⟩ := hl
  rw [ht] at hlast
  have hw : BertsekasIsWalkFrom G k G.t l :=
    ⟨hne, hch.imp fun x y h => harcs h, hh, hlast⟩
  refine (iInf_le (fun l : {l : List V // BertsekasIsWalkFrom G k G.t l} =>
    ((BertsekasWalkLength G l.1 : ℝ) : EReal)) ⟨l, hw⟩).trans ?_
  show ((BertsekasWalkLength G l : ℝ) : EReal) ≤ ((BertsekasWalkLength G' l : ℝ) : EReal)
  rw [bwl_eq, bwl_eq]
  exact EReal.coe_le_coe_iff.2 (bwl_mono G G' harcs hlen l hch)

theorem greatest_core (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hcirc : ∀ l, IsSimpleCircuit G l → 0 ≤ circuitLength G l) :
    IsBellmanSolution G (fun k => BertsekasShortestDistance G k G.t) ∧
      (∀ k, BertsekasShortestDistance G k G.t = ⊤ ∨
        ∃ l, BertsekasIsWalkFrom G k G.t l ∧
          ((BertsekasWalkLength G l : ℝ) : EReal) = BertsekasShortestDistance G k G.t) ∧
      (∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k ≤ BertsekasShortestDistance G k G.t) ∧
      (∀ G' : BertsekasSPGraph V, G'.t = G.t → G'.arcs ⊆ G.arcs →
        (∀ p ∈ G'.arcs, G.length p.1 p.2 ≤ G'.length p.1 p.2) →
        ∀ k, BertsekasShortestDistance G k G.t ≤ BertsekasShortestDistance G' k G'.t) :=
  ⟨dist_isSolution G hloop hout hcirc, dist_attained G hloop hcirc,
    fun C hC k => sol_le_dist G hout C hC k,
    fun G' ht harcs hlen k => dist_mono G G' ht harcs hlen k⟩

def tightWalk (t : V) (nxt : V → V) : ℕ → V → List V
  | 0, k => [k]
  | m + 1, k => if k = t then [k] else k :: tightWalk t nxt m (nxt k)

lemma exists_tight_succ (G : BertsekasSPGraph V) (C : V → EReal) (hC : IsBellmanSolution G C)
    (x : V) (hx : x ≠ G.t) (hfin : C x ≠ ⊤) :
    ∃ y, (x, y) ∈ G.arcs ∧ C y ≠ ⊤ ∧ C x = ((G.length x y : ℝ) : EReal) + C y := by
  have h := hC.2.2 x hx
  set s := Finset.univ.filter (fun j => (x, j) ∈ G.arcs) with hs
  by_cases hne : s.Nonempty
  · obtain ⟨y, hy, hyeq⟩ := Finset.exists_mem_eq_inf s hne
      (fun j => ((G.length x j : ℝ) : EReal) + C j)
    have hyA : (x, y) ∈ G.arcs := (Finset.mem_filter.1 hy).2
    rw [hyeq] at h
    refine ⟨y, hyA, ?_, h⟩
    intro hy'
    rw [hy'] at h
    exact hfin (by rw [h]; exact EReal.coe_add_top _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    exact absurd (by simpa using h) hfin

lemma tight_chain (G : BertsekasSPGraph V) (C : V → EReal) :
    ∀ l : List V, List.IsChain (fun x y => (x, y) ∈ G.arcs ∧
        C x = ((G.length x y : ℝ) : EReal) + C y) l →
      ∀ a b, l.head? = some a → l.getLast? = some b → C a = ((bwl G l : ℝ) : EReal) + C b := by
  intro l
  induction l with
  | nil => intro _ a b h; simp at h
  | cons x l' ih =>
    intro hch a b ha hb
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    cases l' with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hb
      subst hb
      simp [bwl]
    | cons y r =>
      rw [List.isChain_cons_cons] at hch
      obtain ⟨⟨_, hxy⟩, hch'⟩ := hch
      have hb' : (y :: r).getLast? = some b := by
        simpa [List.getLast?_cons_cons] using hb
      have := ih hch' y b rfl hb'
      simp only [bwl]
      rw [hxy, this, EReal.coe_add, add_assoc]

lemma tightWalk_props (G : BertsekasSPGraph V) (C : V → EReal) (hC : IsBellmanSolution G C)
    (nxt : V → V)
    (hnxt : ∀ x, x ≠ G.t → C x ≠ ⊤ → (x, nxt x) ∈ G.arcs ∧ C (nxt x) ≠ ⊤ ∧
      C x = ((G.length x (nxt x) : ℝ) : EReal) + C (nxt x)) :
    ∀ (m : ℕ) (k : V), C k ≠ ⊤ →
      (tightWalk G.t nxt m k).head? = some k ∧
      List.IsChain (fun x y => (x, y) ∈ G.arcs ∧
        C x = ((G.length x y : ℝ) : EReal) + C y) (tightWalk G.t nxt m k) ∧
      (∀ x ∈ tightWalk G.t nxt m k, C x ≠ ⊤) ∧
      ((tightWalk G.t nxt m k).getLast? = some G.t ∨ (tightWalk G.t nxt m k).length = m + 1) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    simp [tightWalk, hk]
  | succ m ih =>
    intro k hk
    by_cases hkt : k = G.t
    · subst hkt
      simp [tightWalk, hk]
    · obtain ⟨h1, h2, h3⟩ := hnxt k hkt hk
      obtain ⟨i1, i2, i3, i4⟩ := ih (nxt k) h2
      have e : tightWalk G.t nxt (m + 1) k = k :: tightWalk G.t nxt m (nxt k) := by
        simp [tightWalk, hkt]
      rw [e]
      refine ⟨by simp, ?_, ?_, ?_⟩
      · cases hw : tightWalk G.t nxt m (nxt k) with
        | nil => rw [hw] at i1; simp at i1
        | cons z r =>
          rw [hw] at i1 i2
          simp only [List.head?_cons, Option.some.injEq] at i1
          subst i1
          rw [List.isChain_cons_cons]
          exact ⟨⟨h1, h3⟩, i2⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hk
        · exact i3 x hx
      · rcases i4 with h | h
        · left
          have hne : tightWalk G.t nxt m (nxt k) ≠ [] := by
            intro hnil; rw [hnil] at i1; simp at i1
          cases hw : tightWalk G.t nxt m (nxt k) with
          | nil => exact absurd hw hne
          | cons z r =>
            rw [hw] at h
            simpa [List.getLast?_cons_cons, List.getLast?_cons] using h
        · right; simp [h]

lemma dist_le_sol (G : BertsekasSPGraph V) (hloop : ∀ i, (i, i) ∉ G.arcs)
    (hpos : ∀ l, IsSimpleCircuit G l → 0 < circuitLength G l)
    (C : V → EReal) (hC : IsBellmanSolution G C) (k : V) (hk : C k ≠ ⊤) :
    BertsekasShortestDistance G k G.t ≤ C k := by
  have hex : ∀ x, ∃ y, (x ≠ G.t → C x ≠ ⊤ → (x, y) ∈ G.arcs ∧ C y ≠ ⊤ ∧
      C x = ((G.length x y : ℝ) : EReal) + C y) := by
    intro x
    by_cases h : x ≠ G.t ∧ C x ≠ ⊤
    · obtain ⟨y, hy⟩ := exists_tight_succ G C hC x h.1 h.2
      exact ⟨y, fun _ _ => hy⟩
    · exact ⟨x, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose nxt hnxt using hex
  obtain ⟨p1, p2, p3, p4⟩ := tightWalk_props G C hC nxt hnxt (Fintype.card V) k hk
  set l := tightWalk G.t nxt (Fintype.card V) k with hl
  rcases p4 with hlast | hlen
  · have hw : BertsekasIsWalkFrom G k G.t l := by
      refine ⟨?_, p2.imp fun x y h => h.1, p1, hlast⟩
      intro h; rw [h] at p1; simp at p1
    have h1 := tight_chain G C l p2 k G.t p1 hlast
    rw [hC.2.1, add_zero] at h1
    rw [h1]
    have := iInf_le (fun l : {l : List V // BertsekasIsWalkFrom G k G.t l} =>
      ((BertsekasWalkLength G l.1 : ℝ) : EReal)) ⟨l, hw⟩
    refine this.trans ?_
    show ((BertsekasWalkLength G l : ℝ) : EReal) ≤ _
    rw [bwl_eq]
  · exfalso
    have hnd : ¬ l.Nodup := by
      intro hnd
      have := hnd.length_le_card
      omega
    obtain ⟨p, a, c', w, hdec, hn⟩ := decomp_nodup l hnd
    have hch : List.IsChain (fun x y => (x, y) ∈ G.arcs) (p ++ a :: c' ++ a :: w) := by
      rw [← hdec]; exact p2.imp fun x y h => h.1
    obtain ⟨hsc, _, _⟩ := cycle_split G hloop p a c' w hch hn
    have hcl : List.IsChain (fun x y => (x, y) ∈ G.arcs ∧
        C x = ((G.length x y : ℝ) : EReal) + C y) (a :: c' ++ [a]) := by
      refine p2.infix ?_
      exact ⟨p, w, by rw [hdec]; simp⟩
    have haf : C a ≠ ⊤ := by
      apply p3
      rw [hdec]; simp
    have h1 := tight_chain G C _ hcl a a (by simp) List.getLast?_concat
    have hz : bwl G (a :: c' ++ [a]) = 0 := by
      have hr := EReal.coe_toReal haf (hC.1 a)
      have h2 : (((C a).toReal : ℝ) : EReal) =
          ((bwl G (a :: c' ++ [a]) : ℝ) : EReal) + (((C a).toReal : ℝ) : EReal) := by
        rw [hr]; exact h1
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h2
      linarith
    have := hpos _ hsc
    unfold circuitLength at this
    rw [bwl_eq] at this
    simp at this
    have e : a :: (c' ++ [a]) = a :: c' ++ [a] := rfl
    rw [e] at this
    linarith

theorem unique_core (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hpos : ∀ l, IsSimpleCircuit G l → 0 < circuitLength G l) :
    ∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k = BertsekasShortestDistance G k G.t := by
  intro C hC k
  by_cases hk : C k = ⊤
  · have h := sol_le_dist G hout C hC k
    rw [hk] at h ⊢
    exact (eq_top_iff.2 h).symm
  · exact le_antisymm (sol_le_dist G hout C hC k) (dist_le_sol G hloop hpos C hC k hk)

end bel
end SendSplit.DPEquations

open SendSplit.DPEquations


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hpos : ∀ l, IsSimpleCircuit G l → 0 < circuitLength G l) :
    ∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k = BertsekasShortestDistance G k G.t := by
  exact unique_core G hloop hout hpos
