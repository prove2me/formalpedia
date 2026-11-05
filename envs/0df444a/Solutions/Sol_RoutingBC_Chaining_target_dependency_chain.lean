-- Prove2me | solution 1 for RoutingBC.Chaining.target_dependency_chain
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:33:57.59386+00:00
-- url     : https://prove2.me/submissions/ed1a2a45-31f3-44e4-882a-2cb174304293

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RBCChainAux

open RoutingBC.Chaining

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_routes (R : V → V → V → V → ℝ) (s t : V) (p : List V) :
    p ∈ routes R s t ↔ p.Nodup ∧ IsRoute R s t p := by
  unfold routes
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨⟨q, hq⟩, -, rfl⟩, h⟩
    exact ⟨hq, h⟩
  · rintro ⟨hq, h⟩
    exact ⟨⟨⟨p, hq⟩, rfl⟩, h⟩

theorem chain_rtg {r : V → V → Prop} :
    ∀ (l : List V) (a x : V), (a :: l).IsChain r → x ∈ a :: l → Relation.ReflTransGen r a x
  | [], a, x, _, hx => by
      simp at hx; subst hx; exact Relation.ReflTransGen.refl
  | b :: l, a, x, hc, hx => by
      rw [List.isChain_cons_cons] at hc
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head hc.1 (chain_rtg l b x hc.2 h)

theorem routes_self (R : V → V → V → V → ℝ) (t : V) : routes R t t = {[t]} := by
  ext p
  rw [mem_routes, Finset.mem_singleton]
  constructor
  · rintro ⟨hnd, hh, hl, -, -⟩
    match p, hh with
    | t' :: q, hh =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases q with
      | nil => rfl
      | cons b q =>
        exfalso
        have : t' ∈ b :: q := by
          have := List.getLast?_cons_cons (a := t') (b := b) (l := q)
          rw [this] at hl
          exact List.mem_of_getLast? hl
        exact (List.nodup_cons.1 hnd).1 this
  · rintro rfl
    refine ⟨List.nodup_singleton _, rfl, rfl, by simp, List.isChain_singleton _⟩

/-- First-step decomposition of the routes from `u ≠ t`. -/
theorem mem_routes_cons (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (u t : V) (hu : u ≠ t) (p : List V) :
    p ∈ routes R u t ↔ ∃ w, 0 < R u u w t ∧ ∃ p' ∈ routes R w t, p = u :: p' := by
  constructor
  · intro hp
    rw [mem_routes] at hp
    obtain ⟨hnd, hh, hl, hd, hc⟩ := hp
    match p, hh with
    | u' :: q, hh =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst u'
      cases q with
      | nil => simp at hl; exact absurd hl hu
      | cons w q =>
        rw [List.isChain_cons_cons] at hc
        refine ⟨w, hc.1, w :: q, ?_, rfl⟩
        rw [mem_routes]
        refine ⟨(List.nodup_cons.1 hnd).2, rfl, ?_, ?_, ?_⟩
        · rw [List.getLast?_cons_cons] at hl; exact hl
        · intro hmem
          apply hd
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_of_mem _ hmem
        · have := hc.2
          refine List.IsChain.imp ?_ this
          intro a b hab
          rw [hobl w u a b t]; exact hab
  · rintro ⟨w, hw, p', hp', rfl⟩
    rw [mem_routes] at hp' ⊢
    obtain ⟨hnd, hh, hl, hd, hc⟩ := hp'
    match p', hh with
    | w' :: q, hh =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst w'
      have hc' : (w :: q).IsChain (fun a b => 0 < R u a b t) :=
        List.IsChain.imp (fun a b hab => by rw [hobl u w a b t]; exact hab) hc
      refine ⟨?_, rfl, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, hnd⟩
        intro hmem
        have h1 := chain_rtg q w u hc' hmem
        exact hR.loopFree u t u (Relation.TransGen.head' hw h1)
      · rw [List.getLast?_cons_cons]; exact hl
      · rw [List.dropLast_cons_of_ne_nil (by simp)]
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hu h.symm, hd⟩
      · rw [List.isChain_cons_cons]; exact ⟨hw, hc'⟩

theorem routeProb_cons (R : V → V → V → V → ℝ) (hobl : IsSourceOblivious R) (u w t : V)
    (q : List V) :
    routeProb R u t (u :: w :: q) = R u u w t * routeProb R w t (w :: q) := by
  unfold routeProb
  simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.prod_cons]
  congr 1
  congr 1
  apply List.map_congr_left
  intro x _
  exact hobl u w _ _ t

theorem head_of_mem_routes (R : V → V → V → V → ℝ) (w t : V) (p : List V)
    (hp : p ∈ routes R w t) : ∃ q, p = w :: q := by
  rw [mem_routes] at hp
  obtain ⟨-, hh, -⟩ := hp
  match p, hh with
  | w' :: q, hh =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    exact ⟨q, by rw [hh]⟩

/-- The first-step recursion for path sums. -/
theorem sum_step (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (u t : V) (hu : u ≠ t) (P : List V → Prop)
    [DecidablePred P] :
    ∑ p ∈ (routes R u t).filter P, routeProb R u t p =
      ∑ w, R u u w t * ∑ p ∈ (routes R w t).filter (fun p => P (u :: p)), routeProb R w t p := by
  classical
  have hset : (routes R u t).filter P =
      (Finset.univ.filter (fun w => 0 < R u u w t)).biUnion
        (fun w => ((routes R w t).filter (fun p => P (u :: p))).image (List.cons u)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    rw [mem_routes_cons R hR hobl u t hu]
    constructor
    · rintro ⟨⟨w, hw, p', hp', rfl⟩, hP⟩
      exact ⟨w, hw, p', ⟨hp', hP⟩, rfl⟩
    · rintro ⟨w, hw, p', ⟨hp', hP⟩, rfl⟩
      exact ⟨⟨w, hw, p', hp', rfl⟩, hP⟩
  rw [hset, Finset.sum_biUnion]
  · have h2 : ∑ w, R u u w t * ∑ p ∈ (routes R w t).filter (fun p => P (u :: p)),
        routeProb R w t p = ∑ w ∈ Finset.univ.filter (fun w => 0 < R u u w t),
        R u u w t * ∑ p ∈ (routes R w t).filter (fun p => P (u :: p)), routeProb R w t p := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro w _ hne
      by_contra hneg
      have : R u u w t = 0 := le_antisymm (not_lt.1 hneg) (hR.nonneg _ _ _ _)
      exact hne (by rw [this, zero_mul])
    rw [h2]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_image (fun a _ b _ h => List.cons_injective h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨q, rfl⟩ := head_of_mem_routes R w t p (Finset.mem_filter.1 hp).1
    exact routeProb_cons R hobl u w t q
  · intro w₁ _ w₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_image, Finset.mem_filter] at h1 h2
    obtain ⟨p1, ⟨hp1, -⟩, rfl⟩ := h1
    obtain ⟨p2, ⟨hp2, -⟩, he⟩ := h2
    obtain ⟨q1, rfl⟩ := head_of_mem_routes R w₁ t p1 hp1
    obtain ⟨q2, rfl⟩ := head_of_mem_routes R w₂ t p2 hp2
    simp only [List.cons.injEq] at he
    exact hne he.2.1.symm

/-- Well-founded induction along the (acyclic) routing graph towards `t`. -/
theorem wf_ind (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (t : V) (C : V → Prop)
    (h : ∀ u, (∀ w, 0 < R u u w t → C w) → C u) : ∀ u, C u := by
  let E : V → V → Prop := fun a b => 0 < R t a b t
  let rel : V → V → Prop := fun w u => Relation.TransGen E u w
  have : IsTrans V rel := ⟨fun a b c hab hbc => Relation.TransGen.trans hbc hab⟩
  have : Std.Irrefl rel := ⟨fun a ha => hR.loopFree t t a ha⟩
  have wf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
  intro u
  induction u using wf.induction with
  | _ u ih =>
    apply h u
    intro w hw
    apply ih
    apply Relation.TransGen.single
    show 0 < R t u w t
    rw [hobl t u u w t]; exact hw

theorem mass_eq_one (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (t : V) :
    ∀ u, ∑ p ∈ routes R u t, routeProb R u t p = 1 := by
  apply wf_ind R hR hobl t
  intro u ih
  by_cases hu : u = t
  · subst hu
    rw [routes_self, Finset.sum_singleton]
    simp [routeProb]
  · have := sum_step R hR hobl u t hu (fun _ => True)
    simp only [Finset.filter_true] at this
    rw [this]
    rw [← hR.forward_one u u t hu]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : 0 < R u u w t
    · rw [ih w hw, mul_one]
    · have : R u u w t = 0 := le_antisymm (not_lt.1 hw) (hR.nonneg _ _ _ _)
      rw [this, zero_mul]

theorem delta_self (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (u t : V) : delta R u t u = 1 := by
  unfold delta
  rw [← mass_eq_one R hR hobl t u]
  congr 1
  apply Finset.filter_true_of_mem
  intro p hp
  obtain ⟨q, rfl⟩ := head_of_mem_routes R u t p hp
  simp

theorem delta_target (R : V → V → V → V → ℝ) (t v : V) (hv : v ≠ t) :
    delta R t t v = 0 := by
  unfold delta
  rw [routes_self]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_singleton] at hp
  obtain ⟨rfl, h⟩ := hp
  simp at h
  exact absurd h hv

theorem delta_step (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (u t v : V) (hu : u ≠ t) (huv : u ≠ v) :
    delta R u t v = ∑ w, R u u w t * delta R w t v := by
  unfold delta
  rw [sum_step R hR hobl u t hu]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  apply Finset.filter_congr
  intro p _
  simp only [List.mem_cons]
  constructor
  · rintro (h | h)
    · exact absurd h.symm huv
    · exact h
  · exact Or.inr

theorem seqDelta_step (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (u t a : V) (X L : List V)
    (hL : L.destutter (· ≠ ·) = a :: X) (hu : u ≠ t) (hua : u ≠ a) :
    seqDelta R u t L = ∑ w, R u u w t * seqDelta R w t L := by
  unfold seqDelta
  rw [sum_step R hR hobl u t hu]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  apply Finset.filter_congr
  intro p _
  rw [hL, List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, -⟩)
    · exact h
    · simp only [List.cons.injEq] at hr
      exact absurd hr.1.symm hua
  · exact Or.inl

/-- Lemma 1 style factorisation through the first node of the (destuttered) sequence. -/
theorem seqDelta_factor (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (t a : V) (X L : List V)
    (hL : L.destutter (· ≠ ·) = a :: X) :
    ∀ u, seqDelta R u t L = delta R u t a * seqDelta R a t L := by
  apply wf_ind R hR hobl t
  intro u ih
  by_cases hua : u = a
  · subst hua; rw [delta_self R hR hobl, one_mul]
  by_cases hu : u = t
  · subst hu
    rw [delta_target R u a (Ne.symm hua), zero_mul]
    unfold seqDelta
    rw [routes_self]
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_singleton] at hp
    obtain ⟨rfl, h⟩ := hp
    rw [hL] at h
    have := h.subset (List.mem_cons_self)
    simp at this
    exact absurd this.symm hua
  · rw [seqDelta_step R hR hobl u t a X L hL hu hua, delta_step R hR hobl u t a hu hua,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : 0 < R u u w t
    · rw [ih w hw, mul_assoc]
    · have : R u u w t = 0 := le_antisymm (not_lt.1 hw) (hR.nonneg _ _ _ _)
      rw [this, zero_mul, zero_mul, zero_mul]

theorem destutter_nodup (L : List V) (h : L.Nodup) : L.destutter (· ≠ ·) = L :=
  List.destutter_of_isChain _ _ (List.Pairwise.isChain h)

theorem seqDelta_chain (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (t : V) :
    ∀ (rest : List V) (a : V), (a :: rest).Nodup →
      seqDelta R a t (a :: rest) =
        (((a :: rest).zip rest).map (fun ab => delta R ab.1 t ab.2)).prod
  | [], a, _ => by
      simp only [List.zip_nil_right, List.map_nil, List.prod_nil]
      unfold seqDelta
      rw [← mass_eq_one R hR hobl t a]
      congr 1
      apply Finset.filter_true_of_mem
      intro p hp
      obtain ⟨q, rfl⟩ := head_of_mem_routes R a t p hp
      simp [List.destutter_singleton]
  | b :: r, a, hnd => by
      have hnd' : (b :: r).Nodup := (List.nodup_cons.1 hnd).2
      have hab : a ≠ b := fun h => (List.nodup_cons.1 hnd).1 (by rw [h]; exact List.mem_cons_self)
      have e1 : seqDelta R a t (a :: b :: r) = seqDelta R a t (b :: r) := by
        unfold seqDelta
        rw [destutter_nodup _ hnd, destutter_nodup _ hnd']
        congr 1
        apply Finset.filter_congr
        intro p hp
        obtain ⟨q, rfl⟩ := head_of_mem_routes R a t p hp
        rw [List.cons_sublist_cons, List.sublist_cons_iff]
        constructor
        · exact Or.inl
        · rintro (h | ⟨r', hr, -⟩)
          · exact h
          · simp only [List.cons.injEq] at hr
            exact absurd hr.1.symm hab
      rw [e1, seqDelta_factor R hR hobl t b r (b :: r) (destutter_nodup _ hnd') a,
        seqDelta_chain R hR hobl t r b hnd']
      simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]


theorem seqDelta_nil (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (a t : V) : seqDelta R a t [] = 1 := by
  unfold seqDelta
  rw [← mass_eq_one R hR hobl t a]
  congr 1
  apply Finset.filter_true_of_mem
  intro p _
  simp [List.destutter_nil]

theorem destutter'_head (b : V) : ∀ l : List V, ∃ Z, l.destutter' (· ≠ ·) b = b :: Z
  | [] => ⟨[], by simp [List.destutter'_nil]⟩
  | a :: l => by
      rw [List.destutter'_cons]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact destutter'_head b l

theorem destutter_cons_struct (a : V) : ∀ rest : List V, ∃ Y : List V,
    (a :: rest).destutter (· ≠ ·) = a :: Y ∧ Y.head? ≠ some a ∧
      (rest.destutter (· ≠ ·) = Y ∨ rest.destutter (· ≠ ·) = a :: Y)
  | [] => ⟨[], by simp [List.destutter_singleton], by simp, Or.inl (by simp [List.destutter_nil])⟩
  | b :: r => by
      by_cases hb : b = a
      · subst hb
        obtain ⟨Y, h1, h2, -⟩ := destutter_cons_struct b r
        refine ⟨Y, ?_, h2, Or.inr h1⟩
        rw [List.destutter_cons_cons, if_neg (by simp), ← List.destutter_cons']
        exact h1
      · refine ⟨(b :: r).destutter (· ≠ ·), ?_, ?_, Or.inl rfl⟩
        · rw [List.destutter_cons_cons, if_pos (Ne.symm hb), List.destutter_cons']
        · rw [List.destutter_cons']
          obtain ⟨Z, hZ⟩ := destutter'_head b r
          rw [hZ]
          simpa using hb

/-- Lemma 1 (dependency chaining), for every source. -/
theorem chaining_gen (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (s t s₁ : V) (rest : List V) :
    seqDelta R s t (s₁ :: rest) = delta R s t s₁ * seqDelta R s₁ t rest := by
  obtain ⟨Y, h1, h2, h3⟩ := destutter_cons_struct s₁ rest
  rw [seqDelta_factor R hR hobl t s₁ Y (s₁ :: rest) h1 s]
  congr 1
  unfold seqDelta
  congr 1
  apply Finset.filter_congr
  intro p hp
  obtain ⟨q, rfl⟩ := head_of_mem_routes R s₁ t p hp
  have hY : List.Sublist Y (s₁ :: q) ↔ List.Sublist Y q := by
    rw [List.sublist_cons_iff]
    constructor
    · rintro (h | ⟨r', hr, -⟩)
      · exact h
      · subst hr; simp at h2
    · exact Or.inl
  rw [h1, List.cons_sublist_cons]
  rcases h3 with h3 | h3
  · rw [h3, hY]
  · rw [h3, List.cons_sublist_cons]

theorem product_gen (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (t : V) : ∀ (rest : List V) (a : V),
    seqDelta R a t rest = (((a :: rest).zip rest).map (fun ab => delta R ab.1 t ab.2)).prod
  | [], a => by rw [seqDelta_nil R hR hobl]; simp
  | b :: r, a => by
      rw [chaining_gen R hR hobl a t b r, product_gen R hR hobl t r b]
      simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]

theorem delta_back (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (x u w t : V) (hpos : 0 < R x u w t) :
    delta R w t u = 0 := by
  unfold delta
  apply Finset.sum_eq_zero
  intro p hp
  exfalso
  rw [Finset.mem_filter] at hp
  obtain ⟨hp, hu⟩ := hp
  obtain ⟨q, rfl⟩ := head_of_mem_routes R w t p hp
  rw [mem_routes] at hp
  have h1 := chain_rtg q w u hp.2.2.2.2 hu
  have hpos' : 0 < R w u w t := by rw [hobl w x]; exact hpos
  exact hR.loopFree w t u (Relation.TransGen.head' hpos' h1)

/-- Last-step (predecessor) recursion of the pairwise dependency. -/
theorem delta_last (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R)
    (hobl : IsSourceOblivious R) (t v : V) : ∀ x,
    delta R x t v = (if x = v then 1 else 0) + ∑ u, delta R x t u * R x u v t := by
  apply wf_ind R hR hobl t
  intro x ih
  by_cases hxv : x = v
  · subst hxv
    rw [delta_self R hR hobl, if_pos rfl]
    have : ∑ u, delta R x t u * R x u x t = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      by_cases hp : 0 < R x u x t
      · rw [delta_back R hR hobl x u x t hp, zero_mul]
      · rw [le_antisymm (not_lt.1 hp) (hR.nonneg _ _ _ _), mul_zero]
    rw [this, add_zero]
  rw [if_neg hxv, zero_add]
  by_cases hxt : x = t
  · subst hxt
    rw [delta_target R x v (Ne.symm hxv)]
    symm
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : u = x
    · subst hu; rw [hR.target_silent, mul_zero]
    · rw [delta_target R x u hu, zero_mul]
  have hh : ∀ u, delta R x t u =
      (if u = x then 1 else 0) + ∑ w, R x x w t * delta R w t u := by
    intro u
    by_cases hux : u = x
    · subst hux
      rw [delta_self R hR hobl, if_pos rfl]
      have : ∑ w, R u u w t * delta R w t u = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        by_cases hp : 0 < R u u w t
        · rw [delta_back R hR hobl u u w t hp, mul_zero]
        · rw [le_antisymm (not_lt.1 hp) (hR.nonneg _ _ _ _), zero_mul]
      rw [this, add_zero]
    · rw [if_neg hux, zero_add, delta_step R hR hobl x t u hxt (Ne.symm hux)]
  have hL : ∑ w, R x x w t * delta R w t v =
      ∑ w, R x x w t * ((if w = v then 1 else 0) + ∑ u, delta R w t u * R w u v t) := by
    apply Finset.sum_congr rfl
    intro w _
    by_cases hp : 0 < R x x w t
    · rw [← ih w hp]
    · rw [le_antisymm (not_lt.1 hp) (hR.nonneg _ _ _ _), zero_mul, zero_mul]
  rw [delta_step R hR hobl x t v hxt hxv, hL]
  conv_rhs => arg 2; ext u; rw [hh u]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  rw [hobl w x u v t]
  ring

/-- Freeze the source index of a routing scheme. -/
def fixSrc (R : V → V → V → V → ℝ) (s : V) : V → V → V → V → ℝ := fun _ a b c => R s a b c

theorem fixSrc_scheme (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (s : V) :
    IsRoutingScheme (fixSrc R s) :=
  ⟨fun _ u v t => hR.nonneg s u v t, fun _ u t h => hR.forward_one s u t h,
    fun _ v t => hR.target_silent s v t, fun _ t u => hR.loopFree s t u⟩

theorem fixSrc_obl (R : V → V → V → V → ℝ) (s : V) : IsSourceOblivious (fixSrc R s) :=
  fun _ _ _ _ _ => rfl

theorem delta_fixSrc (R : V → V → V → V → ℝ) (s t v : V) :
    delta R s t v = delta (fixSrc R s) s t v := rfl

end RBCChainAux

open RoutingBC.Chaining RBCChainAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (hobl : IsSourceOblivious R)
    (T : V → V → ℝ) (t s₁ : V) (rest : List V) :
    targetSeqDelta R T t (s₁ :: rest) =
      targetDelta R T t s₁ *
        (((s₁ :: rest).zip rest).map (fun ab => delta R ab.1 t ab.2)).prod := by
  unfold targetSeqDelta targetDelta
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [chaining_gen R hR hobl s t s₁ rest, product_gen R hR hobl t rest s₁]
  ring
