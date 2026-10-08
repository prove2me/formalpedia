-- Prove2me | solution 1 for ProjSchedTW.OrderPolyhedra.feasible_iff_breaks_up_minimal_forbidden_sets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T16:23:15.132987+00:00
-- url     : https://prove2.me/submissions/2413e807-ae1e-444b-b9c2-72213fca105a

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

set_option autoImplicit false

open ProjSchedTW.OrderPolyhedra in
theorem p2m56a_walk_le {n : ℕ} (N : Network n) (S : Fin (n + 2) → ℝ)
    (hS : ∀ a b, (a, b) ∈ N.arcs → (N.wt a b : ℝ) ≤ S b - S a) :
    ∀ (l : List (Fin (n + 2))) (i j : Fin (n + 2)), N.IsPath i j l →
      (N.walkLength l : ℝ) ≤ S j - S i := by
  intro l
  induction l with
  | nil => intro i j h; simp [Network.IsPath] at h
  | cons a t ih =>
    intro i j h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h2
      subst h2; simp [Network.walkLength]
    | cons b t' =>
      rw [List.isChain_cons_cons] at h3
      have hrest : N.IsPath b j (b :: t') :=
        ⟨rfl, by simpa [List.getLast?_cons_cons] using h2, h3.2⟩
      have e1 := ih b j hrest
      have e2 := hS a b h3.1
      simp only [Network.walkLength]
      push_cast
      linarith

open ProjSchedTW.OrderPolyhedra in
theorem p2m56a_cons {n : ℕ} (N : Network n) (a b u : Fin (n + 2)) (l : List (Fin (n + 2)))
    (hl : N.IsPath b u l) (hab : (a, b) ∈ N.arcs) :
    N.IsPath a u (a :: l) ∧ N.walkLength (a :: l) = N.wt a b + N.walkLength l := by
  obtain ⟨h1, h2, h3⟩ := hl
  cases l with
  | nil => simp at h1
  | cons c t =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    refine ⟨⟨rfl, by simpa [List.getLast?_cons_cons] using h2,
      List.isChain_cons_cons.2 ⟨hab, h3⟩⟩, ?_⟩
    simp only [Network.walkLength]

open ProjSchedTW.OrderPolyhedra in
theorem p2m56a_arcs {n : ℕ} {K : Type} (P : Project n K) (O : Finset (Fin (n + 2) × Fin (n + 2)))
    (S : Fin (n + 2) → ℝ) :
    (∀ a b, (a, b) ∈ (P.orderNetwork O).arcs → ((P.orderNetwork O).wt a b : ℝ) ≤ S b - S a) ↔
    ((∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1) ∧
      ∀ e ∈ O, S e.1 + (P.p e.1 : ℝ) ≤ S e.2) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨a, b⟩ he
      have hh := h a b (by simp [Project.orderNetwork, he])
      refine le_trans ?_ hh
      simp only [Project.orderNetwork]
      split_ifs
      · push_cast; exact le_max_left _ _
      · exact le_rfl
    · rintro ⟨a, b⟩ he
      have hh := h a b (by simp [Project.orderNetwork, he])
      simp only [Project.orderNetwork] at hh
      simp only
      split_ifs at hh
      · push_cast at hh
        have := le_max_right (P.δ a b : ℝ) (P.p a : ℝ)
        linarith
      · push_cast at hh; linarith
  · rintro ⟨hE, hO⟩ a b hab
    simp only [Project.orderNetwork] at hab ⊢
    split_ifs with h1 h2
    · push_cast
      have h3 := hO _ h1
      exact max_le (hE _ h2) (by simp only at h3; linarith)
    · push_cast
      have h3 := hO _ h1
      simp only at h3; linarith
    · have : (a, b) ∈ P.E := by
        simp only [Set.mem_union, Finset.mem_coe] at hab; tauto
      exact hE _ this

/- Theorem 2.3.10 (p. 35, Bartusch et al. 1988): a time-feasible strict order `O` in `V` is
feasible if and only if for each minimal forbidden set `F ∈ ℱ`, the order network `N(O)`
contains a path from some node `i ∈ F` to some node `j ∈ F` whose length is at least `p_i`. -/
open ProjSchedTW.OrderPolyhedra in
theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) (hO : P.IsTimeFeasibleOrder O) :
    P.IsFeasibleOrder O ↔
      ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F →
        ∃ i ∈ F, ∃ j ∈ F, (P.orderNetwork O).HasPathOfLengthAtLeast i j (P.p i) := by
  constructor
  · rintro ⟨-, hfeas⟩ F hF
    by_contra hneg
    have hlt : ∀ i ∈ F, ∀ j ∈ F, ∀ l, (P.orderNetwork O).IsPath i j l →
        (P.orderNetwork O).walkLength l < (P.p i : ℤ) := by
      intro i hi j hj l hl
      by_contra hc
      exact hneg ⟨i, hi, j, hj, l, hl, not_lt.1 hc⟩
    obtain ⟨S0, hS0⟩ := hO.2
    have hS0arc := (p2m56a_arcs P O S0).2 ⟨hS0.1.2, hS0.2⟩
    set N := P.orderNetwork O with hN
    let X : Fin (n + 2) → Set ℝ := fun v =>
      {x | x = S0 v ∨ ∃ u ∈ F, ∃ l, N.IsPath v u l ∧ x = -(N.walkLength l : ℝ)}
    set M : ℝ := ∑ w, S0 w with hMdef
    have hM : ∀ w, S0 w ≤ M := fun w =>
      Finset.single_le_sum (fun w _ => hS0.1.1.2 w) (Finset.mem_univ w)
    have hbdd : ∀ v, BddBelow (X v) := by
      intro v
      refine ⟨-M, ?_⟩
      rintro x (rfl | ⟨u, hu, l, hl, rfl⟩)
      · linarith [hS0.1.1.2 v, hM v]
      · have := p2m56a_walk_le N S0 hS0arc l v u hl
        linarith [hM u, hS0.1.1.2 v]
    have hne : ∀ v, (X v).Nonempty := fun v => ⟨S0 v, Or.inl rfl⟩
    let S : Fin (n + 2) → ℝ := fun v => sInf (X v)
    have hSarc : ∀ a b, (a, b) ∈ N.arcs → (N.wt a b : ℝ) ≤ S b - S a := by
      intro a b hab
      have key : S a + N.wt a b ≤ S b := by
        refine le_csInf (hne b) ?_
        rintro x (rfl | ⟨u, hu, l, hl, rfl⟩)
        · have h1 : S a ≤ S0 a := csInf_le (hbdd a) (Or.inl rfl)
          have h2 := hS0arc a b hab
          linarith
        · obtain ⟨hp, hlen⟩ := p2m56a_cons N a b u l hl hab
          have h1 : S a ≤ -(N.walkLength (a :: l) : ℝ) :=
            csInf_le (hbdd a) (Or.inr ⟨u, hu, a :: l, hp, rfl⟩)
          rw [hlen] at h1
          push_cast at h1
          linarith
      linarith
    have hpF : ∀ i ∈ F, 1 ≤ P.p i := by
      intro i hi
      have := hlt i hi i hi [i] ⟨rfl, rfl, List.isChain_singleton _⟩
      simp [Network.walkLength] at this
      omega
    have hSlo : ∀ i ∈ F, 1 - (P.p i : ℝ) ≤ S i := by
      intro i hi
      refine le_csInf (hne i) ?_
      rintro x (rfl | ⟨u, hu, l, hl, rfl⟩)
      · have h1 := hS0.1.1.2 i
        have h2 : (1 : ℝ) ≤ P.p i := by exact_mod_cast hpF i hi
        linarith
      · have h1 := hlt i hi u hu l hl
        have h2 : (N.walkLength l : ℝ) ≤ (P.p i : ℝ) - 1 := by
          have : N.walkLength l ≤ (P.p i : ℤ) - 1 := by omega
          exact_mod_cast this
        linarith
    have hShi : ∀ j ∈ F, S j ≤ 0 := by
      intro j hj
      have h1 : S j ≤ -(N.walkLength [j] : ℝ) :=
        csInf_le (hbdd j) (Or.inr ⟨j, hj, [j], ⟨rfl, rfl, List.isChain_singleton _⟩, rfl⟩)
      have h0 : N.walkLength [j] = 0 := by simp [Network.walkLength]
      rw [h0] at h1
      simpa using h1
    let S' : Fin (n + 2) → ℝ := fun v => S v - S 0
    have hS'arc : ∀ a b, (a, b) ∈ N.arcs → (N.wt a b : ℝ) ≤ S' b - S' a := by
      intro a b hab
      have := hSarc a b hab
      simp only [S']
      linarith
    obtain ⟨hE', hO'⟩ := (p2m56a_arcs P O S').1 hS'arc
    have hnet : ∀ a b, (a, b) ∈ P.network.arcs → (P.network.wt a b : ℝ) ≤ S' b - S' a := by
      intro a b h
      simp only [Project.network, Finset.mem_coe] at h ⊢
      exact hE' (a, b) h
    have hnonneg : ∀ v, 0 ≤ S' v := by
      intro v
      obtain ⟨l, hl, h0⟩ := hP.2.2.2.2.2.2.2.1 v
      have h1 := p2m56a_walk_le P.network S' hnet l 0 v hl
      have h2 : (0 : ℝ) ≤ (P.network.walkLength l : ℝ) := by exact_mod_cast h0
      have h3 : S' 0 = 0 := by simp [S']
      linarith
    have hmem : S' ∈ P.orderPolyhedron O :=
      ⟨⟨⟨by simp [S'], hnonneg⟩, hE'⟩, hO'⟩
    have hres := (hfeas S' hmem).2
    obtain ⟨k, hk⟩ := hF.1
    obtain ⟨i0, hi0⟩ : F.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      simp at hk
    have ht : 0 ≤ -S 0 := by
      have h1 := hnonneg i0
      have h2 := hShi i0 hi0
      simp only [S'] at h1
      linarith
    have hsub : F ⊆ P.activeSet S' (-S 0) := by
      intro i hi
      simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hShi i hi
      have h2 := hSlo i hi
      simp only [S']
      constructor <;> linarith
    have h1 := hres (-S 0) ht k
    unfold Project.usage at h1
    have h2 := Finset.sum_le_sum_of_subset (f := fun i => P.r i k) hsub
    omega
  · intro h
    refine ⟨hO, fun S hS => ⟨hS.1, ?_⟩⟩
    have harc := (p2m56a_arcs P O S).2 ⟨hS.1.2, hS.2⟩
    intro t _ k
    by_contra hlt
    rw [not_le] at hlt
    have hforb : P.IsForbidden (P.activeSet S t) := by
      unfold Project.usage at hlt
      exact ⟨k, hlt⟩
    obtain ⟨F, hFsub, hFmin⟩ := exists_minimal_le_of_wellFoundedLT _ _ hforb
    obtain ⟨i, hi, j, hj, l, hl, hlen⟩ := h F hFmin
    have hw := p2m56a_walk_le _ S harc l i j hl
    have hi' := hFsub hi
    have hj' := hFsub hj
    simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
    have h3 : ((P.p i : ℤ) : ℝ) ≤ ((P.orderNetwork O).walkLength l : ℝ) := by exact_mod_cast hlen
    push_cast at h3
    linarith [hi'.2, hj'.1]
