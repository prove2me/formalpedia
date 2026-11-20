-- Prove2me | solution 1 for OPG37271.exists_five_cycle_safe_edge_color
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:01:17.880168+00:00
-- url     : https://prove2.me/submissions/8e3f12fd-9cc9-4552-adf4-ae9cf10f67d2

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-- Count of occurrences of `some col` along the 5-cycle vertices. -/
private def fiveCycleColorCount (f : Fin 5 → Option (Fin 4)) (col : Fin 4) : ℕ :=
  (Finset.univ.filter (fun u : Fin 5 => f u = some col)).card

/-- Predicate that cycle edge `e` (connecting `e` and `e + 1`) and color `col` avoid all `M`-edges
at distance `≤ 2` along `C_5` (all `u ≠ e + 3`) as well as all 2-edge-path conflicts in `X`. -/
private def IsSafeFiveCycleChoice (f : Fin 5 → Option (Fin 4)) (X : List (Fin 5 × Fin 4))
    (e : Fin 5) (col : Fin 4) : Prop :=
  (∀ u : Fin 5, u ≠ e + 3 → f u ≠ some col) ∧
  (∀ p ∈ X, (p.1 = e ∨ p.1 = e + 1) → p.2 ≠ col)

private lemma fin5_indep_card_le_two (T : Finset (Fin 5))
    (h01 : ¬ ((0 : Fin 5) ∈ T ∧ (1 : Fin 5) ∈ T))
    (h12 : ¬ ((1 : Fin 5) ∈ T ∧ (2 : Fin 5) ∈ T))
    (h23 : ¬ ((2 : Fin 5) ∈ T ∧ (3 : Fin 5) ∈ T))
    (h34 : ¬ ((3 : Fin 5) ∈ T ∧ (4 : Fin 5) ∈ T))
    (h40 : ¬ ((4 : Fin 5) ∈ T ∧ (0 : Fin 5) ∈ T)) :
    T.card ≤ 2 := by
  decide +revert

/-- On a 5-cycle, if adjacent vertices never carry the same `some col`, then each color appears
at most twice (since `α(C_5) = 2`). -/
private theorem fiveCycleColorCount_le_two_of_adj_ne (f : Fin 5 → Option (Fin 4))
    (hadj : ∀ i : Fin 5, f i ≠ none → f i ≠ f (i + 1)) (col : Fin 4) :
    fiveCycleColorCount f col ≤ 2 := by
  unfold fiveCycleColorCount
  have hno_adj : ∀ i : Fin 5,
      ¬ (i ∈ Finset.univ.filter (fun u : Fin 5 => f u = some col) ∧
         (i + 1) ∈ Finset.univ.filter (fun u : Fin 5 => f u = some col)) := by
    intro i ⟨hi, hi1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi1
    exact hadj i (by simp [hi]) (hi.trans hi1.symm)
  exact fin5_indep_card_le_two _
    (hno_adj 0) (hno_adj 1) (hno_adj 2) (hno_adj 3) (hno_adj 4)

private lemma fin5_add_one_avoid_one (v₁ : Fin 5) :
    v₁ ≠ v₁ + 1 ∧ v₁ ≠ (v₁ + 1) + 1 := by
  decide +revert

private lemma fin5_exists_avoid_two (v₁ v₂ : Fin 5) :
    ∃ e : Fin 5, (v₁ ≠ e ∧ v₁ ≠ e + 1) ∧ (v₂ ≠ e ∧ v₂ ≠ e + 1) := by
  decide +revert

/-- Helper: any list of at most 2 vertices on `Fin 5` blocks at most 4 cycle edges `{v, v - 1}`,
leaving at least one unblocked cycle edge `e : Fin 5`. -/
private lemma exists_edge_avoiding_two_vertices (vs : List (Fin 5)) (hlen : vs.length ≤ 2) :
    ∃ e : Fin 5, ∀ v ∈ vs, v ≠ e ∧ v ≠ e + 1 := by
  cases vs with
  | nil => exact ⟨0, by simp⟩
  | cons v₁ rest =>
    cases rest with
    | nil =>
      refine ⟨v₁ + 1, ?_⟩
      intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      exact fin5_add_one_avoid_one v
    | cons v₂ rest' =>
      cases rest' with
      | nil =>
        obtain ⟨e, he1, he2⟩ := fin5_exists_avoid_two v₁ v₂
        refine ⟨e, ?_⟩
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact he1
        · exact he2
      | cons _ _ =>
        simp only [List.length_cons] at hlen
        omega

/-- Helper: among 3 distinct colors in `Fin 4` and a list of at most 2 forbidden colors in `Fin 4`,
at least one of the 3 colors is not in the forbidden list. -/
private lemma exists_color_not_in_two (S : Finset (Fin 4)) (hS : 3 ≤ S.card)
    (cs : List (Fin 4)) (hlen : cs.length ≤ 2) :
    ∃ col ∈ S, col ∉ cs := by
  by_contra hall
  have hsub : S ⊆ cs.toFinset := by
    intro col hcol
    rw [List.mem_toFinset]
    by_contra hnot
    exact hall ⟨col, hcol, hnot⟩
  have h1 : S.card ≤ cs.toFinset.card := Finset.card_le_card hsub
  have h2 : cs.toFinset.card ≤ cs.length := List.toFinset_card_le cs
  omega

private lemma fin4_sum_ge_six_of_card_le_two (T : Finset (Fin 4)) (hT : T.card ≤ 2) :
    6 ≤ (Finset.univ : Finset (Fin 4)).sum (fun col : Fin 4 => if col ∈ T then 1 else 2) := by
  decide +revert

private lemma fin5_add_two_add_three (u₀ : Fin 5) : (u₀ + 2) + 3 = u₀ := by
  decide +revert

/-- **DMS Theorem 4.1(a), 5-Cycle Cases 1 & 2 (multiplicity form)**:
If every color in `Fin 4` appears on at most 2 vertices of `C_5` and `X.length ≤ 2`,
then there exists a safe pair `(e, col)` avoiding all `C_5`-vertices within distance `≤ 2` of `e`
and all `X`-conflicts incident to `e`'s endpoints. -/
private theorem exists_five_cycle_safe_edge_color_of_card_le_two
    (f : Fin 5 → Option (Fin 4))
    (hcount : ∀ col : Fin 4, fiveCycleColorCount f col ≤ 2)
    (X : List (Fin 5 × Fin 4))
    (hX : X.length ≤ 2) :
    ∃ (e : Fin 5) (col : Fin 4), IsSafeFiveCycleChoice f X e col := by
  by_cases hex0 : ∃ col : Fin 4, fiveCycleColorCount f col = 0
  · -- DMS Case 2: Some color `col` does not appear in `f` at all.
    obtain ⟨col, hcol0⟩ := hex0
    have hnone : ∀ u : Fin 5, f u ≠ some col := by
      intro u hu
      have hmem : u ∈ Finset.univ.filter (fun w : Fin 5 => f w = some col) := by
        simp [hu]
      have hpos : 0 < fiveCycleColorCount f col := Finset.card_pos.mpr ⟨u, hmem⟩
      omega
    obtain ⟨e, he⟩ := exists_edge_avoiding_two_vertices (X.map Prod.fst) (by simp [hX])
    refine ⟨e, col, ?_, ?_⟩
    · intro u _
      exact hnone u
    · intro p hp hinc
      have hp1 : p.1 ∈ X.map Prod.fst := List.mem_map_of_mem hp
      obtain ⟨hne1, hne2⟩ := he p.1 hp1
      rcases hinc with h1 | h2
      · exact absurd h1 hne1
      · exact absurd h2 hne2
  · -- DMS Case 1: Every color in `Fin 4` appears at least once (hence 1 or 2 times).
    have hge1 : ∀ col : Fin 4, 1 ≤ fiveCycleColorCount f col := by
      intro col
      have hne : fiveCycleColorCount f col ≠ 0 := fun h0 => hex0 ⟨col, h0⟩
      omega
    let singletons : Finset (Fin 4) :=
      Finset.univ.filter (fun col : Fin 4 => fiveCycleColorCount f col = 1)
    have hsum_le : (Finset.univ : Finset (Fin 4)).sum (fiveCycleColorCount f) ≤ 5 := by
      have hdisj : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
          (fun col : Fin 4 => Finset.univ.filter (fun u : Fin 5 => f u = some col)) := by
        intro c₁ _ c₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro u hu1 hu2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
        exact hne (Option.some.inj (hu1.symm.trans hu2))
      have hbu : ((Finset.univ : Finset (Fin 4)).biUnion
          (fun col : Fin 4 => Finset.univ.filter (fun u : Fin 5 => f u = some col))).card ≤ 5 := by
        simpa using Finset.card_le_univ
          ((Finset.univ : Finset (Fin 4)).biUnion
            (fun col : Fin 4 => Finset.univ.filter (fun u : Fin 5 => f u = some col)))
      rwa [Finset.card_biUnion hdisj] at hbu
    have hsing_ge3 : 3 ≤ singletons.card := by
      by_contra hlt3
      have hle2 : singletons.card ≤ 2 := by omega
      have hval : ∀ col : Fin 4,
          (if col ∈ singletons then 1 else 2) ≤ fiveCycleColorCount f col := by
        intro col
        split_ifs with hm
        · simp only [singletons, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          omega
        · simp only [singletons, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          have h1 := hge1 col
          have h2 := hcount col
          omega
      have hsum_lower :
          (Finset.univ : Finset (Fin 4)).sum (fun col => if col ∈ singletons then 1 else 2) ≤
            (Finset.univ : Finset (Fin 4)).sum (fiveCycleColorCount f) :=
        Finset.sum_le_sum (fun col _ => hval col)
      have h6 := fin4_sum_ge_six_of_card_le_two singletons hle2
      omega
    obtain ⟨col, hcol_sing, hcol_not_X⟩ :=
      exists_color_not_in_two singletons hsing_ge3 (X.map Prod.snd) (by simp [hX])
    simp only [singletons, Finset.mem_filter, Finset.mem_univ, true_and,
      fiveCycleColorCount, Finset.card_eq_one] at hcol_sing
    obtain ⟨u₀, hu₀⟩ := hcol_sing
    refine ⟨u₀ + 2, col, ?_, ?_⟩
    · intro u hu_ne hfu
      have hmem : u ∈ ({u₀} : Finset (Fin 5)) := by
        rw [← hu₀]
        simp [hfu]
      simp only [Finset.mem_singleton] at hmem
      exact hu_ne (hmem.trans (fin5_add_two_add_three u₀).symm)
    · intro p hp _ heq
      apply hcol_not_X
      rw [← heq]
      exact List.mem_map_of_mem hp

/-- **DMS Theorem 4.1(a), 5-Cycle Cases 1 & 2 (adjacent-distinct form)**:
If adjacent vertices on `C_5` never carry `M`-edges of the same color and `X.length ≤ 2`,
then there exists a safe `(e, col)` pair. -/
theorem solution
    (f : Fin 5 → Option (Fin 4))
    (hadj : ∀ i : Fin 5, f i ≠ none → f i ≠ f (i + 1))
    (X : List (Fin 5 × Fin 4))
    (hX : X.length ≤ 2) :
    ∃ (e : Fin 5) (col : Fin 4),
      (∀ u : Fin 5, u ≠ e + 3 → f u ≠ some col) ∧
      (∀ p ∈ X, (p.1 = e ∨ p.1 = e + 1) → p.2 ≠ col) :=
  exists_five_cycle_safe_edge_color_of_card_le_two f
    (fiveCycleColorCount_le_two_of_adj_ne f hadj) X hX
