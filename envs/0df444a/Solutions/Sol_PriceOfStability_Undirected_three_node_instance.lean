-- Prove2me | solution 1 for PriceOfStability.Undirected.three_node_instance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:28:09.144863+00:00
-- url     : https://prove2.me/submissions/ddda1a16-5f16-4559-aa1c-58d9ac2c79cc

import Definitions.Def_PriceOfStability_Undirected_ThreeNode
open CongestionPoA.AsymSum


namespace PriceOfStability.Undirected

section Base
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pu_load (S : Fin 2 → Finset (Sym2 V)) (e : Sym2 V) :
    load S e = (if e ∈ S 0 then 1 else 0) + (if e ∈ S 1 then 1 else 0) := by
  unfold load
  rw [Finset.card_filter, Fin.sum_univ_two]

lemma pu_load_ij (S : Fin 2 → Finset (Sym2 V)) (e : Sym2 V) (i j : Fin 2) (hij : i ≠ j) :
    load S e = (if e ∈ S i then 1 else 0) + (if e ∈ S j then 1 else 0) := by
  rw [pu_load]
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  omega

lemma pu_setCost_split (c : Sym2 V → ℝ) (A B : Finset (Sym2 V)) :
    setCost c A = setCost c (A \ B) + setCost c (A ∩ B) := by
  unfold setCost
  rw [← Finset.sum_filter_add_sum_filter_not A (fun e => e ∈ B), Finset.filter_mem_eq_inter,
    Finset.filter_not, Finset.filter_mem_eq_inter, Finset.sdiff_inter_self_left]
  ring

lemma pu_cost (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V)
    (S : Fin 2 → Finset (Sym2 V)) (i j : Fin 2) (hij : i ≠ j) :
    cost (twoPlayerGame G c s t) S i = setCost c (S i \ S j) + setCost c (S i ∩ S j) / 2 := by
  unfold cost twoPlayerGame PriceOfStability.Harmonic.fairGame setCost
  simp only
  rw [← Finset.sum_filter_add_sum_filter_not (S i) (fun e => e ∈ S j), Finset.filter_mem_eq_inter,
    Finset.filter_not, Finset.filter_mem_eq_inter, Finset.sdiff_inter_self_left, Finset.sum_div,
    add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_sdiff] at he
    rw [pu_load_ij S e i j hij, if_pos he.1, if_neg he.2]; simp
  · apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_inter] at he
    rw [pu_load_ij S e i j hij, if_pos he.1, if_pos he.2]; norm_num

lemma pu_designCost (c : Sym2 V → ℝ) (S : Fin 2 → Finset (Sym2 V)) :
    PriceOfStability.Harmonic.designCost (fun e _ => c e) S = setCost c (S 0 ∪ S 1) := by
  unfold PriceOfStability.Harmonic.designCost setCost
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, pu_load]
  by_cases h0 : e ∈ S 0 <;> by_cases h1 : e ∈ S 1 <;> simp [h0, h1]

lemma pu_setCost_union (c : Sym2 V → ℝ) (A B : Finset (Sym2 V)) :
    setCost c (A ∪ B) = setCost c (A \ B) + setCost c (B \ A) + setCost c (A ∩ B) := by
  have h1 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := c)
  have h2 := pu_setCost_split c A B
  have h3 := pu_setCost_split c B A
  unfold setCost at *
  rw [Finset.inter_comm B A] at h3
  linarith

lemma pu_setCost_nonneg (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) (A : Finset (Sym2 V)) :
    0 ≤ setCost c A := Finset.sum_nonneg (fun e _ => hc e)

lemma pu_setCost_mono (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) {A B : Finset (Sym2 V)} (h : A ⊆ B) :
    setCost c A ≤ setCost c B := Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => hc e)

/-- the two-player potential -/
noncomputable def pot (c : Sym2 V → ℝ) (S : Fin 2 → Finset (Sym2 V)) : ℝ :=
  setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + 3 / 2 * setCost c (S 0 ∩ S 1)

lemma pu_pot_eq (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V)
    (S : Fin 2 → Finset (Sym2 V)) (i j : Fin 2) (hij : i ≠ j) :
    pot c S = cost (twoPlayerGame G c s t) S i + setCost c (S j) := by
  rw [pu_cost G c s t S i j hij, pu_setCost_split c (S j) (S i)]
  unfold pot
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> rw [Finset.inter_comm] <;> ring

lemma pu_exists_nash_min (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V)
    (S : Fin 2 → Finset (Sym2 V)) (hS : IsProfile (twoPlayerGame G c s t) S) :
    ∃ S', IsPureNash (twoPlayerGame G c s t) S' ∧
      ∀ P, IsProfile (twoPlayerGame G c s t) P → pot c S' ≤ pot c P := by
  classical
  have hmem : S ∈ Fintype.piFinset (fun i => (twoPlayerGame G c s t).strategies i) :=
    Fintype.mem_piFinset.mpr hS
  obtain ⟨S', hS'mem, hmin⟩ := Finset.exists_min_image _ (pot c) ⟨S, hmem⟩
  have hprof : ∀ P, IsProfile (twoPlayerGame G c s t) P →
      P ∈ Fintype.piFinset (fun i => (twoPlayerGame G c s t).strategies i) :=
    fun P hP => Fintype.mem_piFinset.mpr hP
  have hS'p : IsProfile (twoPlayerGame G c s t) S' := Fintype.mem_piFinset.mp hS'mem
  refine ⟨S', ⟨hS'p, ?_⟩, fun P hP => hmin P (hprof P hP)⟩
  intro i T hT
  set j : Fin 2 := if i = 0 then 1 else 0 with hj
  have hij : i ≠ j := by fin_cases i <;> simp [hj]
  have hP : IsProfile (twoPlayerGame G c s t) (Function.update S' i T) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [hT]
    · simp [hk]; exact hS'p k
  have h := hmin _ (hprof _ hP)
  rw [pu_pot_eq G c s t S' i j hij, pu_pot_eq G c s t _ i j hij,
    Function.update_of_ne (Ne.symm hij)] at h
  linarith



/-- degree of `v` in the edge set `F` -/
noncomputable def pdeg (F : Finset (Sym2 V)) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => e ∈ F ∧ v ∈ e)).card

lemma pu_reach_of_walk {G' : SimpleGraph V} (F : Set (Sym2 V)) {u w : V} (p : G'.Walk u w)
    (hp : ∀ e ∈ p.edges, e ∈ F) : (SimpleGraph.fromEdgeSet F).Reachable u w := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h q ih =>
    rename_i a b c
    have h1 : (SimpleGraph.fromEdgeSet F).Adj a b := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hp _ (by simp), h.ne⟩
    exact h1.reachable.trans (ih (fun e he => hp e (by simp [he])))

lemma pu_min_par (G : SimpleGraph V) (s : V) (t : Fin 2 → V) (i : Fin 2) (T : Finset (Sym2 V))
    (hT : IsMinimalStrategy G s t i T) (v : V) :
    Even (pdeg T v) ↔ (t i ≠ s → v ≠ t i ∧ v ≠ s) := by
  classical
  obtain ⟨hmem, hmin⟩ := hT
  have hmem' := hmem
  unfold connStrategies at hmem'
  rw [Finset.mem_filter] at hmem'
  obtain ⟨_, hsub, hreach⟩ := hmem'
  obtain ⟨q⟩ := hreach
  set p := q.toPath with hp
  have hpath : (p : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Walk (t i) s).IsPath := p.2
  set T' : Finset (Sym2 V) := (p : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Walk (t i) s).edges.toFinset
    with hT'
  have hT'T : T' ⊆ T := by
    intro e he
    rw [hT', List.mem_toFinset] at he
    have := SimpleGraph.Walk.edges_subset_edgeSet _ he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  have hT'mem : T' ∈ connStrategies G s t i := by
    unfold connStrategies
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, ?_⟩
    · intro e he; exact hsub (hT'T he)
    · apply pu_reach_of_walk _ (p : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Walk (t i) s)
      intro e he
      rw [hT', Finset.mem_coe, List.mem_toFinset]; exact he
  have hEq : T' = T := by
    by_contra hne
    exact hmin T' (Finset.ssubset_iff_subset_ne.mpr ⟨hT'T, hne⟩) hT'mem
  have hdeg : pdeg T v = (p : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Walk (t i) s).edges.countP
      (fun e => v ∈ e) := by
    have h1 : pdeg T v = pdeg T' v := by rw [hEq]
    rw [h1]
    unfold pdeg
    rw [List.countP_eq_length_filter]
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ hpath.isTrail.edges_nodup)]
    congr 1
    ext e
    simp [hT']
  rw [hdeg]
  exact hpath.isTrail.even_countP_edges_iff v

lemma pu_even_sum (C : Finset V) (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hC : ∀ x y, s(x, y) ∈ F → (x ∈ C ↔ y ∈ C)) : Even (∑ v ∈ C, pdeg F v) := by
  classical
  unfold pdeg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.even_sum
  intro e _
  induction e using Sym2.ind with
  | h x y =>
  by_cases he : s(x, y) ∈ F
  · have hxy : x ≠ y := by
      intro h; apply hF _ he; simp [h]
    by_cases hx : x ∈ C
    · have hy : y ∈ C := (hC x y he).mp hx
      have : ∑ v ∈ C, (if s(x, y) ∈ F ∧ v ∈ s(x, y) then 1 else 0) =
          ∑ v ∈ C, ((if v = x then 1 else 0) + (if v = y then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h1 : v = x
        · subst h1; simp [he, hxy]
        · by_cases h2 : v = y
          · subst h2; simp [he, h1]
          · simp [he, h1, h2]
      rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hx, if_pos hy]
      exact ⟨1, rfl⟩
    · have hy : y ∉ C := fun hy => hx ((hC x y he).mpr hy)
      have : ∑ v ∈ C, (if s(x, y) ∈ F ∧ v ∈ s(x, y) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have h1 : v ≠ x := fun h => hx (h ▸ hv)
        have h2 : v ≠ y := fun h => hy (h ▸ hv)
        simp [h1, h2]
      rw [this]; exact ⟨0, rfl⟩
  · have : ∑ v ∈ C, (if s(x, y) ∈ F ∧ v ∈ s(x, y) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      simp [he]
    rw [this]; exact ⟨0, rfl⟩

lemma pu_deg_symmDiff (A B : Finset (Sym2 V)) (v : V) :
    pdeg ((A \ B) ∪ (B \ A)) v + 2 * pdeg (A ∩ B) v = pdeg A v + pdeg B v := by
  unfold pdeg
  simp_rw [Finset.card_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;> by_cases hv : v ∈ e <;> simp [ha, hb, hv]

lemma pu_reach_symmDiff (s u0 u1 : V) (T0 T1 : Finset (Sym2 V))
    (h0 : ∀ v, Even (pdeg T0 v) ↔ (u0 ≠ s → v ≠ u0 ∧ v ≠ s))
    (h1 : ∀ v, Even (pdeg T1 v) ↔ (u1 ≠ s → v ≠ u1 ∧ v ≠ s))
    (hsub : ∀ e ∈ T0 ∪ T1, ¬ e.IsDiag) (hne : u0 ≠ u1) :
    (SimpleGraph.fromEdgeSet (((T0 \ T1) ∪ (T1 \ T0) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
      u0 u1 := by
  classical
  set X : Finset (Sym2 V) := (T0 \ T1) ∪ (T1 \ T0) with hX
  have hpar : ∀ v, Even (pdeg X v) ↔ (v ≠ u0 ∧ v ≠ u1) := by
    intro v
    have hd := pu_deg_symmDiff T0 T1 v
    rw [← hX] at hd
    have e1 : Even (pdeg X v) ↔ Even (pdeg T0 v + pdeg T1 v) := by
      rw [← hd, Nat.even_add]; simp
    rw [e1, Nat.even_add, h0, h1]
    by_cases a : v = u0 <;> by_cases b : v = u1 <;> by_cases c : v = s <;>
      by_cases d0 : u0 = s <;> by_cases d1 : u1 = s <;> simp_all
  by_contra hnr
  set H := SimpleGraph.fromEdgeSet (X : Set (Sym2 V))
  set C : Finset V := Finset.univ.filter (fun v => H.Reachable u0 v)
  have hev := pu_even_sum C X (fun e he => by
      apply hsub e
      rw [hX, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at he
      rw [Finset.mem_union]; tauto)
    (fun x y he => by
      have hxy : x ≠ y := by
        intro h
        apply hsub (s(x, y))
        · rw [hX, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at he
          rw [Finset.mem_union]; tauto
        · simp [h]
      have hadj : H.Adj x y := by
        rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hxy⟩
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩)
  have hu0 : u0 ∈ C := by simp [C]
  rw [← Finset.add_sum_erase C _ hu0, Nat.even_add] at hev
  have hodd : ¬ Even (pdeg X u0) := by rw [hpar]; simp
  apply hodd
  apply hev.mpr
  apply Finset.even_sum
  intro v hv
  rw [Finset.mem_erase] at hv
  rw [hpar]
  refine ⟨hv.1, ?_⟩
  rintro rfl
  simp [C] at hv
  exact hnr hv.2


lemma pu_mem_conn (G : SimpleGraph V) (s : V) (t : Fin 2 → V) (k : Fin 2) (T : Finset (Sym2 V)) :
    T ∈ connStrategies G s t k ↔ ((T : Set (Sym2 V)) ⊆ G.edgeSet ∧
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Reachable (t k) s) := by
  classical
  unfold connStrategies
  rw [Finset.mem_filter]
  simp

lemma pu_dev (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') (i j : Fin 2) (hij : i ≠ j) :
    setCost c (S' i \ S' j) + setCost c (S' i ∩ S' j) / 2 ≤
      setCost c (S i \ S j) + setCost c (S j \ S i) + setCost c (S' j \ S' i) / 2 +
        setCost c (S' i ∩ S' j) / 2 := by
  classical
  set X : Finset (Sym2 V) := (S i \ S j) ∪ (S j \ S i) with hX
  set D : Finset (Sym2 V) := X ∪ S' j with hD
  have hSi := (pu_mem_conn G s t i (S i)).mp (hS i).1
  have hSj := (pu_mem_conn G s t j (S j)).mp (hS j).1
  have hS'j := (pu_mem_conn G s t j (S' j)).mp (hS'.1 j)
  have hDmem : D ∈ connStrategies G s t i := by
    rw [pu_mem_conn]
    constructor
    · intro e he
      simp only [hD, hX, Finset.coe_union, Finset.coe_sdiff, Set.mem_union, Set.mem_sdiff,
        Finset.mem_coe] at he
      rcases he with (h | h) | h
      · exact hSi.1 h.1
      · exact hSj.1 h.1
      · exact hS'j.1 h
    · have r2 : (SimpleGraph.fromEdgeSet (D : Set (Sym2 V))).Reachable (t j) s :=
        hS'j.2.mono (SimpleGraph.fromEdgeSet_mono (by
          intro e he; simp only [hD, Finset.coe_union, Set.mem_union]; exact Or.inr he))
      by_cases ht : t i = t j
      · rw [ht]; exact r2
      · have r1 := pu_reach_symmDiff s (t i) (t j) (S i) (S j)
          (pu_min_par G s t i (S i) (hS i)) (pu_min_par G s t j (S j) (hS j))
          (by
            intro e he
            rw [Finset.mem_union] at he
            rcases he with h | h
            · exact G.not_isDiag_of_mem_edgeSet (hSi.1 h)
            · exact G.not_isDiag_of_mem_edgeSet (hSj.1 h)) ht
        have r1' : (SimpleGraph.fromEdgeSet (D : Set (Sym2 V))).Reachable (t i) (t j) :=
          r1.mono (SimpleGraph.fromEdgeSet_mono (by
            intro e he; simp only [hD, Finset.coe_union, Set.mem_union]; left; exact he))
        exact r1'.trans r2
  have hN := hS'.2 i D hDmem
  rw [pu_cost G c s t S' i j hij, pu_cost G c s t _ i j hij, Function.update_self,
    Function.update_of_ne (Ne.symm hij)] at hN
  have h1 : D ∩ S' j = S' j := Finset.inter_eq_right.mpr Finset.subset_union_right
  have h2 : D \ S' j ⊆ X := by
    intro e he
    rw [Finset.mem_sdiff, hD, Finset.mem_union] at he
    tauto
  have h3 := pu_setCost_mono c hc h2
  have h4 : setCost c X ≤ setCost c (S i \ S j) + setCost c (S j \ S i) := by
    have := Finset.sum_union_inter (s₁ := S i \ S j) (s₂ := S j \ S i) (f := c)
    have h5 := pu_setCost_nonneg c hc ((S i \ S j) ∩ (S j \ S i))
    unfold setCost at *
    rw [hX]; linarith
  have h6 := pu_setCost_split c (S' j) (S' i)
  rw [h1] at hN
  rw [Finset.inter_comm (S' j) (S' i)] at h6
  linarith

theorem deviation_inequality_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 1 \ S' 0) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 ∧
      setCost c (S' 1 \ S' 0) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 0 \ S' 1) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 := by
  have a := pu_dev G c s t hc S S' hS hS' 0 1 (by decide)
  have b := pu_dev G c s t hc S S' hS hS' 1 0 (by decide)
  rw [Finset.inter_comm (S' 1) (S' 0)] at b
  constructor <;> linarith

theorem ineq_4_2_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) / 2 + setCost c (S' 1 \ S' 0) / 2 ≤
      2 * setCost c (S 0 \ S 1) + 2 * setCost c (S 1 \ S 0) := by
  have h := deviation_inequality_core G c s t hc S S' hS hS'
  linarith [h.1, h.2]


section Three

lemma tn_first_edge {W : Type*} (F : Set (Sym2 W)) {u v : W}
    (h : (SimpleGraph.fromEdgeSet F).Reachable u v) (huv : u ≠ v) :
    ∃ w, s(u, w) ∈ F ∧ u ≠ w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl huv
  | cons h q =>
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact ⟨_, h.1, h.2⟩

lemma tn_cost_out (ε : ℝ) (e : Sym2 (Fin 3)) (h : e ∉ ({s(0, 1), s(0, 2), s(1, 2)} : Finset _)) :
    threeNodeCost ε e = 0 := by
  unfold threeNodeCost
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  rw [if_neg (by tauto), if_neg h.2.2]

lemma tn_ca (ε : ℝ) : threeNodeCost ε s(0, 1) = 2 := by
  unfold threeNodeCost; rw [if_pos (Or.inl rfl)]
lemma tn_cb (ε : ℝ) : threeNodeCost ε s(0, 2) = 2 := by
  unfold threeNodeCost; rw [if_pos (Or.inr rfl)]
lemma tn_cd (ε : ℝ) : threeNodeCost ε s(1, 2) = 1 + ε := by
  unfold threeNodeCost; rw [if_neg (by decide), if_pos rfl]

lemma tn_setCost (ε : ℝ) (F : Finset (Sym2 (Fin 3))) :
    setCost (threeNodeCost ε) F = (if s(0, 1) ∈ F then 2 else 0) + (if s(0, 2) ∈ F then 2 else 0)
      + (if s(1, 2) ∈ F then 1 + ε else 0) := by
  unfold setCost
  rw [← Finset.sum_subset (Finset.inter_subset_left (s₁ := F) (s₂ := {s(0, 1), s(0, 2), s(1, 2)}))
    (fun e he he' => by
      apply tn_cost_out
      intro h; exact he' (Finset.mem_inter.mpr ⟨he, h⟩)),
    Finset.inter_comm, ← Finset.sum_ite_mem]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    tn_ca, tn_cb, tn_cd]
  ring

lemma tn_strat (ε : ℝ) (k : Fin 2) (T : Finset (Sym2 (Fin 3))) :
    T ∈ (threeNode ε).strategies k ↔ T ∈ connStrategies ⊤ 0 ![1, 2] k := Iff.rfl

lemma tn_strat0 (ε : ℝ) (T : Finset (Sym2 (Fin 3))) (hT : T ∈ (threeNode ε).strategies 0) :
    s(0, 1) ∈ T ∨ (s(0, 2) ∈ T ∧ s(1, 2) ∈ T) := by
  rw [tn_strat, pu_mem_conn] at hT
  have hr := hT.2
  simp only [Matrix.cons_val_zero] at hr
  obtain ⟨w, hw, hne⟩ := tn_first_edge _ hr (by decide)
  obtain ⟨w', hw', hne'⟩ := tn_first_edge _ hr.symm (by decide)
  have e1 : s((1 : Fin 3), 0) = s(0, 1) := Sym2.eq_swap
  have e2 : s((2 : Fin 3), 0) = s(0, 2) := Sym2.eq_swap
  have e3 : s((2 : Fin 3), 1) = s(1, 2) := Sym2.eq_swap
  have hw3 : w = 0 ∨ w = 1 ∨ w = 2 := by fin_cases w <;> simp
  have hw3' : w' = 0 ∨ w' = 1 ∨ w' = 2 := by fin_cases w' <;> simp
  rcases hw3 with rfl | rfl | rfl <;> rcases hw3' with rfl | rfl | rfl <;>
    (try simp only [e1, e2, e3] at hw hw') <;> simp_all

lemma tn_strat1 (ε : ℝ) (T : Finset (Sym2 (Fin 3))) (hT : T ∈ (threeNode ε).strategies 1) :
    s(0, 2) ∈ T ∨ (s(0, 1) ∈ T ∧ s(1, 2) ∈ T) := by
  rw [tn_strat, pu_mem_conn] at hT
  have hr : (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin 3)))).Reachable (2 : Fin 3) 0 := by
    simpa using hT.2
  obtain ⟨w, hw, hne⟩ := tn_first_edge _ hr (by decide)
  obtain ⟨w', hw', hne'⟩ := tn_first_edge _ hr.symm (by decide)
  have e1 : s((1 : Fin 3), 0) = s(0, 1) := Sym2.eq_swap
  have e2 : s((2 : Fin 3), 0) = s(0, 2) := Sym2.eq_swap
  have e3 : s((2 : Fin 3), 1) = s(1, 2) := Sym2.eq_swap
  have hw3 : w = 0 ∨ w = 1 ∨ w = 2 := by fin_cases w <;> simp
  have hw3' : w' = 0 ∨ w' = 1 ∨ w' = 2 := by fin_cases w' <;> simp
  rcases hw3 with rfl | rfl | rfl <;> rcases hw3' with rfl | rfl | rfl <;>
    (try simp only [e1, e2, e3] at hw hw') <;> simp_all

lemma tn_adj (T : Finset (Sym2 (Fin 3))) (x y : Fin 3) (h : s(x, y) ∈ T) (hxy : x ≠ y) :
    (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin 3)))).Reachable x y := by
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨h, hxy⟩

lemma tn_sub (T : Finset (Sym2 (Fin 3))) (hT : T ⊆ {s(0, 1), s(0, 2), s(1, 2)}) :
    (T : Set (Sym2 (Fin 3))) ⊆ (⊤ : SimpleGraph (Fin 3)).edgeSet := by
  intro e he
  have := hT he
  rw [SimpleGraph.edgeSet_top]
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl <;> decide


lemma tn_cost (ε : ℝ) (S : Fin 2 → Finset (Sym2 (Fin 3))) (i j : Fin 2) (hij : i ≠ j) :
    cost (threeNode ε) S i =
      setCost (threeNodeCost ε) (S i \ S j) + setCost (threeNodeCost ε) (S i ∩ S j) / 2 :=
  pu_cost ⊤ (threeNodeCost ε) 0 ![1, 2] S i j hij

lemma tn_mem_strat0 (ε : ℝ) (T : Finset (Sym2 (Fin 3))) (hT : T ⊆ {s(0, 1), s(0, 2), s(1, 2)})
    (h : s(0, 1) ∈ T ∨ (s(0, 2) ∈ T ∧ s(1, 2) ∈ T)) : T ∈ (threeNode ε).strategies 0 := by
  rw [tn_strat, pu_mem_conn]
  refine ⟨tn_sub T hT, ?_⟩
  show (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin 3)))).Reachable (1 : Fin 3) 0
  rcases h with h | ⟨h1, h2⟩
  · exact (tn_adj T 0 1 h (by decide)).symm
  · exact (tn_adj T 1 2 h2 (by decide)).trans (tn_adj T 0 2 h1 (by decide)).symm

lemma tn_mem_strat1 (ε : ℝ) (T : Finset (Sym2 (Fin 3))) (hT : T ⊆ {s(0, 1), s(0, 2), s(1, 2)})
    (h : s(0, 2) ∈ T ∨ (s(0, 1) ∈ T ∧ s(1, 2) ∈ T)) : T ∈ (threeNode ε).strategies 1 := by
  rw [tn_strat, pu_mem_conn]
  refine ⟨tn_sub T hT, ?_⟩
  show (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin 3)))).Reachable (2 : Fin 3) 0
  rcases h with h | ⟨h1, h2⟩
  · exact (tn_adj T 0 2 h (by decide)).symm
  · exact (tn_adj T 1 2 h2 (by decide)).symm.trans (tn_adj T 0 1 h1 (by decide)).symm

theorem three_node_core (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
    (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
    (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
    (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨![{s(0, 1)}, {s(0, 2)}], ⟨?_, ?_⟩, ?_⟩
    · intro k
      fin_cases k
      · exact tn_mem_strat0 ε _ (by simp) (Or.inl (by simp))
      · exact tn_mem_strat1 ε _ (by simp) (Or.inl (by simp))
    · intro k T hT
      fin_cases k
      · have h := tn_strat0 ε T hT
        simp only [Fin.zero_eta, Fin.isValue]
        rw [tn_cost ε _ 0 1 (by decide), tn_cost ε _ 0 1 (by decide)]
        simp only [Function.update_self, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
          Function.update_of_ne, Matrix.cons_val_zero, Matrix.cons_val_one, tn_setCost]
        by_cases ha : s(0, 1) ∈ T <;> by_cases hb : s(0, 2) ∈ T <;> by_cases hd : s(1, 2) ∈ T <;>
          simp_all <;> linarith
      · have h := tn_strat1 ε T hT
        simp only [Fin.mk_one, Fin.isValue]
        rw [tn_cost ε _ 1 0 (by decide), tn_cost ε _ 1 0 (by decide)]
        simp only [Function.update_self, Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true,
          Function.update_of_ne, Matrix.cons_val_zero, Matrix.cons_val_one, tn_setCost]
        by_cases ha : s(0, 1) ∈ T <;> by_cases hb : s(0, 2) ∈ T <;> by_cases hd : s(1, 2) ∈ T <;>
          simp_all <;> linarith
    · rw [pu_designCost, tn_setCost]
      simp
      norm_num
  · intro S hS
    have h0 := hS.2 0 {s(0, 1)} (tn_mem_strat0 ε _ (by simp) (Or.inl (by simp)))
    have h1 := hS.2 1 {s(0, 2)} (tn_mem_strat1 ε _ (by simp) (Or.inl (by simp)))
    have c0 := tn_strat0 ε _ (hS.1 0)
    have c1 := tn_strat1 ε _ (hS.1 1)
    rw [tn_cost ε _ 0 1 (by decide), tn_cost ε _ 0 1 (by decide)] at h0
    rw [tn_cost ε _ 1 0 (by decide), tn_cost ε _ 1 0 (by decide)] at h1
    simp only [Function.update_self, Fin.isValue, ne_eq, one_ne_zero, zero_ne_one,
      not_false_eq_true, Function.update_of_ne, tn_setCost] at h0 h1
    rw [pu_designCost, tn_setCost]
    by_cases ha0 : s(0, 1) ∈ S 0 <;> by_cases hb0 : s(0, 2) ∈ S 0 <;>
      by_cases hd0 : s(1, 2) ∈ S 0 <;> by_cases ha1 : s(0, 1) ∈ S 1 <;>
      by_cases hb1 : s(0, 2) ∈ S 1 <;> by_cases hd1 : s(1, 2) ∈ S 1 <;>
      simp_all <;> linarith
  · refine ⟨![{s(0, 1), s(1, 2)}, {s(0, 1), s(1, 2)}], ?_, ?_⟩
    · intro k
      fin_cases k
      · exact tn_mem_strat0 ε _ (by intro e; simp; tauto) (Or.inl (by simp))
      · exact tn_mem_strat1 ε _ (by intro e; simp; tauto) (Or.inr ⟨by simp, by simp⟩)
    · rw [pu_designCost, tn_setCost]
      simp
      norm_num
      ring
  · intro P hP
    have c0 := tn_strat0 ε _ (hP 0)
    have c1 := tn_strat1 ε _ (hP 1)
    rw [pu_designCost, tn_setCost]
    by_cases ha0 : s(0, 1) ∈ P 0 <;> by_cases hb0 : s(0, 2) ∈ P 0 <;>
      by_cases hd0 : s(1, 2) ∈ P 0 <;> by_cases ha1 : s(0, 1) ∈ P 1 <;>
      by_cases hb1 : s(0, 2) ∈ P 1 <;> by_cases hd1 : s(1, 2) ∈ P 1 <;>
      simp_all <;> linarith

end Three


lemma pu_exists_minimal (G : SimpleGraph V) (s : V) (t : Fin 2 → V) (i : Fin 2)
    (T : Finset (Sym2 V)) (hT : T ∈ connStrategies G s t i) :
    ∃ Q ⊆ T, IsMinimalStrategy G s t i Q := by
  classical
  set F := (connStrategies G s t i).filter (· ⊆ T)
  have hF : T ∈ F := Finset.mem_filter.mpr ⟨hT, subset_rfl⟩
  obtain ⟨Q, hQ, hmin⟩ := Finset.exists_min_image F Finset.card ⟨T, hF⟩
  rw [Finset.mem_filter] at hQ
  refine ⟨Q, hQ.2, hQ.1, fun Q' hQ' hmem => ?_⟩
  have h1 := hmin Q' (Finset.mem_filter.mpr ⟨hmem, hQ'.subset.trans hQ.2⟩)
  have h2 := Finset.card_lt_card hQ'
  omega

theorem pos_general {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (hex : ∃ P, IsProfile (twoPlayerGame G c s t) P) :
    ∃ S, IsPureNash (twoPlayerGame G c s t) S ∧
      ∀ P, IsProfile (twoPlayerGame G c s t) P →
        PriceOfStability.Harmonic.designCost (fun e _ => c e) S ≤
          4 / 3 * PriceOfStability.Harmonic.designCost (fun e _ => c e) P := by
  obtain ⟨P0, hP0⟩ := hex
  obtain ⟨S, hN, hmin⟩ := pu_exists_nash_min G c s t P0 hP0
  refine ⟨S, hN, fun P hP => ?_⟩
  have hQ : ∀ i, ∃ Q ⊆ P i, IsMinimalStrategy G s t i Q :=
    fun i => pu_exists_minimal G s t i (P i) (hP i)
  choose Q hQsub hQmin using hQ
  have hQprof : IsProfile (twoPlayerGame G c s t) Q := fun i => (hQmin i).1
  have h1 := hmin Q hQprof
  have h2 := ineq_4_2_core G c s t hc Q S hQmin hN
  have h3 : setCost c (Q 0 ∪ Q 1) ≤ setCost c (P 0 ∪ P 1) :=
    pu_setCost_mono c hc (Finset.union_subset_union (hQsub 0) (hQsub 1))
  rw [pu_designCost, pu_designCost]
  rw [pu_setCost_union] at h3 ⊢
  unfold pot at h1
  have n1 := pu_setCost_nonneg c hc (S 0 ∩ S 1)
  have n2 := pu_setCost_nonneg c hc (Q 0 \ Q 1)
  have n3 := pu_setCost_nonneg c hc (Q 1 \ Q 0)
  have n4 := pu_setCost_nonneg c hc (Q 0 ∩ Q 1)
  linarith

theorem two_player_pos_core :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V)
        (t : Fin 2 → V), (∀ e, 0 ≤ c e) →
        (∃ P, IsProfile (twoPlayerGame G c s t) P) →
        ∃ S, IsPureNash (twoPlayerGame G c s t) S ∧
          ∀ P, IsProfile (twoPlayerGame G c s t) P →
            PriceOfStability.Harmonic.designCost (fun e _ => c e) S ≤ 4 / 3 * PriceOfStability.Harmonic.designCost (fun e _ => c e) P) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
      (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
      (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
      (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P)) :=
  ⟨fun G c s t hc hex => pos_general G c s t hc hex, fun ε h1 h2 => three_node_core ε h1 h2⟩

end Base
end PriceOfStability.Undirected

open PriceOfStability.Undirected


theorem solution (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
    (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
    (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
    (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P) := by
  exact three_node_core ε hε hε1
