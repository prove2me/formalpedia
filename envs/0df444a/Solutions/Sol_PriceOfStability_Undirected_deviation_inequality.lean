-- Prove2me | solution 1 for PriceOfStability.Undirected.deviation_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:21:25.543141+00:00
-- url     : https://prove2.me/submissions/de55685a-764d-4081-a067-00c1524baa12

import Definitions.Def_PriceOfStability_Undirected_ThreeNode
import Definitions.Def_PriceOfStability_Undirected_Model
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

end Base
end PriceOfStability.Undirected

open PriceOfStability.Undirected


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 1 \ S' 0) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 ∧
      setCost c (S' 1 \ S' 0) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 0 \ S' 1) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 := by
  exact deviation_inequality_core G c s t hc S S' hS hS'
