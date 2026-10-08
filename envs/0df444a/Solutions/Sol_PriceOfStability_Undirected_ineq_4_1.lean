-- Prove2me | solution 1 for PriceOfStability.Undirected.ineq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:17:28.897391+00:00
-- url     : https://prove2.me/submissions/44398718-dbca-430b-9290-75e2d60fa7a5

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



theorem ineq_4_1_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (S : Fin 2 → Finset (Sym2 V))
    (hS : IsProfile (twoPlayerGame G c s t) S) :
    ∃ S' : Fin 2 → Finset (Sym2 V), IsPureNash (twoPlayerGame G c s t) S' ∧
      setCost c (S' 0 \ S' 1) + setCost c (S' 1 \ S' 0) + 3 / 2 * setCost c (S' 0 ∩ S' 1) ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + 3 / 2 * setCost c (S 0 ∩ S 1) := by
  obtain ⟨S', h1, h2⟩ := pu_exists_nash_min G c s t S hS
  exact ⟨S', h1, h2 S hS⟩

end Base
end PriceOfStability.Undirected

open PriceOfStability.Undirected


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e) (S : Fin 2 → Finset (Sym2 V))
    (hS : IsProfile (twoPlayerGame G c s t) S) :
    ∃ S' : Fin 2 → Finset (Sym2 V), IsPureNash (twoPlayerGame G c s t) S' ∧
      setCost c (S' 0 \ S' 1) + setCost c (S' 1 \ S' 0) + 3 / 2 * setCost c (S' 0 ∩ S' 1) ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + 3 / 2 * setCost c (S 0 ∩ S 1) := by
  exact ineq_4_1_core G c s t S hS
