-- Prove2me | solution 1 for PoAIndep.Topology.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:15:43.018459+00:00
-- url     : https://prove2.me/submissions/c9ccd6fd-6303-47dc-bb07-6af9317b5660

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
open PoAIndep.Topology
open Filter Topology
set_option maxHeartbeats 800000

private theorem edge_nonneg {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I)
    (hf : ∀ i P, 0 ≤ f i P) (e : E) : 0 ≤ edgeFlow I f e := by
  unfold edgeFlow Finsupp.sum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro P _
  dsimp only
  split_ifs <;> simp [hf]

private theorem moved_nonneg {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f)
    (i : Fin I.k) (P Q : List E) (δ : ℝ) (hd : δ ∈ Set.Icc 0 (f i P)) :
    ∀ j R, 0 ≤ Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ) j R := by
  intro j R
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Finsupp.add_apply, Finsupp.sub_apply]
    by_cases hP : P = R
    · subst R
      by_cases hQ : Q = P <;> simp [hQ] <;> linarith [hd.1, hd.2, (hf i).1 P]
    · by_cases hQ : Q = R <;> simp [hP, hQ] <;> linarith [hd.1, (hf i).1 R]
  · simpa [Function.update_of_ne hj] using (hf j).1 R

private theorem edge_affine {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I)
    (i : Fin I.k) (P Q : List E) (δ : ℝ) (e : E) :
    edgeFlow I (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ)) e =
      edgeFlow I f e - (if e ∈ P then δ else 0) + (if e ∈ Q then δ else 0) := by
  classical
  have hs (g h : List E →₀ ℝ) :
      (g+h).sum (fun R a => if e ∈ R then a else 0) =
        g.sum (fun R a => if e ∈ R then a else 0) +
        h.sum (fun R a => if e ∈ R then a else 0) := by
    apply Finsupp.sum_add_index' <;> intros <;> split_ifs <;> simp
  have ht (g h : List E →₀ ℝ) :
      (g-h).sum (fun R a => if e ∈ R then a else 0) =
        g.sum (fun R a => if e ∈ R then a else 0) -
        h.sum (fun R a => if e ∈ R then a else 0) := by
    apply Finsupp.sum_sub_index <;> intros <;> split_ifs <;> simp
  unfold edgeFlow
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, hs, ht]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ) j).sum
        (fun R a => if e ∈ R then a else 0) =
      ∑ j ∈ Finset.univ.erase i, (f j).sum (fun R a => if e ∈ R then a else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hrest]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  ring

private theorem shortest {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f)
    (hn : IsNashFlow I f) (i : Fin I.k) (P Q : List E)
    (hP : IsSimplePath I.src I.tgt P (I.s i) (I.t i))
    (hQ : IsSimplePath I.src I.tgt Q (I.s i) (I.t i)) (hp : 0 < f i P) :
    pathLatency I f P ≤ pathLatency I f Q := by
  let S := Set.Icc (0 : ℝ) (f i P)
  let a := fun δ e => edgeFlow I f e - (if e ∈ P then δ else 0) + (if e ∈ Q then δ else 0)
  have ha (e : E) : Continuous (fun δ => a δ e) := by
    dsimp [a]
    apply Continuous.add
    · apply Continuous.sub continuous_const
      split_ifs <;> fun_prop
    · split_ifs <;> fun_prop
  have hnon (δ : ℝ) (hd : δ ∈ S) (e : E) : 0 ≤ a δ e := by
    dsimp only [a]
    rw [← edge_affine I f i P Q δ e]
    exact edge_nonneg I _ (moved_nonneg I f hf i P Q δ hd) e
  have hc (e : E) : ContinuousOn (fun δ => I.ℓ e (a δ e)) S :=
    (I.latency e).2.1.continuousOn.comp (ha e).continuousOn (fun δ hd => hnon δ hd e)
  have hsum : ContinuousOn (fun δ => (Q.map fun e => I.ℓ e (a δ e)).sum) S := by
    have hall : ∀ R : List E, ContinuousOn (fun δ => (R.map fun e => I.ℓ e (a δ e)).sum) S := by
      intro R
      induction R with
      | nil => simpa using continuousOn_const
      | cons e R ih => simpa [Pi.add_def] using (hc e).add ih
    exact hall Q
  have ht := (hsum.continuousWithinAt (show (0 : ℝ) ∈ S from ⟨le_rfl, hp.le⟩)).mono
    Set.Ioc_subset_Icc_self
  letI := left_nhdsWithin_Ioc_neBot hp
  have hineq : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioc 0 (f i P)),
      pathLatency I f P ≤ (Q.map fun e => I.ℓ e (a δ e)).sum := by
    filter_upwards [self_mem_nhdsWithin] with δ hd
    have hh := hn i P Q hP hQ hp δ hd
    simpa [pathLatency, edge_affine, a] using hh
  have hh := ge_of_tendsto ht hineq
  simpa [a, pathLatency] using hh

theorem PoAIndep.Topology.proposition_2_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) :
    IsNashFlow I f ↔
      ∀ (i : Fin I.k) (P₁ P₂ : List E),
        IsSimplePath I.src I.tgt P₁ (I.s i) (I.t i) →
        IsSimplePath I.src I.tgt P₂ (I.s i) (I.t i) →
        0 < f i P₁ → pathLatency I f P₁ ≤ pathLatency I f P₂ := by
  constructor
  · intro hn i P Q hP hQ hp
    exact shortest I f hf hn i P Q hP hQ hp
  · intro hs i P Q hP hQ hp δ hd
    apply le_trans (hs i P Q hP hQ hp)
    unfold pathLatency
    apply List.sum_le_sum
    intro e he
    apply (I.latency e).2.2 (edge_nonneg I f (fun i => (hf i).1) e)
      (edge_nonneg I _ (moved_nonneg I f hf i P Q δ ⟨hd.1.le, hd.2⟩) e)
    rw [edge_affine]
    simp only [he, ite_true]
    split_ifs <;> linarith [hd.1]

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) :
    IsNashFlow I f ↔
      ∀ (i : Fin I.k) (P₁ P₂ : List E),
        IsSimplePath I.src I.tgt P₁ (I.s i) (I.t i) →
        IsSimplePath I.src I.tgt P₂ (I.s i) (I.t i) →
        0 < f i P₁ → pathLatency I f P₁ ≤ pathLatency I f P₂ := PoAIndep.Topology.proposition_2_2 I f hf

#print axioms solution

