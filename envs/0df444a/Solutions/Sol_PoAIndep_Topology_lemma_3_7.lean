-- Prove2me | solution 1 for PoAIndep.Topology.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:20:24.779588+00:00
-- url     : https://prove2.me/submissions/ae3e70ae-c701-4562-b275-026a5e7f7a08

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

private theorem path_sum {E : Type} [Fintype E] [DecidableEq E] (P : List E)
    (hP : P.Nodup) (w : E → ℝ) :
    (∑ e, if e ∈ P then w e else 0) = (P.map w).sum := by
  induction P with
  | nil => simp
  | cons a P ih =>
    have hn := List.nodup_cons.mp hP
    have he (e : E) : (if e ∈ a :: P then w e else 0) =
        (if e = a then w e else 0) + (if e ∈ P then w e else 0) := by
      by_cases h : e = a
      · subst e; simp [hn.1]
      · simp [h]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih hn.2]
    simp

private theorem edge_path {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) (w : E → ℝ) :
    (∑ e, w e * edgeFlow I f e) =
      ∑ i, (f i).sum (fun P a => (P.map w).sum * a) := by
  classical
  unfold edgeFlow Finsupp.sum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  have hn : P.Nodup := ((hf i).2 P hP).2.2.2.2.of_cons.of_map
  have he (e : E) : w e * (if e ∈ P then f i P else 0) =
      (if e ∈ P then w e else 0) * f i P := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul, path_sum P hn]

private theorem fixed_min {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f g : Flow I) (hf : IsFlow I f)
    (hfeas : IsFeasible I f) (hnash : IsNashFlow I f)
    (hg : IsFlow I g) (hgfeas : IsFeasible I g) :
    ∑ i, (f i).sum (fun P a => pathLatency I f P * a) ≤
      ∑ i, (g i).sum (fun P a => pathLatency I f P * a) := by
  classical
  have hex (i : Fin I.k) : ∃ P, 0 < f i P := by
    by_contra h
    have hz : (f i).sum (fun _ x => x) ≤ 0 := by
      unfold Finsupp.sum
      exact Finset.sum_nonpos (fun P _ => le_of_not_gt (fun hh => h ⟨P,hh⟩))
    rw [hfeas i] at hz
    linarith [I.r_pos i]
  choose P hP using hex
  apply Finset.sum_le_sum
  intro i _
  let Lc := pathLatency I f (P i)
  have hs (R : List E) (hr : 0 < f i R) :=
    (hf i).2 R (Finsupp.mem_support_iff.mpr (ne_of_gt hr))
  have he (R : List E) (hr : 0 < f i R) : pathLatency I f R = Lc :=
    le_antisymm (shortest I f hf hnash i R (P i) (hs R hr) (hs (P i) (hP i)) hr)
      (shortest I f hf hnash i (P i) R (hs (P i) (hP i)) (hs R hr) (hP i))
  have hleft : (f i).sum (fun R a => pathLatency I f R * a) = Lc * I.r i := by
    rw [← hfeas i]
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    dsimp only
    rw [he R (lt_of_le_of_ne ((hf i).1 R) (Ne.symm (Finsupp.mem_support_iff.mp hR)))]
  rw [hleft, ← hgfeas i]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact mul_le_mul_of_nonneg_right
    (shortest I f hf hnash i (P i) R (hs (P i) (hP i)) ((hg i).2 R hR) (hP i))
    ((hg i).1 R)

theorem PoAIndep.Topology.lemma_3_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f g : Flow I) (hf : IsFlow I f) (hfeas : IsFeasible I f)
    (hnash : IsNashFlow I f) (hg : IsFlow I g) (hgfeas : IsFeasible I g) :
    ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e ≤
      ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I g e := by
  rw [edge_path I f hf, edge_path I g hg]
  exact fixed_min I f g hf hfeas hnash hg hgfeas

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f g : Flow I) (hf : IsFlow I f) (hfeas : IsFeasible I f)
    (hnash : IsNashFlow I f) (hg : IsFlow I g) (hgfeas : IsFeasible I g) :
    ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e ≤
      ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I g e :=
  PoAIndep.Topology.lemma_3_7 I f g hf hfeas hnash hg hgfeas

#print axioms solution
