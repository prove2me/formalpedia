-- Prove2me | solution 1 for UniformADProbes.Trace.distance_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:33:39.563381+00:00
-- url     : https://prove2.me/submissions/e1e0fcd2-0da5-4cdc-85e8-5463ce6e2d32

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

section
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.Dist
open UniformADProbes.Trace

section eval
variable {R : Type} [Ring R]

def fmon (H K : R) : Bool → R := fun b => if b then K else H

lemma wordEval_eq (H K : R) (w : Word) : wordEval H K w = FreeMonoid.lift (fmon H K) w := by
  simp [wordEval, FreeMonoid.lift_apply, List.prod_eq_foldr, fmon, List.foldr_map]

noncomputable def ev (H K : R) : NCPoly →ₐ[ℤ] R :=
  MonoidAlgebra.lift ℤ R Word (FreeMonoid.lift (fmon H K))

lemma polyEval_eq_ev (H K : R) (p : NCPoly) : polyEval H K p = ev H K p := by
  rw [ev, MonoidAlgebra.lift_apply]
  simp [polyEval, wordEval_eq]

lemma polyEval_x (H K : R) : polyEval H K x = H := by
  simp [polyEval, x, wordEval]

lemma polyEval_y (H K : R) : polyEval H K y = K := by
  simp [polyEval, y, wordEval]

lemma wordEval_map {S : Type} [Ring S] (φ : R →+* S) (H K : R) (w : Word) :
    φ (wordEval H K w) = wordEval (φ H) (φ K) w := by
  unfold wordEval
  induction w.toList with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, map_mul, ih]
    cases b <;> simp

lemma polyEval_map {S : Type} [Ring S] (φ : R →+* S) (H K : R) (p : NCPoly) :
    φ (polyEval H K p) = polyEval (φ H) (φ K) p := by
  unfold polyEval
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [map_zsmul, wordEval_map]

end eval

section tree
open scoped Classical
variable {n : ℕ} {T : SimpleGraph (Fin n)}

lemma step (hT : T.IsTree) (v a b : Fin n) (hab : T.Adj a b) :
    T.dist b v = T.dist a v + 1 ∨ T.dist a v = T.dist b v + 1 := by
  have := hT.dist_eq_dist_add_one_of_adj v hab
  rw [SimpleGraph.dist_comm (u := v) (v := a), SimpleGraph.dist_comm (u := v) (v := b)] at this
  omega

lemma exists_closer (hT : T.IsTree) {u v : Fin n} (huv : u ≠ v) :
    ∃ w, T.Adj u w ∧ T.dist w v + 1 = T.dist u v := by
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist u v
  cases p with
  | nil => exact absurd rfl huv
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    have hle : T.dist w v ≤ q.length := SimpleGraph.dist_le q
    have := step hT v u w h
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

lemma unique_closer (hT : T.IsTree) {u v w1 w2 : Fin n}
    (h1 : T.Adj u w1) (d1 : T.dist w1 v + 1 = T.dist u v)
    (h2 : T.Adj u w2) (d2 : T.dist w2 v + 1 = T.dist u v) : w1 = w2 := by
  obtain ⟨q1, hq1⟩ := hT.connected.exists_walk_length_eq_dist w1 v
  obtain ⟨q2, hq2⟩ := hT.connected.exists_walk_length_eq_dist w2 v
  have p1 : (SimpleGraph.Walk.cons h1 q1).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by simp [hq1, d1])
  have p2 : (SimpleGraph.Walk.cons h2 q2).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by simp [hq2, d2])
  have := (hT.existsUnique_path u v).unique p1 p2
  have h3 := congrArg SimpleGraph.Walk.snd this
  simpa using h3

lemma adj_apply (i j : Fin n) : adjacency T i j = if T.Adj i j then 1 else 0 := by
  unfold adjacency; rfl

lemma deg_eq (u : Fin n) :
    degreeMatrix T u u = ((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) := by
  unfold degreeMatrix
  simp only [Matrix.diagonal_apply_eq]
  have : T.neighborSet u = ↑(Finset.univ.filter (fun w => T.Adj u w)) := by
    ext w; simp
  rw [this, Set.ncard_coe_finset]

noncomputable def F (T : SimpleGraph (Fin n)) (k : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if T.dist i j = k then 1 else 0

lemma AF (hT : T.IsTree) (m : ℕ) (u v : Fin n) :
    (adjacency T * F T m) u v =
      if u = v then (if m = 1 then ((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) else 0)
      else ((if m + 1 = T.dist u v then 1 else 0) +
        (if m = T.dist u v + 1 then
          (((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) - 1) else 0)) := by
  rw [Matrix.mul_apply]
  simp only [adj_apply, F]
  by_cases huv : u = v
  · subst huv
    simp only [if_true]
    have : ∀ w : Fin n, ((if T.Adj u w then (1:ℤ) else 0) * (if T.dist w u = m then 1 else 0)) =
        if T.Adj u w then (if m = 1 then 1 else 0) else 0 := by
      intro w
      by_cases hw : T.Adj u w
      · have : T.dist w u = 1 := by
          rw [SimpleGraph.dist_comm]; exact (SimpleGraph.dist_eq_one_iff_adj).2 hw
        simp [hw, this, eq_comm]
      · simp [hw]
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const]
    by_cases hm : m = 1 <;> simp [hm]
  · obtain ⟨c, hc1, hc2⟩ := exists_closer hT huv
    simp only [huv, if_false]
    set S := Finset.univ.filter (fun w => T.Adj u w) with hS
    have hcS : c ∈ S := by simp [hS, hc1]
    have key : ∀ w : Fin n, ((if T.Adj u w then (1:ℤ) else 0) * (if T.dist w v = m then 1 else 0)) =
        (if w = c then (if m + 1 = T.dist u v then (1:ℤ) else 0) else 0) +
        (if w ∈ S.erase c then (if m = T.dist u v + 1 then (1:ℤ) else 0) else 0) := by
      intro w
      by_cases hw : T.Adj u w
      · have hwS : w ∈ S := by simp [hS, hw]
        by_cases hwc : w = c
        · subst hwc
          simp [hw, hc2]
          by_cases hh : m + 1 = T.dist u v
          · simp [hh]; omega
          · simp [hh]; omega
        · have : T.dist w v = T.dist u v + 1 := by
            rcases step hT v u w hw with h | h
            · exact h
            · exfalso; apply hwc
              apply unique_closer hT hw _ hc1 hc2
              omega
          simp [hw, hwc, hwS, this]
          omega
      · have hwc : w ≠ c := fun h => hw (h ▸ hc1)
        have : w ∉ S := by simp [hS, hw]
        simp [hw, hwc, this]
    simp only [key]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_erase_of_mem hcS]
    have h1 : 1 ≤ S.card := Finset.card_pos.2 ⟨c, hcS⟩
    by_cases hm : m = T.dist u v + 1
    · simp [hm]; omega
    · simp [hm]

lemma Dmul (X : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) :
    (degreeMatrix T * X) u v =
      ((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) * X u v := by
  have h := deg_eq (T := T) u
  rw [← h]
  unfold degreeMatrix
  rw [Matrix.diagonal_mul]
  simp

lemma F_zero (hT : T.IsTree) : F T 0 = 1 := by
  ext u v
  simp only [F, Matrix.one_apply]
  simp [(hT.connected u v).dist_eq_zero_iff]

lemma F_one : F T 1 = adjacency T := by
  ext u v
  simp only [F, adj_apply]
  simp [SimpleGraph.dist_eq_one_iff_adj]

lemma D_apply (u v : Fin n) : degreeMatrix T u v =
    if u = v then ((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) else 0 := by
  by_cases huv : u = v
  · subst huv; simp [deg_eq]
  · simp only [huv, if_false]; unfold degreeMatrix; simp [Matrix.diagonal_apply, huv]

lemma F_two (hT : T.IsTree) : adjacency T * adjacency T - degreeMatrix T = F T 2 := by
  ext u v
  have h1 := AF hT 1 u v
  rw [F_one] at h1
  rw [Matrix.sub_apply, h1, D_apply]
  simp only [F]
  by_cases huv : u = v
  · subst huv; simp
  · have hd : T.dist u v ≠ 0 := fun h => huv ((hT.connected u v).dist_eq_zero_iff.1 h)
    simp only [huv, if_false]
    split_ifs <;> omega

lemma F_rec (hT : T.IsTree) (k : ℕ) :
    adjacency T * F T (k + 2) - (degreeMatrix T - 1) * F T (k + 1) = F T (k + 3) := by
  ext u v
  rw [Matrix.sub_apply, AF hT, Matrix.sub_mul, Matrix.sub_apply, Dmul, Matrix.one_mul]
  simp only [F]
  by_cases huv : u = v
  · subst huv; simp
  · have hd : T.dist u v ≠ 0 := fun h => huv ((hT.connected u v).dist_eq_zero_iff.1 h)
    simp only [huv, if_false]
    split_ifs <;> first | omega | (push_cast; ring) | (simp_all; omega)

lemma ev_x (H K : Matrix (Fin n) (Fin n) ℤ) : ev H K x = H := by
  rw [← polyEval_eq_ev, polyEval_x]

lemma ev_y (H K : Matrix (Fin n) (Fin n) ℤ) : ev H K y = K := by
  rw [← polyEval_eq_ev, polyEval_y]

lemma ev_dp_aux (hT : T.IsTree) (k : ℕ) :
    ev (adjacency T) (degreeMatrix T) (distancePoly k) = F T k ∧
    ev (adjacency T) (degreeMatrix T) (distancePoly (k + 1)) = F T (k + 1) ∧
    ev (adjacency T) (degreeMatrix T) (distancePoly (k + 2)) = F T (k + 2) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [distancePoly, F_zero hT]
    · simp [distancePoly, ev_x, F_one]
    · simp [distancePoly, ev_x, ev_y, F_two hT]
  | succ k ih =>
    obtain ⟨_, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    have : distancePoly (k + 1 + 2) = x * distancePoly (k + 2) - (y - 1) * distancePoly (k + 1) := rfl
    rw [this, map_sub, map_mul, map_mul, map_sub, map_one, ev_x, ev_y, h1, h2]
    exact F_rec hT k

lemma ev_sum (hT : T.IsTree) (N : ℕ) :
    ev (adjacency T) (degreeMatrix T) (distanceSum N) = ∑ k ∈ Finset.range N, F T k := by
  induction N with
  | zero => simp [distanceSum]
  | succ N ih =>
    have : distanceSum (N + 1) = distanceSum N + distancePoly N := by
      simp [distanceSum, List.range_succ]
    rw [this, map_add, ih, Finset.sum_range_succ, (ev_dp_aux hT N).1]

lemma dist_lt (hT : T.IsTree) (u v : Fin n) : T.dist u v < n := by
  obtain ⟨p, hp, hl⟩ := (hT.connected u v).exists_path_of_dist
  have := hp.length_lt
  simpa [hl] using this

lemma ones_sum (hT : T.IsTree) (N : ℕ) (hN : n ≤ N) :
    ev (adjacency T) (degreeMatrix T) (distanceSum N) = fun _ _ => (1 : ℤ) := by
  rw [ev_sum hT]
  ext u v
  rw [Matrix.sum_apply]
  simp only [F]
  rw [Finset.sum_ite_eq]
  have := dist_lt hT u v
  simp; omega

end tree

section part3
lemma trace_ones {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (Matrix.of (fun _ _ => (1 : ℝ)) * X) =
      dot (ones n) (X.mulVec (ones n)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dot, ones, Matrix.mulVec,
    dotProduct, one_mul, mul_one]
  rw [Finset.sum_comm]
  simp
end part3

end UniformADProbes.Trace.Dev.Dist

namespace UniformADProbes.Trace
open UniformADProbes.Trace.Dev.Dist in
theorem chk_distance_polynomials (n : ℕ)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    (∀ k : ℕ, ∀ i j : Fin n,
      polyEval (adjacency T) (degreeMatrix T) (distancePoly k) i j =
        if T.dist i j = k then (1 : ℤ) else 0) ∧
    (∀ N : ℕ, n ≤ N →
      polyEval (adjacency T) (degreeMatrix T) (distanceSum N) =
        (fun _ _ => (1 : ℤ))) ∧
    (∀ N : ℕ, n ≤ N → ∀ X : Matrix (Fin n) (Fin n) ℝ,
      Matrix.trace (polyEval (realMatrix (adjacency T)) (realMatrix (degreeMatrix T))
        (distanceSum N) * X) = dot (ones n) (X.mulVec (ones n))) := by
  have p2 : ∀ N : ℕ, n ≤ N →
      polyEval (adjacency T) (degreeMatrix T) (distanceSum N) = (fun _ _ => (1 : ℤ)) := by
    intro N hN
    rw [polyEval_eq_ev]; exact ones_sum hT N hN
  refine ⟨?_, p2, ?_⟩
  · intro k i j
    rw [polyEval_eq_ev, (ev_dp_aux hT k).1]
    rfl
  · intro N hN X
    have h2 : polyEval (realMatrix (adjacency T)) (realMatrix (degreeMatrix T)) (distanceSum N) =
        Matrix.of (fun _ _ => (1 : ℝ)) := by
      have h := polyEval_map (Int.castRingHom ℝ).mapMatrix (adjacency T) (degreeMatrix T)
        (distanceSum N)
      have h' : polyEval (realMatrix (adjacency T)) (realMatrix (degreeMatrix T)) (distanceSum N) =
          (Int.castRingHom ℝ).mapMatrix (polyEval (adjacency T) (degreeMatrix T) (distanceSum N)) :=
        h.symm
      rw [h', p2 N hN]
      ext i j; exact Int.cast_one
    rw [h2]
    exact trace_ones X

end UniformADProbes.Trace
end

theorem solution : type_of% @UniformADProbes.Trace.chk_distance_polynomials := @UniformADProbes.Trace.chk_distance_polynomials
