-- Prove2me | solution 1 for TensorNP.SpectralNorm.theorem_6_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:48:03.915189+00:00
-- url     : https://prove2.me/submissions/80e7503c-fd85-4746-82a1-f49235d326b6

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace MotzkinProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def bil (x y : V → ℝ) : ℝ :=
  ∑ i, ∑ j, (if G.Adj i j then (1 : ℝ) else 0) * x i * y j

noncomputable def mass (x : V → ℝ) (i : V) : ℝ :=
  ∑ j, if G.Adj i j then x j else 0

noncomputable def supp (x : V → ℝ) : Finset V :=
  univ.filter fun i => x i ≠ 0

lemma bil_add_left (x y z : V → ℝ) : bil G (x + y) z = bil G x z + bil G y z := by
  simp only [bil, Pi.add_apply, add_mul, mul_add, sum_add_distrib]

lemma bil_add_right (x y z : V → ℝ) : bil G x (y + z) = bil G x y + bil G x z := by
  simp only [bil, Pi.add_apply, mul_add, sum_add_distrib]
lemma bil_symm (x y : V → ℝ) : bil G x y = bil G y x := by
  rw [bil, sum_comm]
  simp only [bil, G.adj_comm, mul_comm, mul_left_comm]
lemma bil_single (a : V) (t : ℝ) (x : V → ℝ) :
    bil G (Pi.single a t) x = t * mass G x a := by
  rw [bil, sum_eq_single a] <;> simp +contextual [mass, mul_sum, mul_comm]
lemma bil_update (x : V → ℝ) (a : V) (t : ℝ) :
    bil G (Function.update x a t) (Function.update x a t) =
      bil G x x + 2 * (t - x a) * mass G x a := by
  have hu : Function.update x a t = x + Pi.single a (t - x a) := by
    ext i
    by_cases hi : i = a <;> simp [hi]
  simp only [hu, bil_add_left, bil_add_right, bil_single]
  rw [bil_symm G x (Pi.single a (t - x a)), bil_single]
  have hz : mass G (Pi.single a (t - x a)) a = 0 := by
    exact sum_eq_zero (fun j _ => by by_cases hj : j = a <;> simp [hj])
  simp [hz, two_mul, add_mul, add_assoc]

lemma mass_update (x : V → ℝ) (a b : V) (t : ℝ) (hab : ¬ G.Adj a b) :
    mass G (Function.update x b t) a = mass G x a := by
  exact sum_congr rfl (fun j _ => by by_cases hj : j = b <;> simp [hj, hab])

noncomputable def move (x : V → ℝ) (a b : V) : V → ℝ :=
  Function.update (Function.update x a (x a + x b)) b 0

lemma move_increases (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) (a b : V)
    (hne : a ≠ b) (hab : ¬ G.Adj a b) (hm : mass G x b ≤ mass G x a) :
    bil G x x ≤ bil G (move x a b) (move x a b) := by
  simp only [move, bil_update]
  rw [mass_update G x b a _ (by simpa [G.adj_comm] using hab), Function.update_of_ne hne.symm]
  nlinarith [mul_nonneg (hx b) (sub_nonneg.mpr hm)]

lemma sum_update (x : V → ℝ) (a : V) (t : ℝ) :
    (∑ i, Function.update x a t i) = (∑ i, x i) + t - x a := by
  have hu : Function.update x a t = x + Pi.single a (t - x a) := by
    ext i
    by_cases hi : i = a <;> simp [hi]
  simp [hu, sum_add_distrib, add_sub_assoc]

lemma move_simplex (x : V → ℝ) (hx : x ∈ stdSimplex ℝ V) (a b : V) (hne : a ≠ b) :
    move x a b ∈ stdSimplex ℝ V := by
  refine ⟨?_, ?_⟩
  · exact fun i => by by_cases hib : i = b <;> by_cases hia : i = a <;> simp [move, hib, hia, hne, hx.1, add_nonneg]
  · simp [move, sum_update, hne.symm, hx.2, add_sub_assoc]

lemma move_support_lt (x : V → ℝ) (a b : V) (_hne : a ≠ b)
    (ha : a ∈ supp x) (hb : b ∈ supp x) :
    (supp (move x a b)).card < (supp x).card := by
  have hs : supp (move x a b) ⊆ (supp x).erase b := by
    intro i hi
    have hxi : move x a b i ≠ 0 := (Finset.mem_filter.mp hi).2
    by_cases hib : i = b
    · simp [move, hib] at hxi
    · refine mem_erase.mpr ⟨hib, ?_⟩
      by_cases hia : i = a
      · exact hia.symm ▸ ha
      · exact Finset.mem_filter.mpr ⟨mem_univ _, by simpa [move, hia, hib] using hxi⟩
  exact lt_of_le_of_lt (card_le_card hs) (card_erase_lt_of_mem hb)

lemma exists_clique_dominating (x : V → ℝ) (hx : x ∈ stdSimplex ℝ V) :
    ∃ y ∈ stdSimplex ℝ V, G.IsClique (↑(supp y) : Set V) ∧ bil G x x ≤ bil G y y := by
  generalize hn : (supp x).card = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hc : G.IsClique (↑(supp x) : Set V)
    · exact ⟨x, hx, hc, le_rfl⟩
    · obtain ⟨a, b, hne, hab⟩ := G.not_isClique_iff.mp hc
      have step (a b : V) (hne : a ≠ b) (ha : a ∈ supp x) (hb : b ∈ supp x)
          (hab : ¬ G.Adj a b) (hm : mass G x b ≤ mass G x a) :
          ∃ y ∈ stdSimplex ℝ V, G.IsClique (↑(supp y) : Set V) ∧ bil G x x ≤ bil G y y := by
        obtain ⟨y, hy, hc, he⟩ := ih _ (by simpa [hn] using move_support_lt x a b hne ha hb)
          (move x a b) (move_simplex x hx a b hne) rfl
        exact ⟨y, hy, hc, (move_increases G x hx.1 a b hne hab hm).trans he⟩
      rcases le_total (mass G x b) (mass G x a) with hm | hm
      · exact step a b (fun h => hne (Subtype.ext h)) a.property b.property hab hm
      · exact step b a (fun h => hne (Subtype.ext h.symm)) b.property a.property (fun h => hab h.symm) hm

lemma clique_term (x : V → ℝ) (hc : G.IsClique (↑(supp x) : Set V)) (i j : V) :
    (if G.Adj i j then (1 : ℝ) else 0) * x i * x j =
      x i * x j - if i = j then x i*x j else 0 := by
  by_cases hij : i = j
  · simp [hij]
  · by_cases hi : x i = 0
    · simp [hi, hij]
    · by_cases hj : x j = 0
      · simp [hj, hij]
      · have hadj : G.Adj i j := hc (mem_filter.mpr ⟨mem_univ i, hi⟩) (mem_filter.mpr ⟨mem_univ j, hj⟩) hij
        simp [hadj, hij]

lemma clique_identity (x : V → ℝ) (hc : G.IsClique (↑(supp x) : Set V)) :
    bil G x x = (∑ i, x i)^2 - ∑ i, x i^2 := by
  simp only [bil, clique_term G x hc]
  simp [sum_sub_distrib, ← mul_sum, ← sum_mul, sq]

omit [DecidableEq V] in
lemma sum_supp (x : V → ℝ) : ∑ i ∈ supp x, x i = ∑ i, x i := by
  simp [supp, sum_filter]
  exact sum_congr rfl (fun i _ => ite_eq_right_iff.mpr (fun h => h.symm))

omit [DecidableEq V] in
lemma sum_supp_sq (x : V → ℝ) : ∑ i ∈ supp x, x i^2 = ∑ i, x i^2 := by
  simp [supp, sum_filter]
  exact sum_congr rfl (fun i _ => ite_eq_right_iff.mpr (fun h => by simp [h]))

lemma clique_bound (x : V → ℝ) (hx : x ∈ stdSimplex ℝ V)
    (hc : G.IsClique (↑(supp x) : Set V)) :
    bil G x x ≤ 1 - 1/(G.cliqueNum : ℝ) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := supp x) (f := x)
  simp only [sum_supp, sum_supp_sq, hx.2, one_pow] at hcs
  have hcard : ((supp x).card : ℝ) ≤ (G.cliqueNum : ℝ) := by exact_mod_cast hc.card_le_cliqueNum
  have hs0 : 0 ≤ ∑ i, x i^2 := sum_nonneg (fun i _ => sq_nonneg (x i))
  have hw : 1 ≤ (G.cliqueNum : ℝ) * ∑ i, x i^2 := hcs.trans (mul_le_mul_of_nonneg_right hcard hs0)
  have hp : 0 < (G.cliqueNum : ℝ) := lt_of_not_ge fun h =>
    (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h hs0)) (lt_of_lt_of_le zero_lt_one hw)
  have hinv : 1/(G.cliqueNum : ℝ) ≤ ∑ i, x i^2 :=
    (div_le_iff₀ hp).2 (by simpa only [mul_comm] using hw)
  simpa only [clique_identity G x hc, hx.2, one_pow] using sub_le_sub_left hinv (1 : ℝ)


lemma uniform_attains [Nonempty V] :
    ∃ x ∈ stdSimplex ℝ V, bil G x x = 1 - 1 / (G.cliqueNum : ℝ) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have h1 : 1 ≤ G.cliqueNum := by
    have h : G.IsClique (↑({Classical.choice (inferInstance : Nonempty V)} : Finset V) : Set V) := by
      simp
    simpa using h.card_le_cliqueNum
  have hω : (G.cliqueNum : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp h1)
  let x : V → ℝ := fun i => if i ∈ s then 1 / (s.card : ℝ) else 0
  have hsum : (∑ i, x i) = 1 := by
    simp [x, hs.card_eq, hω]
  have hsq : (∑ i, x i ^ 2) = 1 / (G.cliqueNum : ℝ) := by
    simp [x, ite_pow, hs.card_eq, pow_two, hω]
  have hc : G.IsClique (↑(supp x) : Set V) := by
    exact hs.isClique.subset (fun i hi => by
      by_contra his
      exact (Finset.mem_filter.mp hi).2 (if_neg his))
  refine ⟨x, ⟨?_, hsum⟩, ?_⟩
  · exact fun i => by by_cases hi : i ∈ s <;> simp [x, hi]
  · simpa [hsum, hsq] using clique_identity G x hc

end MotzkinProof







open scoped BigOperators

private theorem weighted_darts {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (w : Sym2 (Fin v) → ℝ) :
    (∑ d : G.Dart, w d.edge) = 2 * ∑ e ∈ G.edgeFinset, w e := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
    (g := SimpleGraph.Dart.edge) (fun d _ => G.mem_edgeFinset.mpr d.edge_mem) w
  rw [← hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.sum_const, nsmul_eq_mul, G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he), Nat.cast_ofNat]

private theorem ordered_dart_sum {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (f : Fin v → Fin v → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f i j else 0) = ∑ d : G.Dart, f d.fst d.snd := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin v × Fin v => if G.Adj p.1 p.2 then f p.1 p.2 else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_bij (fun p hp => (⟨p, (Finset.mem_filter.mp hp).2⟩ : G.Dart))
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => congrArg SimpleGraph.Dart.toProd h)
    (fun d _ => ⟨d.toProd, Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.adj⟩, rfl⟩)
    (fun _ _ => rfl)

theorem ordered_edge_sum {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (x : Fin v → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then x i * x j else 0) =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩ e := by
  exact (ordered_dart_sum G (fun i j => x i * x j)).trans
    (weighted_darts G (Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩))

theorem solution {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] :
    IsGreatest
      ((fun x : Fin v → ℝ =>
          2 * ∑ s ∈ G.edgeFinset, Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩ s) ''
        stdSimplex ℝ (Fin v))
      (1 - 1 / (G.cliqueNum : ℝ)) := by
  classical
  let : Nonempty (Fin v) := ⟨⟨0, hv⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, he⟩ := MotzkinProof.uniform_attains G
    refine ⟨x, hx, ?_⟩
    dsimp only
    rw [← ordered_edge_sum G x]
    simpa [MotzkinProof.bil] using he
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hc, he⟩ := MotzkinProof.exists_clique_dominating G x hx
    dsimp only
    rw [← ordered_edge_sum G x]
    simpa [MotzkinProof.bil] using he.trans (MotzkinProof.clique_bound G y hy hc)
