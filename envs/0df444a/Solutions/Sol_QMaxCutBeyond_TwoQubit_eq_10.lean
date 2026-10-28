-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T22:10:35.416578+00:00
-- url     : https://prove2.me/submissions/7e4ac4d3-255e-4b4b-af84-9c119d5ff45b

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

open Matrix QMaxCutBeyond.TwoQubit

namespace QMB10Aux

lemma inc_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (v : Fin n) :
    ∑ e ∈ G.incidenceFinset v, w e = ∑ u, if G.Adj v u then w s(v, u) else 0 := by
  have hset : G.incidenceFinset v =
      (Finset.univ.filter (fun u => G.Adj v u)).image (fun u => s(v, u)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_incidenceFinset, Finset.mem_image]
      simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq, SimpleGraph.mem_edgeSet,
        Sym2.mem_iff, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨b, hab, rfl⟩
        · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      · rintro ⟨u, hu, he⟩
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1 h2; exact ⟨hu, Or.inl rfl⟩
        · subst h1 h2; exact ⟨hu.symm, Or.inr rfl⟩
  rw [hset, Finset.sum_image, Finset.sum_filter]
  intro a _ b _ h
  exact Sym2.congr_right.mp h

end QMB10Aux

open QMB10Aux

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) (c : Fin n) (hstar : IsStar G c)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (laplacian G w *ᵥ x) ≤ (totalWeight G w + maxEdgeWeight G w) * (x ⬝ᵥ x) := by
  set b : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then w s(i, j) else 0 with hb
  have bsymm : ∀ i j, b i j = b j i := by
    intro i j; simp only [hb]
    by_cases h : G.Adj i j
    · rw [if_pos h, if_pos h.symm, Sym2.eq_swap]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have bnn : ∀ i j, 0 ≤ b i j := by intro i j; simp only [hb]; split_ifs <;> simp [hw]
  have bself : ∀ i, b i i = 0 := by intro i; simp [hb]
  have bstar : ∀ i j, b i j ≠ 0 → i = c ∨ j = c := by
    intro i j h; simp only [hb] at h; split_ifs at h with h'
    · exact hstar i j h'
    · exact absurd rfl h
  set a : Fin n → ℝ := fun j => b c j with ha
  have hLv : ∀ i, (laplacian G w *ᵥ x) i = ∑ j, b i j * (x i - x j) := by
    intro i
    simp only [mulVec, dotProduct, laplacian]
    rw [inc_sum]
    have : ∀ j, (if i = j then ∑ u, (if G.Adj i u then w s(i, u) else 0)
        else if G.Adj i j then -w s(i, j) else 0) * x j =
        (if i = j then (∑ u, b i u) * x i else 0) - b i j * x j := by
      intro j
      by_cases hij : i = j
      · subst hij; simp [hb]
      · simp only [if_neg hij, hb]; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_mul, mul_sub]
  have hQ : x ⬝ᵥ (laplacian G w *ᵥ x) = ∑ j, a j * (x c - x j) ^ 2 := by
    simp only [dotProduct, hLv]
    have hrow : ∀ i, i ≠ c → x i * ∑ j, b i j * (x i - x j) = a i * (x i - x c) * x i := by
      intro i hi
      rw [Finset.sum_eq_single c]
      · simp only [ha, bsymm c i]; ring
      · intro j _ hj
        by_cases h0 : b i j = 0
        · simp [h0]
        · rcases bstar i j h0 with h | h
          · exact absurd h hi
          · exact absurd h hj
      · simp
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
      Finset.sum_congr rfl (fun i hi => hrow i (Finset.ne_of_mem_erase hi))]
    rw [← Finset.add_sum_erase _ (fun j => a j * (x c - x j) ^ 2) (Finset.mem_univ c)]
    have hac : a c = 0 := bself c
    have e1 : ∑ i ∈ Finset.univ.erase c, a i * (x i - x c) * x i =
        ∑ j, a j * (x j - x c) * x j := by
      rw [← Finset.add_sum_erase _ (fun j => a j * (x j - x c) * x j) (Finset.mem_univ c)]
      simp [hac]
    rw [e1, Finset.mul_sum, ← Finset.sum_add_distrib, hac]
    simp only [zero_mul, zero_add]
    rw [← Finset.add_sum_erase _ (fun i => x c * (b c i * (x c - x i)) + a i * (x i - x c) * x i)
      (Finset.mem_univ c)]
    simp only [bself, hac]
    simp only [zero_mul, mul_zero, add_zero, zero_add, sub_self]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha]; ring
  have hW : totalWeight G w = ∑ j, a j := by
    have : G.edgeFinset = G.incidenceFinset c := by
      ext e
      induction e using Sym2.ind with
      | _ p q =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset]
        simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq, SimpleGraph.mem_edgeSet,
          Sym2.mem_iff]
        constructor
        · intro h; refine ⟨h, ?_⟩
          rcases hstar p q h with h' | h'
          · exact Or.inl h'.symm
          · exact Or.inr h'.symm
        · exact fun h => h.1
    rw [totalWeight, this, inc_sum]
  have hM : ∀ j, a j ≤ maxEdgeWeight G w := by
    intro j
    simp only [ha, hb]
    split_ifs with h
    · have hmem : s(c, j) ∈ G.edgeFinset := by simpa using h
      have := Finset.le_sup (f := fun e => (w e).toNNReal) hmem
      unfold maxEdgeWeight
      calc w s(c, j) ≤ ((w s(c, j)).toNNReal : ℝ) := Real.le_coe_toNNReal _
        _ ≤ _ := by exact_mod_cast this
    · exact NNReal.coe_nonneg _
  have hM0 : 0 ≤ maxEdgeWeight G w := NNReal.coe_nonneg _
  have hann : ∀ j, 0 ≤ a j := fun j => bnn c j
  have hac : a c = 0 := bself c
  rw [hQ, hW]
  set W := ∑ j, a j
  set M := maxEdgeWeight G w
  have hxx : x ⬝ᵥ x = ∑ j, x j ^ 2 := by simp [dotProduct, sq]
  rw [hxx]
  rcases (Finset.sum_nonneg (fun j _ => hann j) : 0 ≤ W).eq_or_lt with hW0 | hWpos
  · have : ∀ j, a j = 0 := by
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hann j)).mp hW0.symm j
        (Finset.mem_univ j)
    simp only [this, zero_mul, Finset.sum_const_zero]
    exact mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  · have haW : ∀ j, a j ≤ W := fun j =>
      Finset.single_le_sum (fun j _ => hann j) (Finset.mem_univ j)
    obtain ⟨j0, hj0⟩ : ∃ j, 0 < a j := by
      by_contra hcon; push_neg at hcon
      have : W ≤ 0 := Finset.sum_nonpos fun j _ => hcon j
      linarith
    have hMpos : 0 < M := lt_of_lt_of_le hj0 (hM j0)
    set k := M / W with hk
    have hkpos : 0 < k := div_pos hMpos hWpos
    have hkW : k * W = M := by rw [hk, div_mul_cancel₀ M hWpos.ne']
    have term : ∀ j, a j * (x c - x j) ^ 2 ≤
        a j * (1 + k) * x c ^ 2 + (if j = c then 0 else (W + M) * x j ^ 2) := by
      intro j
      by_cases hj : j = c
      · subst hj; simp [hac]
      · rw [if_neg hj]
        have h1 := hann j
        have h2 := hM j
        have h2' : a j ≤ k * W := hkW ▸ h2
        have key : k * (a j * (x c - x j) ^ 2) ≤
            k * (a j * (1 + k) * x c ^ 2 + (W + M) * x j ^ 2) := by
          rw [← hkW]
          nlinarith [mul_nonneg h1 (sq_nonneg (k * x c + x j)),
            mul_nonneg (sub_nonneg.mpr h2') (sq_nonneg (x j)),
            mul_nonneg hkpos.le (mul_nonneg (sub_nonneg.mpr h2') (sq_nonneg (x j)))]
        exact le_of_mul_le_mul_left key hkpos
    calc ∑ j, a j * (x c - x j) ^ 2
        ≤ ∑ j, (a j * (1 + k) * x c ^ 2 + (if j = c then 0 else (W + M) * x j ^ 2)) :=
          Finset.sum_le_sum fun j _ => term j
      _ = (W + M) * ∑ j, x j ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          have e : ∑ j, (if j = c then (0:ℝ) else (W + M) * x j ^ 2) =
              (W + M) * ∑ j, x j ^ 2 - (W + M) * x c ^ 2 := by
            rw [Finset.mul_sum, ← Finset.add_sum_erase _ (fun j => (W + M) * x j ^ 2)
              (Finset.mem_univ c), ← Finset.add_sum_erase _
              (fun j => if j = c then (0:ℝ) else (W + M) * x j ^ 2) (Finset.mem_univ c)]
            simp only [if_true, zero_add, add_sub_cancel_left]
            exact Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)
          rw [e, Finset.sum_mul, Finset.sum_mul]
          have hkW' : k * (∑ i, a i) = M := hkW
          rw [← Finset.sum_mul, ← Finset.sum_mul, show (∑ i, a i) * (1 + k) = W + M by rw [mul_add, mul_one, mul_comm _ k, hkW']]
          ring
