-- Prove2me | solution 1 for TheoryOfGames.Minimax.alternative_strict
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:03:30.769665+00:00
-- url     : https://prove2.me/submissions/af66f88a-ca75-4b59-a0fb-d48dde68ac01

import Mathlib

namespace MinimaxAux

open Finset

/-- The two alternatives cannot hold simultaneously. -/
lemma not_both {n m : ℕ} (a : Fin n → Fin m → ℝ) (x : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n))
    (h1 : ∀ i, ∑ j, a i j * x j ≤ 0) (h2 : ∀ j, 0 < ∑ i, a i j * w i) : False := by
  have e : ∑ i, w i * ∑ j, a i j * x j = ∑ j, x j * ∑ i, a i j * w i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hA : ∑ i, w i * ∑ j, a i j * x j ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw.1 i) (h1 i)
  have hB : 0 < ∑ j, x j * ∑ i, a i j * w i := by
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := x) (by rw [hx.2]; exact one_ne_zero)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hx.1 j) (h2 j).le) ⟨j, mem_univ _, ?_⟩
    exact mul_pos (lt_of_le_of_ne (hx.1 j) (Ne.symm hj)) (h2 j)
  linarith

/-- If the first alternative fails, the second holds (separation of the compact convex set
`A(S_m)` from the closed negative orthant). -/
lemma exists_of_not {n m : ℕ} (hn : 0 < n) (a : Fin n → Fin m → ℝ)
    (h : ¬ ∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) :
    ∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 < ∑ i, a i j * w i := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · refine ⟨fun _ => 1 / (n : ℝ), ⟨fun _ => by positivity, ?_⟩, fun j => isEmptyElim j⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  let A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of a)
  have hA : ∀ x i, A x i = ∑ j, a i j * x j := by
    intro x i; simp [A, Matrix.mulVec, dotProduct]
  set S : Set (Fin n → ℝ) := A '' stdSimplex ℝ (Fin m) with hS
  have hSc : IsCompact S :=
    (isCompact_stdSimplex ℝ (Fin m)).image (LinearMap.continuous_of_finiteDimensional A)
  have hSv : Convex ℝ S := (convex_stdSimplex ℝ (Fin m)).linear_image A
  set T : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Iic (0 : ℝ)) with hT
  have hTv : Convex ℝ T := convex_pi fun i _ => convex_Iic 0
  have hTc : IsClosed T := isClosed_set_pi fun i _ => isClosed_Iic
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hmem
    exact h ⟨x, hx, fun i => by rw [← hA]; exact hmem i (Set.mem_univ i)⟩
  obtain ⟨f, u, v, hf1, huv, hf2⟩ := geometric_hahn_banach_compact_closed hSv hSc hTv hTc hdisj
  have h0 : v < 0 := by
    have h00 : (0 : Fin n → ℝ) ∈ T := by
      rw [hT, Set.mem_univ_pi]
      intro i
      exact (le_refl (0 : ℝ))
    have := hf2 0 h00
    simpa using this
  let e : Fin n → (Fin n → ℝ) := fun i j => if i = j then 1 else 0
  have hrep : ∀ y : Fin n → ℝ, f y = ∑ i, y i * f (e i) := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) y
    simpa [e] using this
  -- the functional is nonpositive on the coordinate vectors
  have hneg : ∀ i, f (e i) ≤ 0 := by
    intro i
    by_contra hpos
    rw [not_le] at hpos
    set p := f (e i) with hp
    set t : ℝ := (-v + 1) / p with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have hb : (fun j => -t * e i j) ∈ T := by
      intro j _
      simp only [Set.mem_Iic, e]
      split_ifs <;> linarith
    have := hf2 _ hb
    rw [hrep] at this
    have hsum : ∑ j, (-t * e i j) * f (e j) = -t * p := by
      rw [Finset.sum_eq_single i]
      · simp [e, hp]
      · intro j _ hj
        simp [e, Ne.symm hj]
      · intro hi; exact absurd (mem_univ i) hi
    rw [hsum, ht] at this
    have : -((-v + 1) / p) * p = v - 1 := by field_simp; ring
    linarith
  set w' : Fin n → ℝ := fun i => - f (e i) with hw'
  have hw'nn : ∀ i, 0 ≤ w' i := fun i => by simp only [hw']; linarith [hneg i]
  have hpos : ∀ j, 0 < ∑ i, a i j * w' i := by
    intro j
    have hmem : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ stdSimplex ℝ (Fin m) := single_mem_stdSimplex ℝ j
    have h1 := hf1 _ ⟨_, hmem, rfl⟩
    rw [hrep] at h1
    have hcol : ∀ i, A (Pi.single j (1 : ℝ)) i = a i j := by
      intro i; rw [hA]; simp [Pi.single_apply]
    simp only [hcol] at h1
    have : ∑ i, a i j * w' i = - ∑ i, a i j * f (e i) := by
      simp only [hw', mul_neg, Finset.sum_neg_distrib]
    rw [this]
    linarith
  have hs : 0 < ∑ i, w' i := by
    by_contra hle
    rw [not_lt] at hle
    have hz : ∀ i, w' i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw'nn i)).1
        (le_antisymm hle (Finset.sum_nonneg fun i _ => hw'nn i))
      exact this i (mem_univ i)
    obtain ⟨j⟩ := hm
    have := hpos j
    simp [hz] at this
  refine ⟨fun i => w' i / ∑ k, w' k, ⟨fun i => div_nonneg (hw'nn i) hs.le, ?_⟩, fun j => ?_⟩
  · rw [← Finset.sum_div, div_self hs.ne']
  · have : ∑ i, a i j * (w' i / ∑ k, w' k) = (∑ i, a i j * w' i) / ∑ k, w' k := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact div_pos (hpos j) hs

end MinimaxAux

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : Fin n → Fin m → ℝ) :
    Xor (∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0)
      (∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 < ∑ i, a i j * w i) := by
  by_cases h : ∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0
  · refine Or.inl ⟨h, ?_⟩
    rintro ⟨w, hw, hw2⟩
    obtain ⟨x, hx, hx2⟩ := h
    exact MinimaxAux.not_both a x hx w hw hx2 hw2
  · exact Or.inr ⟨MinimaxAux.exists_of_not hn a h, h⟩
