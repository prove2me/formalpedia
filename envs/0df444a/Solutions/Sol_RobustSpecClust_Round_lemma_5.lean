-- Prove2me | solution 1 for RobustSpecClust.Round.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T10:50:24.931758+00:00
-- url     : https://prove2.me/submissions/fcc41992-abdb-4e2c-842e-93aeab555c69

import Definitions.Def_RobustSpecClust_Round_Setting

open RobustSpecClust.Round Matrix

theorem solution {n r : ℕ} (φ : Fin n → Fin r) (Bstar : Matrix (Fin r) (Fin r) ℝ)
    (Vh : Matrix (Fin n) (Fin r) ℝ) (ε : ℝ) (hε : 0 < ε)
    (a : Fin n → Fin r) (B : Matrix (Fin r) (Fin r) ℝ) (hkm : IsApproxKMeans ε Vh a B)
    (δ : Fin r → ℝ) (hδ0 : ∀ k, 0 ≤ δ k)
    (hδ : ∀ k l, l ≠ k → δ k ≤ vecNorm (Bstar l - Bstar k)) :
    ∑ k, ((misSet (memb φ * Bstar) (memb a * B) φ δ k).card : ℝ) * δ k ^ 2
      ≤ 4 * (4 + 2 * ε) * frobSq (memb φ * Bstar - Vh) := by
  set W := memb φ * Bstar with hW
  set Vb := memb a * B with hVb
  -- squared row errors `‖v̄_i − v_i‖²`
  set f : Fin n → ℝ := fun i => ∑ j, (Vb i j - W i j) ^ 2 with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- (G.2) tested against the feasible pair `(Θ*, B*)`
  have hopt : frobSq (Vh - Vb) ≤ (1 + ε) * frobSq (Vh - W) := hkm φ Bstar
  have hswap : frobSq (Vh - W) = frobSq (W - Vh) := by
    unfold frobSq
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]; ring
  -- `‖V̄ − V‖_F² ≤ 2‖V̄ − V̂‖_F² + 2‖V̂ − V‖_F² ≤ (4 + 2ε)‖V − V̂‖_F²`
  have htri : ∑ i, f i ≤ (4 + 2 * ε) * frobSq (W - Vh) := by
    have h1 : ∑ i, f i ≤ 2 * frobSq (Vh - Vb) + 2 * frobSq (Vh - W) := by
      simp only [hf, frobSq, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      simp only [Matrix.sub_apply]
      nlinarith [sq_nonneg (Vb i j + W i j - 2 * Vh i j)]
    rw [hswap] at h1 hopt
    nlinarith
  -- every point of `S_k` carries squared error at least `δ_k² / 4`
  have hpt : ∀ k, ∀ i ∈ misSet W Vb φ δ k, δ k ^ 2 ≤ 4 * f i := by
    intro k i hi
    simp only [misSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hnorm : vecNorm (Vb i - W i) ^ 2 = f i := by
      unfold vecNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
      rfl
    have h2 : (δ k / 2) ^ 2 ≤ vecNorm (Vb i - W i) ^ 2 :=
      pow_le_pow_left₀ (by linarith [hδ0 k]) hi.2 2
    nlinarith
  have hsub : ∀ k, misSet W Vb φ δ k ⊆ Finset.univ.filter (fun i => φ i = k) := by
    intro k i hi
    simp only [misSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.1
  calc ∑ k, ((misSet W Vb φ δ k).card : ℝ) * δ k ^ 2
      = ∑ k, ∑ i ∈ misSet W Vb φ δ k, δ k ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k, ∑ i ∈ misSet W Vb φ δ k, 4 * f i :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i hi => hpt k i hi
    _ ≤ ∑ k, ∑ i ∈ Finset.univ.filter (fun i => φ i = k), 4 * f i :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum_of_subset_of_nonneg (hsub k)
          (fun i _ _ => by linarith [hf0 i])
    _ = ∑ i, 4 * f i := Finset.sum_fiberwise _ _ _
    _ = 4 * ∑ i, f i := by rw [Finset.mul_sum]
    _ ≤ 4 * ((4 + 2 * ε) * frobSq (W - Vh)) := by linarith [htri]
    _ = 4 * (4 + 2 * ε) * frobSq (W - Vh) := by ring
