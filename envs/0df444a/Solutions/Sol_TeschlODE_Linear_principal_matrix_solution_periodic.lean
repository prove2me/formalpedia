-- Prove2me | solution 1 for TeschlODE.Linear.principal_matrix_solution_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:09:26.853609+00:00
-- url     : https://prove2.me/submissions/60277229-9d52-47b0-9e2d-01af7a9f2e29

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

set_option autoImplicit false

namespace TeschlODE.Linear.P2MAuxBde

open Set

lemma mulVec_norm_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    ‖Matrix.mulVec B w‖ ≤ (∑ i, ∑ k, |B i k|) * ‖w‖ := by
  have hM : 0 ≤ ∑ i, ∑ k, |B i k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg _))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ k, B i k * w k| ≤ ∑ k, |B i k * w k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |B i k| * ‖w‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := norm_le_pi_norm w k
        rwa [Real.norm_eq_abs] at this
    _ = (∑ k, |B i k|) * ‖w‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ k, |B i k|) * ‖w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ k, |B i k|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

lemma col_unique {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (hA : Continuous A)
    (f g : ℝ → Fin n → ℝ)
    (hf : ∀ s, HasDerivAt f (Matrix.mulVec (A s) (f s)) s) (hg : ∀ s, HasDerivAt g (Matrix.mulVec (A s) (g s)) s)
    (t₀ : ℝ) (h0 : f t₀ = g t₀) (t : ℝ) : f t = g t := by
  have hcont : Continuous fun s => ∑ i, ∑ k, |A s i k| := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
    exact (hA.matrix_elem i k).abs
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := min t t₀ - 1) (b := max t t₀ + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hv : ∀ s ∈ Ioo (min t t₀ - 1) (max t t₀ + 1),
      LipschitzOnWith (Real.toNNReal M) (fun x => Matrix.mulVec (A s) x) univ := by
    intro s hs
    refine LipschitzWith.lipschitzOnWith ?_
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← Matrix.mulVec_sub]
    refine (mulVec_norm_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := hM s (Ioo_subset_Icc_self hs)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (Real.le_coe_toNNReal M))
  have ht0 : t₀ ∈ Ioo (min t t₀ - 1) (max t t₀ + 1) :=
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
  have ht : t ∈ Ioo (min t t₀ - 1) (max t t₀ + 1) :=
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩
  exact ODE_solution_unique_of_mem_Ioo (v := fun s x => Matrix.mulVec (A s) x) (s := fun _ => univ) hv ht0
    (fun s _ => ⟨hf s, mem_univ _⟩) (fun s _ => ⟨hg s, mem_univ _⟩) h0 ht

end TeschlODE.Linear.P2MAuxBde

open TeschlODE.Linear in
theorem solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hper : ∀ t, A (t + T) = A t)
    (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ) (hΦ : IsPrincipalMatrixSolution A Set.univ Φ)
    (t t₀ : ℝ) :
    Φ (t + T) (t₀ + T) = Φ t t₀ := by
  ext i j
  have key := TeschlODE.Linear.P2MAuxBde.col_unique A hA (fun s k => Φ (s + T) (t₀ + T) k j) (fun s k => Φ s t₀ k j)
    ?_ ?_ t₀ ?_ t
  · exact congrFun key i
  · intro s
    rw [hasDerivAt_pi]
    intro k
    have h := (hΦ (t₀ + T) (Set.mem_univ _)).2 (s + T) (Set.mem_univ _) k j
    rw [hasDerivWithinAt_univ] at h
    have h2 := h.comp_add_const s T
    rw [hper] at h2
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2
  · intro s
    rw [hasDerivAt_pi]
    intro k
    have h := (hΦ t₀ (Set.mem_univ _)).2 s (Set.mem_univ _) k j
    rw [hasDerivWithinAt_univ] at h
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  · funext k
    simp only [(hΦ _ (Set.mem_univ _)).1]
