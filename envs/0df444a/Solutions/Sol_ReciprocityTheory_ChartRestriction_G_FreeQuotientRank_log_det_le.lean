-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.log_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:57:18.525448+00:00
-- url     : https://prove2.me/submissions/dca91519-06b5-4331-b4ae-fef5e2f37280

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hadamard_det_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {ρ : ℕ} (m : Matrix (Fin ρ) (Fin ρ) K) (hdet : m.det ≠ 0) (σ : InfinitePlace K)
    (a b : Fin ρ → ℝ) (harch : ∀ i j, m i j ≠ 0 → Real.log (σ (m i j)) + a i ≤ b j) :
    Real.log (σ m.det) ≤ ∑ j, b j - ∑ i, a i + (ρ : ℝ) / 2 * Real.log ρ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · simp [Matrix.det_fin_zero]
  have hpos : 0 < σ m.det := InfinitePlace.pos_iff.2 hdet
  let A : Matrix (Fin ρ) (Fin ρ) ℂ := fun i j => (Real.exp (a i) : ℂ) * σ.embedding (m i j)
  have hAdet : A.det = (∏ i, (Real.exp (a i) : ℂ)) * σ.embedding m.det := by
    have h : A = Matrix.diagonal (fun i => (Real.exp (a i) : ℂ)) * (σ.embedding.mapMatrix m) := by
      ext i j
      simp [A, Matrix.diagonal_mul]
    rw [h, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  have hnormA : ‖A.det‖ = Real.exp (∑ i, a i) * σ m.det := by
    rw [hAdet, norm_mul, norm_prod, InfinitePlace.norm_embedding_eq, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hentry : ∀ i j, ‖A i j‖ ≤ Real.exp (b j) := by
    intro i j
    by_cases h : m i j = 0
    · simp [A, h, (Real.exp_pos _).le]
    · have hp : 0 < σ (m i j) := InfinitePlace.pos_iff.2 h
      have h2 := harch i j h
      simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        InfinitePlace.norm_embedding_eq]
      calc Real.exp (a i) * σ (m i j) = Real.exp (a i + Real.log (σ (m i j))) := by
            rw [Real.exp_add, Real.exp_log hp]
        _ ≤ Real.exp (b j) := Real.exp_le_exp.2 (by linarith)
  have hcol : ∀ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt ρ * Real.exp (b j) := by
    intro j
    rw [← Real.sqrt_sq (Real.exp_pos (b j)).le, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin ρ, Real.exp (b j) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
      _ = ρ * Real.exp (b j) ^ 2 := by simp
  have hH := ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le A.transpose
  rw [Matrix.det_transpose, hnormA] at hH
  simp only [Matrix.transpose_apply] at hH
  have hprod : ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ ∏ j : Fin ρ, (Real.sqrt ρ * Real.exp (b j)) :=
    Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _) fun j _ => hcol j
  have key : Real.exp (∑ i, a i) * σ m.det ≤ Real.sqrt ρ ^ ρ * Real.exp (∑ j, b j) := by
    calc _ ≤ _ := hH
      _ ≤ _ := hprod
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.exp_sum]
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by exact_mod_cast hρ)
  have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) key
  rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp,
    Real.log_mul (pow_pos hs _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg _)] at h1
  linarith
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
