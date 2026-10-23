-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P03.rankAndSpecializations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:18:24.131699+00:00
-- url     : https://prove2.me/submissions/301fba9a-2270-42c6-aa49-dd2edc88a36a

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

lemma x8_rank {m n r : ℕ} (P : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin n) (Fin r) ℝ)
    (hP : P.rank = r) (hQ : Q.rank = r) : (P * Q.transpose).rank = r := by
  have hQt : (Q.transpose).rank = r := by rw [Matrix.rank_transpose, hQ]
  have htop : LinearMap.range (Q.transpose).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hQt]; simp
  rw [Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ htop, ← Matrix.rank,
    hP]

theorem x8_main {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (hrho : IsDensityMatrix rho) :
    ((r ≤ m ∧ r ≤ n ∧ Matrix.rank z.P = r ∧ Matrix.rank z.Q = r) →
      Matrix.rank (z.P * z.Q.transpose) = r) ∧
    (∀ alpha beta : ℝ,
      enhanced (rankOneParameters (fun _ : Fin 1 => alpha) (fun _ : Fin 1 => beta)) rho =
        rankOneBlock (fun _ : Fin 1 => alpha) (fun _ : Fin 1 => beta) rho) ∧
    (∀ (l : ℕ) (alpha beta : ℝ), 0 < l →
      enhanced (rankOneParameters (fun _ : Fin l => alpha) (fun _ : Fin l => beta)) rho =
        rankOneBlock (fun _ : Fin l => alpha) (fun _ : Fin l => beta) rho) ∧
    (∀ (a : Fin m → ℝ) (b : Fin n → ℝ),
      enhanced (rankOneParameters a b) rho = rankOneBlock a b rho) := by
  have key : ∀ {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ),
      enhanced (rankOneParameters a b) rho = rankOneBlock a b rho := by
    intro m n a b
    simp [enhanced, rankOneBlock, rankOneParameters]
  exact ⟨fun h => x8_rank _ _ h.2.2.1 h.2.2.2, fun _ _ => key _ _, fun _ _ _ _ => key _ _,
    fun _ _ => key _ _⟩

end QAlgorithms.Papers.Independent.Information100.P03

open QAlgorithms.Papers.Independent.Information100.P03 in
theorem solution {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    ((r ≤ m ∧ r ≤ n ∧ Matrix.rank z.P = r ∧ Matrix.rank z.Q = r) →
      Matrix.rank (z.P * z.Q.transpose) = r) ∧
    (∀ alpha beta : ℝ,
      enhanced (rankOneParameters (fun _ : Fin 1 => alpha) (fun _ : Fin 1 => beta)) rho =
        rankOneBlock (fun _ : Fin 1 => alpha) (fun _ : Fin 1 => beta) rho) ∧
    (∀ (l : ℕ) (alpha beta : ℝ), 0 < l →
      enhanced (rankOneParameters (fun _ : Fin l => alpha) (fun _ : Fin l => beta)) rho =
        rankOneBlock (fun _ : Fin l => alpha) (fun _ : Fin l => beta) rho) ∧
    (∀ (a : Fin m → ℝ) (b : Fin n → ℝ),
      enhanced (rankOneParameters a b) rho = rankOneBlock a b rho) :=
  x8_main z rho hrho
