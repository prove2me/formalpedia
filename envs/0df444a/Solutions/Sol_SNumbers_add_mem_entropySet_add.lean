-- Prove2me | solution 1 for SNumbers.add_mem_entropySet_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:16.18629+00:00
-- url     : https://prove2.me/submissions/f81d1302-2a72-4575-bdc7-4d7281752e1a

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {S T : X →L[𝕜] Y} {n m : ℕ} {ε δ : ℝ}
    (hε : ε ∈ entropySet S n) (hδ : δ ∈ entropySet T m) :
    ε + δ ∈ entropySet (S + T) (n + m) := by
  classical
  obtain ⟨hε0, N, hN, hNcov⟩ := hε
  obtain ⟨hδ0, M, hM, hMcov⟩ := hδ
  refine ⟨by linarith, Finset.image₂ (· + ·) N M, ?_, ?_⟩
  · calc (Finset.image₂ (· + ·) N M).card ≤ N.card * M.card :=
          Finset.card_image₂_le _ _ _
      _ ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul hN hM
      _ = 2 ^ (n + m) := (pow_add 2 n m).symm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp (hNcov ⟨x, hx, rfl⟩)
    obtain ⟨z, hz, hz'⟩ := Set.mem_iUnion₂.mp (hMcov ⟨x, hx, rfl⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hy' hz'
    refine Set.mem_iUnion₂.mpr ⟨y + z, ?_, ?_⟩
    · exact_mod_cast Finset.mem_image₂_of_mem (by exact_mod_cast hy) (by exact_mod_cast hz)
    · rw [Metric.mem_closedBall, dist_eq_norm, add_apply]
      calc ‖S x + T x - (y + z)‖ = ‖(S x - y) + (T x - z)‖ := by congr 1; abel
        _ ≤ ‖S x - y‖ + ‖T x - z‖ := norm_add_le _ _
        _ ≤ ε + δ := add_le_add hy' hz'
end SNumbers
