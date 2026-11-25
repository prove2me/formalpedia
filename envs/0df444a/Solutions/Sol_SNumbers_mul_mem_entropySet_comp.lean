-- Prove2me | solution 1 for SNumbers.mul_mem_entropySet_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:33.960094+00:00
-- url     : https://prove2.me/submissions/7e6bd789-e3fd-40ba-8147-c95e3f33458b

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
attribute [local simp] SNumbers.entropyNumber_zero_op

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n m : ℕ} {β δ : ℝ}
    (hβ : β ∈ entropySet B n) (hδ : δ ∈ entropySet S m) {c : 𝕜} (hc : δ < ‖c‖) :
    ‖c‖ * β ∈ entropySet (B.comp S) (n + m) := by
  classical
  obtain ⟨hβ0, N, hN, hNcov⟩ := hβ
  obtain ⟨hδ0, M, hM, hMcov⟩ := hδ
  have hc0 : (0 : ℝ) < ‖c‖ := hδ0.trans hc
  have hcne : c ≠ 0 := by simpa [norm_pos_iff] using hc0
  refine ⟨by positivity, Finset.image₂ (fun z y => B y + c • z) N M, ?_, ?_⟩
  · calc (Finset.image₂ (fun z y => B y + c • z) N M).card ≤ N.card * M.card :=
          Finset.card_image₂_le _ _ _
      _ ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul hN hM
      _ = 2 ^ (n + m) := (pow_add 2 n m).symm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp (hMcov ⟨x, hx, rfl⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hy'
    -- the rescaled difference lies in the unit ball of `Y`
    have hw : c⁻¹ • (S x - y) ∈ Metric.closedBall (0 : Y) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
      calc ‖c‖⁻¹ * ‖S x - y‖ ≤ ‖c‖⁻¹ * ‖c‖ := by gcongr; exact hy'.trans hc.le
        _ = 1 := inv_mul_cancel₀ hc0.ne'
    obtain ⟨z, hz, hz'⟩ := Set.mem_iUnion₂.mp (hNcov ⟨_, hw, rfl⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz'
    refine Set.mem_iUnion₂.mpr ⟨B y + c • z, ?_, ?_⟩
    · have hmem : B y + c • z ∈ Finset.image₂ (fun z y => B y + c • z) N M :=
        Finset.mem_image₂_of_mem (f := fun z y => B y + c • z)
          (by exact_mod_cast hz) (by exact_mod_cast hy)
      exact_mod_cast hmem
    · rw [Metric.mem_closedBall, dist_eq_norm, ContinuousLinearMap.coe_comp,
        Function.comp_apply]
      have hBv : c • B (c⁻¹ • (S x - y)) = B (S x) - B y := by
        rw [← ContinuousLinearMap.map_smul, smul_inv_smul₀ hcne, map_sub]
      calc ‖B (S x) - (B y + c • z)‖
          = ‖c • (B (c⁻¹ • (S x - y)) - z)‖ := by rw [smul_sub, hBv]; congr 1; abel
        _ = ‖c‖ * ‖B (c⁻¹ • (S x - y)) - z‖ := norm_smul c _
        _ ≤ ‖c‖ * β := by gcongr
end SNumbers
