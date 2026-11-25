-- Prove2me | solution 1 for SNumbers.norm_mul_mem_entropySet_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:31.947224+00:00
-- url     : https://prove2.me/submissions/bf18608e-3e3f-42eb-ab2c-905efc796f73

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
theorem _root_.solution {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hB : 0 < ‖B‖) (hε : ε ∈ entropySet S n) :
    ‖B‖ * ε ∈ entropySet (B.comp S) n := by
  classical
  obtain ⟨hε0, N, hN, hcov⟩ := hε
  refine ⟨by positivity, N.image B, (Finset.card_image_le).trans hN, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp (hcov ⟨x, hx, rfl⟩)
  rw [Metric.mem_closedBall, dist_eq_norm] at hy'
  refine Set.mem_iUnion₂.mpr ⟨B y, ?_, ?_⟩
  · exact_mod_cast Finset.mem_image_of_mem B (by exact_mod_cast hy)
  · rw [Metric.mem_closedBall, dist_eq_norm, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    calc ‖B (S x) - B y‖ = ‖B (S x - y)‖ := by rw [map_sub]
      _ ≤ ‖B‖ * ‖S x - y‖ := B.le_opNorm _
      _ ≤ ‖B‖ * ε := by gcongr
end SNumbers
