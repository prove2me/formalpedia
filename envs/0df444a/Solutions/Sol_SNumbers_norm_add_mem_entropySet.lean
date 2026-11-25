-- Prove2me | solution 1 for SNumbers.norm_add_mem_entropySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:04.734164+00:00
-- url     : https://prove2.me/submissions/4b26e5e6-cd00-4297-84ee-533f36b14bfb

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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ‖S‖ + δ ∈ entropySet S n := by
  refine ⟨add_pos_of_nonneg_of_pos (norm_nonneg S) hδ, {0},
    by simpa using Nat.one_le_two_pow, ?_⟩
  simp only [Finset.coe_singleton, Set.biUnion_singleton]
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hSx : ‖S x‖ ≤ ‖S‖ := by
    calc ‖S x‖ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
      _ ≤ ‖S‖ * 1 := by gcongr
      _ = ‖S‖ := mul_one _
  simpa using hSx.trans (by linarith)
end SNumbers
