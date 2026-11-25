-- Prove2me | solution 1 for SNumbers.rank_id_piLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:50.692635+00:00
-- url     : https://prove2.me/submissions/31508e8a-66c9-452a-9009-c0ac7335aa09

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Theorems.Thm_SNumbers_finrank_piLp


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (k : ℕ) :
    (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank = (k : Cardinal) := by
  have h1 : (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank
      = Module.rank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) := by
    rw [ContinuousLinearMap.rank, ContinuousLinearMap.coe_id]
    show Module.rank 𝕜 (LinearMap.range (LinearMap.id : _ →ₗ[𝕜] _)) = _
    rw [LinearMap.range_id]; exact Submodule.topEquiv.rank_eq
  rw [h1, ← Module.finrank_eq_rank, finrank_piLp]
end SNumbers
