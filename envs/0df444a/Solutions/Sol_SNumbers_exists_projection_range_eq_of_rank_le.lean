-- Prove2me | solution 1 for SNumbers.exists_projection_range_eq_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:23.051928+00:00
-- url     : https://prove2.me/submissions/6525047c-3f25-4d40-8924-f2c544980590

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_BasicResults_John
public import Definitions.Def_BasicResults_KadetsSnobar
public import Theorems.Thm_John_exists_projection


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution
    {V : Submodule 𝕜 Y} {n : ℕ} (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt n := by
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hV_rank Cardinal.natCast_lt_aleph0)
  have hfr : Module.finrank 𝕜 V ≤ n := by
    rw [← Nat.cast_le (α := Cardinal), Module.finrank_eq_rank]; exact hV_rank
  obtain ⟨P, hPP, hPrange, hPnorm⟩ := John.exists_projection V
  exact ⟨P, hPP, hPrange, hPnorm.trans (Real.sqrt_le_sqrt (by exact_mod_cast hfr))⟩
end SNumbers
