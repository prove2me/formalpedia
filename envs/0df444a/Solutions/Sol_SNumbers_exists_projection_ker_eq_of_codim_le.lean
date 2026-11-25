-- Prove2me | solution 1 for SNumbers.exists_projection_ker_eq_of_codim_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:38.787173+00:00
-- url     : https://prove2.me/submissions/976eb640-92a4-4df7-896e-2ba1e1521552

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_BasicResults_John
public import Definitions.Def_BasicResults_GarlingGordon
public import Theorems.Thm_John_exists_projection_ker


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
namespace SNumbers
theorem _root_.solution
    {M : Submodule 𝕜 X} (hM_closed : IsClosed (M : Set X)) {n : ℕ}
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧
      LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧ ‖P‖ ≤ Real.sqrt n + ε := by
  have : FiniteDimensional 𝕜 (X ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hM_codim Cardinal.natCast_lt_aleph0)
  have hfrn : Module.finrank 𝕜 (X ⧸ M) ≤ n := by
    rw [← Nat.cast_le (α := Cardinal), Module.finrank_eq_rank]; exact hM_codim
  have hfr : (Module.finrank 𝕜 (X ⧸ M) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfrn
  obtain ⟨P, hPP, hPker, hPnorm⟩ := John.exists_projection_ker M hε
  refine ⟨P, hPP, hPker, hPnorm.trans ?_⟩
  gcongr
end SNumbers
