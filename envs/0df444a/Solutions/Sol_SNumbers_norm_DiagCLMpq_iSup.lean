-- Prove2me | solution 1 for SNumbers.norm_DiagCLMpq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:14:51.42683+00:00
-- url     : https://prove2.me/submissions/7e5cc146-566a-4ba6-b6e3-f207e4cbd76c

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_DiagonalMatrices
public import Theorems.Thm_SNumbers_norm_idEmbed_le_one
public import Theorems.Thm_SNumbers_DiagCLMpq_eq_comp
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
namespace SNumbers
theorem _root_.solution [Nonempty (Fin m)] (hqp : q ≤ p) (σ : Fin m → 𝕜) :
    ‖DiagCLMpq p q σ‖ = ⨆ i, ‖σ i‖ := by
  refine le_antisymm ?_ ?_
  · -- Upper bound via the factorisation.
    rw [DiagCLMpq_eq_comp]
    calc ‖(idEmbed p q).comp (DiagCLM q σ)‖
        ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ * ‖DiagCLM q σ‖ := opNorm_comp_le _ _
      _ ≤ 1 * ⨆ i, ‖σ i‖ := by
          rw [norm_DiagCLM]
          exact mul_le_mul_of_nonneg_right (norm_idEmbed_le_one hqp)
            (Real.iSup_nonneg fun i => norm_nonneg _)
      _ = ⨆ i, ‖σ i‖ := one_mul _
  · -- Lower bound: test on each basis vector.
    refine ciSup_le fun j => ?_
    have hDe : DiagCLMpq p q σ (PiLp.single q j (1 : 𝕜)) = PiLp.single p j (σ j) := by
      ext k
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [hk]
    have hbound := (DiagCLMpq p q σ).le_opNorm (PiLp.single q j (1 : 𝕜))
    rw [hDe, PiLp.norm_single, PiLp.norm_single, norm_one, mul_one] at hbound
    exact hbound
end SNumbers
