-- Prove2me | solution 1 for SNumbers.approximationNumber_DiagCLMpq_le_of_exponent_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:27.964677+00:00
-- url     : https://prove2.me/submissions/1c43ede1-050b-4bdb-b827-eb51a7a16898

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
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le


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
theorem _root_.solution (hqp : q ≤ p) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p q σ) n ≤ ‖σ ⟨n, hn⟩‖ := by
  have : Nonempty (Fin m) := ⟨⟨n, hn⟩⟩
  rw [DiagCLMpq_eq_comp]
  calc approximationNumber ((idEmbed p q).comp (DiagCLM q σ)) n
      = approximationNumber ((idEmbed p q).comp ((DiagCLM q σ).comp
          (ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin m => 𝕜))))) n := by
        rw [ContinuousLinearMap.comp_id]
    _ ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ * approximationNumber (DiagCLM q σ) n
          * ‖ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin m => 𝕜))‖ :=
        approximationNumber_comp_comp_le _ _ _ _
    _ = ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ * ‖σ ⟨n, hn⟩‖
          * ‖ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin m => 𝕜))‖ := by
        rw [approximationNumber_DiagCLM_eq hσ hn]
    _ ≤ 1 * ‖σ ⟨n, hn⟩‖ * 1 := by
        gcongr
        · exact norm_idEmbed_le_one hqp
        · exact norm_id_le
    _ = ‖σ ⟨n, hn⟩‖ := by ring
end SNumbers
