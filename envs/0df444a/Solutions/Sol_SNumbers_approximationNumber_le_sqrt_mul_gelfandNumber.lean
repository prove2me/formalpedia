-- Prove2me | solution 1 for SNumbers.approximationNumber_le_sqrt_mul_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:21:10.536614+00:00
-- url     : https://prove2.me/submissions/3a0af161-4b0a-48e6-8457-6272cea0c4fb

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_deviationFromRestriction

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * gelfandNumber S n := by
  have hc_pos : (0 : ℝ) < 1 + Real.sqrt n := by positivity
  rw [← div_le_iff₀' hc_pos, gelfandNumber]
  refine le_csInf ⟨_, ⊤, by rw [Submodule.top_coe]; exact isClosed_univ,
    by rw [rank_zero_iff.mpr inferInstance]; exact bot_le, rfl⟩ ?_
  rintro r ⟨M, hM_closed, hM_codim, rfl⟩
  rw [div_le_iff₀' hc_pos]
  exact approximationNumber_le_sqrt_mul_deviationFromRestriction S hM_closed hM_codim
end SNumbers
