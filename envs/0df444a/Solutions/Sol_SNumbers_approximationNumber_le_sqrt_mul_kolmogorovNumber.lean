-- Prove2me | solution 1 for SNumbers.approximationNumber_le_sqrt_mul_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:21:53.205818+00:00
-- url     : https://prove2.me/submissions/275b37a0-7abd-43aa-ab81-dfcfb7c3453c

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
public import Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_deviationFromSubspace

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
    approximationNumber S n ≤ (1 + Real.sqrt n) * kolmogorovNumber S n := by
  have hc_pos : (0 : ℝ) < 1 + Real.sqrt n := by positivity
  rw [← div_le_iff₀' hc_pos, kolmogorovNumber]
  refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
  rintro r ⟨V, hV_rank, rfl⟩
  rw [div_le_iff₀' hc_pos]
  exact approximationNumber_le_sqrt_mul_deviationFromSubspace S hV_rank
end SNumbers
