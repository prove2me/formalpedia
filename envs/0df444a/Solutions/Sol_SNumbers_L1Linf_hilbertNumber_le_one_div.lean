-- Prove2me | solution 1 for SNumbers.L1Linf.hilbertNumber_le_one_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:46:33.668399+00:00
-- url     : https://prove2.me/submissions/6b587c64-cdf2-4813-ab1c-c4f48a4fece9

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
public import Theorems.Thm_SNumbers_L1Linf_approximationNumber_comp_incl_comp_le
public import Theorems.Thm_SNumbers_hilbertNumber_def


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (n : ℕ) :
    hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ (1 : ℝ) / (n + 1) := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (by positivity)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  have h := approximationNumber_comp_incl_comp_le A B n
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h
  rw [div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [h]
end SNumbers.L1Linf
