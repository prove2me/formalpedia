-- Prove2me | solution 1 for SNumbers.L1Linf.one_div_le_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:43:27.751673+00:00
-- url     : https://prove2.me/submissions/2f18a3a7-d47f-4663-803b-29bb6e7f493d

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
public import Theorems.Thm_SNumbers_L1Linf_norm_emb1_le
public import Theorems.Thm_SNumbers_L1Linf_norm_projinf_le
public import Theorems.Thm_SNumbers_L1Linf_projinf_comp_incl_comp_emb1
public import Theorems.Thm_SNumbers_hilbertNumber_comp_comp_le
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_SNumbers_one_le_hilbertNumber_id


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (n : ℕ) :
    (1 : ℝ) / (n + 1) ≤ hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  set hI := hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n with hI_def
  have hmnn : (0 : ℝ) ≤ hI := hilbertNumber_nonneg _ _
  have hid := one_le_hilbertNumber_id (𝕜 := 𝕜) n
  have hideal := hilbertNumber_comp_comp_le (emb1 (n + 1))
    (incl : L1 𝕜 →L[𝕜] Linf 𝕜) (projinf (n + 1)) n
  rw [projinf_comp_incl_comp_emb1 (n + 1), ← hI_def] at hideal
  -- `1 ≤ hₙ(id) ≤ ‖proj∞‖ · hI · ‖emb1‖`.
  have h1 : (1 : ℝ)
      ≤ ‖(projinf (n + 1) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ * hI
        * ‖(emb1 (n + 1) : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L1 𝕜)‖ := hid.trans hideal
  -- `‖proj∞‖ · hI · ‖emb1‖ ≤ √(n+1) · hI · √(n+1) = (n+1) · hI`.
  have hbound : ‖(projinf (n + 1) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ * hI
      * ‖(emb1 (n + 1) : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L1 𝕜)‖
      ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * hI * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    gcongr
    · exact norm_projinf_le (𝕜 := 𝕜) (n + 1)
    · exact norm_emb1_le (𝕜 := 𝕜) (n + 1)
  have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) * hI * Real.sqrt ((n + 1 : ℕ) : ℝ)
      = ((n : ℝ) + 1) * hI := by
    rw [mul_right_comm, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) * hI := by
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ _ := hbound
      _ = ((n : ℝ) + 1) * hI := hsqrt
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [h3]
end SNumbers.L1Linf
