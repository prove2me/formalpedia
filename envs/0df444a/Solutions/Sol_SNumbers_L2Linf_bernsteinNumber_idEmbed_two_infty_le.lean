-- Prove2me | solution 1 for SNumbers.L2Linf.bernsteinNumber_idEmbed_two_infty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:55:15.729794+00:00
-- url     : https://prove2.me/submissions/1f54e368-c20e-41bf-9bbb-093ccbf07098

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_sqrt_le_norm_toLp_two
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_exists_flat_vector
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
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
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution (N n : ℕ) :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := N) ∞ 2) n ≤ 1 / Real.sqrt (n + 1) := by
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- transport `M` to `Fin N → 𝕜` and pick a flat vector there
  set e : PiLp 2 (fun _ : Fin N => 𝕜) ≃ₗ[𝕜] (Fin N → 𝕜) :=
    WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜) with he
  have hkV : n + 1 ≤ Module.finrank 𝕜
      (M.map (e : PiLp 2 (fun _ : Fin N => 𝕜) →ₗ[𝕜] (Fin N → 𝕜))) := by
    rw [LinearEquiv.finrank_map_eq, Module.finrank_eq_of_rank_eq hM_rank]
  obtain ⟨w, hwV, hw0, hwle, hwcard⟩ := exists_flat_vector (k := n + 1) (by omega) hkV
  obtain ⟨v, hvM, hev⟩ := Submodule.mem_map.mp hwV
  have hxM : (WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜)) ∈ M := by
    rw [← hev]; simpa [he] using hvM
  have hx0 : (WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜)) ≠ 0 := fun h =>
    hw0 (by simpa using congrArg WithLp.ofLp h)
  -- `‖x‖_∞ ≤ 1` and `‖x‖₂ ≥ √(n+1)`
  have hnum : ‖idEmbed (𝕜 := 𝕜) (m := N) ∞ 2 (WithLp.toLp 2 w)‖ ≤ 1 := by
    rw [← PiLp.norm_ofLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => hwle i
  have hden : Real.sqrt (n + 1) ≤ ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by
    have h := sqrt_le_norm_toLp_two w hwcard
    push_cast at h
    exact h
  have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  calc gainOnSubspace (idEmbed (𝕜 := 𝕜) (m := N) ∞ 2) M
      ≤ ‖idEmbed (𝕜 := 𝕜) (m := N) ∞ 2 (WithLp.toLp 2 w)‖ /
          ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := gainOnSubspace_le_div hxM hx0
    _ ≤ 1 / ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by gcongr
    _ ≤ 1 / Real.sqrt (n + 1) := one_div_le_one_div_of_le hsqrt hden
end SNumbers.L2Linf
