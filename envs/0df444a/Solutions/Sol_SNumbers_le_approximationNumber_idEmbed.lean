-- Prove2me | solution 1 for SNumbers.le_approximationNumber_idEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:16.070705+00:00
-- url     : https://prove2.me/submissions/7fe59a6e-76c1-48d0-8f57-94182806c4b2

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_exists_norm_ratio_ge_idEmbed
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_finrank_piLp
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply


attribute [local simp] SNumbers.idEmbed_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
      ≤ approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n := by
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro r ⟨L, hL, rfl⟩
  -- The kernel of a rank-`≤ n` operator has dimension `≥ m - n`.
  have hker : m - n ≤ Module.finrank 𝕜 (LinearMap.ker (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) := by
    have hrn := (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜]
      PiLp p (fun _ : Fin m => 𝕜)).finrank_range_add_finrank_ker
    have hrange : Module.finrank 𝕜 (LinearMap.range (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) ≤ n :=
      Module.finrank_le_of_rank_le hL
    rw [finrank_piLp] at hrn
    omega
  obtain ⟨x, hxV, hxne, hxbound⟩ := exists_norm_ratio_ge_idEmbed hpq hq hn
    (LinearMap.ker (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) hker
  have hLx : L x = 0 := LinearMap.mem_ker.mp hxV
  have happ : (idEmbed (𝕜 := 𝕜) (m := m) p q - L) x = idEmbed p q x := by
    simp [sub_apply, hLx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  refine le_of_mul_le_mul_right ?_ hxpos
  calc ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖
      ≤ ‖idEmbed p q x‖ := hxbound
    _ = ‖(idEmbed (𝕜 := 𝕜) (m := m) p q - L) x‖ := by rw [happ]
    _ ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q - L‖ * ‖x‖ :=
        (idEmbed (𝕜 := 𝕜) (m := m) p q - L).le_opNorm x
end SNumbers
