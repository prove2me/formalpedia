-- Prove2me | solution 1 for SNumbers.exists_next_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:50:43.865792+00:00
-- url     : https://prove2.me/submissions/17cf906a-02b1-4802-8dbe-f786f1afee9a

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
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL



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
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγc : γ < gelfandNumber S n) {m : ℕ} (hm : m ≤ n) (ρ' : Fin m → (Y →L[𝕜] 𝕜)) :
    ∃ (em : X) (ρm : Y →L[𝕜] 𝕜),
      ‖S em‖ = 1 ∧ ‖em‖ ≤ 1 / γ ∧ ‖ρm‖ = 1 ∧ ρm (S em) = (‖S em‖ : 𝕜) ∧
      (∀ i : Fin m, ρ' i (S em) = 0) := by
  classical
  set Φ : X →L[𝕜] (Fin m → 𝕜) := ContinuousLinearMap.pi (fun i => (ρ' i).comp S) with hΦ
  have hΦapp : ∀ x i, Φ x i = ρ' i (S x) := by intro x i; simp [hΦ]
  set N : Submodule 𝕜 X := LinearMap.ker (Φ : X →ₗ[𝕜] (Fin m → 𝕜)) with hN
  have hN_closed : IsClosed (N : Set X) := Φ.isClosed_ker
  have hN_rank : Module.rank 𝕜 (X ⧸ N) ≤ (n : Cardinal) := by
    have heq : Module.rank 𝕜 (X ⧸ N)
        = Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin m → 𝕜))) :=
      (Φ : X →ₗ[𝕜] (Fin m → 𝕜)).quotKerEquivRange.rank_eq
    rw [heq]
    calc Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin m → 𝕜)))
        ≤ Module.rank 𝕜 (Fin m → 𝕜) := Submodule.rank_le _
      _ = (m : Cardinal) := rank_fin_fun m
      _ ≤ (n : Cardinal) := by exact_mod_cast hm
  have hdev : γ < ‖S.comp N.subtypeL‖ :=
    lt_of_lt_of_le hγc (gelfandNumber_le_deviation hN_closed hN_rank)
  obtain ⟨ξ, hξ1, hξγ⟩ := (S.comp N.subtypeL).exists_lt_apply_of_lt_opNorm hdev
  set u : X := (ξ : X) with hu
  have hSu : γ < ‖S u‖ := hξγ
  have hSu_pos : 0 < ‖S u‖ := lt_trans hγ hSu
  have hu_le : ‖u‖ ≤ 1 := le_of_lt hξ1
  have hΦu0 : Φ u = 0 := LinearMap.mem_ker.mp ξ.2
  set em : X := ((‖S u‖ : 𝕜))⁻¹ • u with hem
  have hSem : ‖S em‖ = 1 := by
    rw [hem, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hSu_pos,
      inv_mul_cancel₀ hSu_pos.ne']
  have hem_norm : ‖em‖ ≤ 1 / γ := by
    rw [hem, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hSu_pos]
    calc (‖S u‖)⁻¹ * ‖u‖
        ≤ (‖S u‖)⁻¹ * 1 := by apply mul_le_mul_of_nonneg_left hu_le (by positivity)
      _ = (‖S u‖)⁻¹ := mul_one _
      _ ≤ 1 / γ := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hγ hSu.le
  have hem_ker : ∀ i : Fin m, ρ' i (S em) = 0 := by
    intro i
    have hui : ρ' i (S u) = 0 := by rw [← hΦapp u i, hΦu0]; rfl
    rw [hem, map_smul, map_smul, hui, smul_zero]
  obtain ⟨ρm, hρm_norm, hρm_app⟩ :=
    exists_dual_vector (𝕜 := 𝕜) (S em) (ne_of_eq_of_ne hSem one_ne_zero)
  exact ⟨em, ρm, hSem, hem_norm, hρm_norm, hρm_app, hem_ker⟩
end SNumbers
