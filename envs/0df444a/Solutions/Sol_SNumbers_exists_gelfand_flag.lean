-- Prove2me | solution 1 for SNumbers.exists_gelfand_flag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:18.885732+00:00
-- url     : https://prove2.me/submissions/4dfa19e6-76f8-4e20-927b-47bb5661e6b2

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
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
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_exists_next_vector
public import Theorems.Thm_SNumbers_padFin_apply
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
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγc : γ < gelfandNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (x : Fin m → X) (ρ : Fin m → (Y →L[𝕜] 𝕜)),
      (∀ j, ‖x j‖ ≤ 1) ∧ (∀ j, ‖ρ j‖ ≤ 1) ∧
      (∀ j, ρ j (S (x j)) = ((γ : ℝ) : 𝕜)) ∧
      (∀ i j : Fin m, i < j → ρ i (S (x j)) = 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, (fun j => j.elim0), (fun j => j.elim0),
      (fun j => j.elim0), (fun i => i.elim0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨x', ρ', hx'norm, hρ'norm, hρ'diag, hρ'tri⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨em, ρm, hSem, hem_norm, hρm_norm, hρm_diag, hker⟩ :=
      exists_next_vector S hγ hγc (Nat.le_of_succ_le_succ hk) ρ'
    have hxm_norm : ‖((γ : ℝ) : 𝕜) • em‖ ≤ 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hγ]
      calc γ * ‖em‖ ≤ γ * (1 / γ) := mul_le_mul_of_nonneg_left hem_norm hγ.le
        _ = 1 := by field_simp
    have hxm_diag : ρm (S (((γ : ℝ) : 𝕜) • em)) = ((γ : ℝ) : 𝕜) := by
      rw [map_smul, map_smul, hρm_diag, hSem]
      simp
    have hxm_ker : ∀ i : Fin k, ρ' i (S (((γ : ℝ) : 𝕜) • em)) = 0 := by
      intro i
      rw [map_smul, map_smul, hker i, smul_zero]
    refine ⟨Fin.snoc x' (((γ : ℝ) : 𝕜) • em), Fin.snoc ρ' ρm, ?_, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hxm_norm
      | cast j' => simpa using hx'norm j'
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hρm_norm.le
      | cast j' => simpa using hρ'norm j'
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hxm_diag
      | cast j' => simpa using hρ'diag j'
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hi : i ≠ Fin.last k := ne_of_lt (hij.trans (Fin.castSucc_lt_last j'))
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hρ'tri i' j' (Fin.castSucc_lt_castSucc_iff.mp hij)
      · have hi : i ≠ Fin.last k := ne_of_lt hij
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact hxm_ker i'
end SNumbers
