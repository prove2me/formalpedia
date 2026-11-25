-- Prove2me | solution 1 for SNumbers.exists_triangular_system_hilbert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:34.013383+00:00
-- url     : https://prove2.me/submissions/e173f1f5-9390-480d-958e-36ce10e08f5d

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
public import Theorems.Thm_SNumbers_exists_next_vector
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
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] H) {n : ℕ}
    {γ : ℝ} (hγ : 0 < γ) (hγc : γ < gelfandNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ e : Fin m → X,
      (∀ j, ‖S (e j)‖ = 1) ∧ (∀ j, ‖e j‖ ≤ 1 / γ) ∧
      (∀ i j : Fin m, i < j → inner 𝕜 (S (e i)) (S (e j)) = 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, (fun j => j.elim0), (fun j => j.elim0), (fun i => i.elim0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨e', h1, h2, h3⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨em, _, hSem, hemn, _, _, hker⟩ :=
      exists_next_vector S hγ hγc (Nat.le_of_succ_le_succ hk)
        (fun i => (innerSL 𝕜 (S (e' i)) : H →L[𝕜] 𝕜))
    refine ⟨Fin.snoc e' em, ?_, ?_, ?_⟩
    · intro j; induction j using Fin.lastCases with
      | last => simpa using hSem
      | cast j' => simpa using h1 j'
    · intro j; induction j using Fin.lastCases with
      | last => simpa using hemn
      | cast j' => simpa using h2 j'
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hi : i ≠ Fin.last k := ne_of_lt (hij.trans (Fin.castSucc_lt_last j'))
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact h3 i' j' (Fin.castSucc_lt_castSucc_iff.mp hij)
      · have hi : i ≠ Fin.last k := ne_of_lt hij
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        have hk0 := hker i'
        simpa using hk0
end SNumbers
