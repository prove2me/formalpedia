-- Prove2me | solution 1 for SNumbers.bernsteinNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:55:13.28325+00:00
-- url     : https://prove2.me/submissions/58bfc048-13ae-4a34-8020-041f2efaa253

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
private lemma rank_eq_succ_implies_ne_bot {M : Submodule 𝕜 X} {n : ℕ}
    (hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal)) :
    M ≠ ⊥ := fun hM_bot => by
  rw [hM_bot, rank_bot] at hM_rank
  exact Nat.succ_ne_zero n (by exact_mod_cast hM_rank.symm)
private lemma gainOnSubspace_comp_comp_le_of_injective
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) {M : Submodule 𝕜 W}
    (hM : M ≠ ⊥) (h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0) :
    gainOnSubspace (B.comp (S.comp A)) M ≤
      ‖B‖ * ‖A‖ * gainOnSubspace S (M.map (A : W →ₗ[𝕜] X)) := by
  by_cases hBA : ‖B‖ * ‖A‖ = 0
  · -- `‖B‖ * ‖A‖ = 0`. Either `‖B‖ = 0` (so `B = 0` and `BSA = 0`), or
    -- `‖A‖ = 0` (which is incompatible with `M ≠ ⊥` and `h_inj`).
    rw [hBA, zero_mul]
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    rcases mul_eq_zero.mp hBA with hB | hA
    · have hB_zero : B = 0 := norm_eq_zero.mp hB
      have h_zero : B.comp (S.comp A) = 0 := by rw [hB_zero, zero_comp]
      rw [h_zero]
      refine (gainOnSubspace_le_div (S := (0 : W →L[𝕜] Z)) hx_mem hx_ne).trans ?_
      rw [zero_apply, norm_zero, zero_div]
    · exfalso
      apply h_inj x hx_mem hx_ne
      rw [norm_eq_zero.mp hA, zero_apply]
  · -- `‖B‖ * ‖A‖ > 0`. The main case.
    have hBA_pos : 0 < ‖B‖ * ‖A‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hBA)
    set M' : Submodule 𝕜 X := M.map (A : W →ₗ[𝕜] X)
    have hM'_ne_bot : M' ≠ ⊥ := by
      obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
      intro hM'_bot
      have : A x ∈ M' := ⟨x, hx_mem, rfl⟩
      rw [hM'_bot, Submodule.mem_bot] at this
      exact h_inj x hx_mem hx_ne this
    -- Show `gain (BSA) M / (‖B‖‖A‖) ≤ gain S M'`.
    suffices h_div :
        gainOnSubspace (B.comp (S.comp A)) M / (‖B‖ * ‖A‖) ≤
          gainOnSubspace S M' by
      rw [div_le_iff₀ hBA_pos] at h_div
      linarith [mul_comm (‖B‖ * ‖A‖) (gainOnSubspace S M')]
    refine le_gainOnSubspace hM'_ne_bot ?_
    rintro _ ⟨x, hx_mem, rfl⟩ hAx_ne
    -- `A x ≠ 0` ⇒ `x ≠ 0` (since `A 0 = 0`).
    have hx_ne : x ≠ 0 := fun h => hAx_ne (by rw [h, map_zero])
    have hAx_pos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx_ne
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    -- `‖(BSA) x‖/‖x‖ ≤ ‖B‖‖A‖ * ‖S(A x)‖/‖A x‖`.
    have h_per_vec :
        ‖(B.comp (S.comp A)) x‖ / ‖x‖ ≤
          ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) := by
      rw [div_le_iff₀ hx_pos]
      calc ‖(B.comp (S.comp A)) x‖
          = ‖B (S (A x))‖ := rfl
        _ ≤ ‖B‖ * ‖S (A x)‖ := B.le_opNorm _
        _ = ‖B‖ * (‖S (A x)‖ / ‖A x‖) * ‖A x‖ := by
            rw [mul_assoc, div_mul_cancel₀ _ hAx_pos.ne']
        _ ≤ ‖B‖ * (‖S (A x)‖ / ‖A x‖) * (‖A‖ * ‖x‖) := by
            gcongr; exact A.le_opNorm x
        _ = ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) * ‖x‖ := by ring
    rw [div_le_iff₀ hBA_pos]
    calc gainOnSubspace (B.comp (S.comp A)) M
        ≤ ‖(B.comp (S.comp A)) x‖ / ‖x‖ := gainOnSubspace_le_div hx_mem hx_ne
      _ ≤ ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) := h_per_vec
      _ = ‖S (A x)‖ / ‖A x‖ * (‖B‖ * ‖A‖) := by ring
private lemma rank_map_of_injective_on
    (A : W →L[𝕜] X) {M : Submodule 𝕜 W}
    (h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0) :
    Module.rank 𝕜 (M.map (A : W →ₗ[𝕜] X)) = Module.rank 𝕜 M := by
  -- `f := A.domRestrict M : M →ₗ X` has range `M.map A` and trivial kernel.
  set f : M →ₗ[𝕜] X := (A : W →ₗ[𝕜] X).domRestrict M with hf_def
  have h_inj_f : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx_mem⟩ hx_ker
    by_contra hx_ne_zero
    exact h_inj x hx_mem (fun h => hx_ne_zero (by ext; exact h)) hx_ker
  rw [← LinearMap.range_domRestrict M (A : W →ₗ[𝕜] X)]
  exact (LinearEquiv.ofInjective f h_inj_f).rank_eq.symm
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    bernsteinNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * bernsteinNumber S n * ‖A‖ := by
  refine Real.sSup_le ?_
    (mul_nonneg (mul_nonneg (norm_nonneg _) (bernsteinNumber_nonneg _ _))
      (norm_nonneg _))
  rintro _ ⟨M, hM_rank, rfl⟩
  have hM_ne_bot : M ≠ ⊥ := rank_eq_succ_implies_ne_bot hM_rank
  by_cases h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0
  · -- Injective case.
    set M' : Submodule 𝕜 X := M.map (A : W →ₗ[𝕜] X)
    have hM'_rank : Module.rank 𝕜 M' = ((n + 1 : ℕ) : Cardinal) := by
      rw [rank_map_of_injective_on A h_inj, hM_rank]
    calc gainOnSubspace (B.comp (S.comp A)) M
        ≤ ‖B‖ * ‖A‖ * gainOnSubspace S M' :=
          gainOnSubspace_comp_comp_le_of_injective A S B hM_ne_bot h_inj
      _ ≤ ‖B‖ * ‖A‖ * bernsteinNumber S n :=
          mul_le_mul_of_nonneg_left
            (le_csSup (bddAbove_bernsteinSet S n) ⟨M', hM'_rank, rfl⟩)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖B‖ * bernsteinNumber S n * ‖A‖ := by ring
  · -- Non-injective case: some nonzero `x ∈ M` has `A x = 0`, so `(BSA) x = 0`.
    simp only [not_forall, Classical.not_not, ne_eq] at h_inj
    obtain ⟨x, hx_mem, hx_ne, hAx_zero⟩ := h_inj
    have h_zero : ‖B.comp (S.comp A) x‖ / ‖x‖ = 0 := by
      show ‖B (S (A x))‖ / ‖x‖ = 0
      rw [hAx_zero, map_zero, map_zero, norm_zero, zero_div]
    linarith [(gainOnSubspace_le_div hx_mem hx_ne).trans (le_of_eq h_zero),
      mul_nonneg (mul_nonneg (norm_nonneg B) (bernsteinNumber_nonneg S n))
        (norm_nonneg A)]
end SNumbers
