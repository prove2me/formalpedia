-- Prove2me | solution 1 for SNumbers.approximationNumber_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:00.048271+00:00
-- url     : https://prove2.me/submissions/e972e5be-666a-4003-a66c-385bad58499f

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_finiteDimensional_of_rank_le
public import Theorems.Thm_SNumbers_ne_top_of_rank_le_of_lt_rank
public import Theorems.Thm_SNumbers_nontrivial_of_natCast_lt_rank
attribute [local simp] ContinuousLinearMap.rank_zero


attribute [local simp] SNumbers.approximationNumber_zero_eq_norm

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
variable [CompleteSpace 𝕜]
namespace SNumbers
theorem _root_.solution {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    approximationNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have : Nontrivial X := nontrivial_of_natCast_lt_rank h
  have h_id_norm : ‖ContinuousLinearMap.id 𝕜 X‖ = 1 := norm_id
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- Upper bound: `a_n I ≤ ‖I − 0‖ = ‖I‖ = 1`.
    have h_zero_rank : (0 : X →L[𝕜] X).rank ≤ (n : Cardinal) := by simp
    calc approximationNumber I n
        ≤ ‖I - 0‖ := approximationNumber_le_norm_sub h_zero_rank
      _ = ‖I‖ := by rw [sub_zero]
      _ = 1 := h_id_norm
  · -- Lower bound: every `L` with `rank L ≤ n` satisfies `‖I − L‖ ≥ 1`.
    refine le_csInf (approximationSet_nonempty I n) ?_
    rintro _ ⟨L, hL, rfl⟩
    -- ===== Step A: `range L` is a closed proper subspace of `X`. =====
    set V : Submodule 𝕜 X := LinearMap.range (L : X →ₗ[𝕜] X) with hV_def
    -- `dim V ≤ rank L ≤ n < dim X`, so `V` is finite-dimensional and not all of `X`.
    have : FiniteDimensional 𝕜 V := finiteDimensional_of_rank_le hL
    have hV_ne_top : V ≠ ⊤ := ne_top_of_rank_le_of_lt_rank hL h
    -- Finite-dimensional subspaces are closed (uses `[CompleteSpace 𝕜]`).
    have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
    -- Properness gives some point outside `V`.
    have hV_exists : ∃ x : X, x ∉ V := by by_contra h; push Not at h; exact hV_ne_top (eq_top_iff.mpr fun x _ => h x)
    -- ===== Steps B–D: for every `r ∈ (0, 1)`, show `r ≤ ‖I − L‖`. =====
    have h_aux : ∀ r : ℝ, 0 < r → r < 1 → r ≤ ‖I - L‖ := by
      intro r _ hr1
      -- ----- Step B: Riesz's lemma at level `r < 1` produces `x₀`. -----
      obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists hr1
      -- `x₀ ∉ V`, in particular `x₀ ≠ 0`, so `‖x₀‖ > 0`.
      have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
      have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
      -- ----- Step C: `r * ‖x₀‖ ≤ ‖(I − L) x₀‖`. -----
      -- Specialise the Riesz distance bound to `y = L x₀ ∈ range L`.
      have h_apply : (I - L) x₀ = x₀ - L x₀ := by
        simp [hI_def, sub_apply, ContinuousLinearMap.id_apply]
      have h_riesz : r * ‖x₀‖ ≤ ‖x₀ - L x₀‖ :=
        hx₀_dist (L x₀) (LinearMap.mem_range_self _ _)
      have h_witness : r * ‖x₀‖ ≤ ‖(I - L) x₀‖ := by
        rw [h_apply]; exact h_riesz
      -- ----- Step D: divide by `‖x₀‖` after the operator-norm bound. -----
      -- `‖(I − L) x₀‖ ≤ ‖I − L‖ * ‖x₀‖` is the operator-norm inequality.
      have h_op : ‖(I - L) x₀‖ ≤ ‖I - L‖ * ‖x₀‖ := (I - L).le_opNorm x₀
      have h_chain : r * ‖x₀‖ ≤ ‖I - L‖ * ‖x₀‖ := h_witness.trans h_op
      -- Cancel the positive factor `‖x₀‖`.
      exact le_of_mul_le_mul_right h_chain hx₀_norm_pos
    -- ===== Step E: ε → 1 via `le_of_forall_pos_le_add`. =====
    -- We have `(1 - ε) ≤ ‖I − L‖` for every small `ε > 0`. Rephrase as
    -- `1 ≤ ‖I − L‖ + ε`; the `ε ≥ 1` case is trivial (RHS ≥ 0 + 1).
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hε1 : 1 ≤ ε
    · linarith [norm_nonneg (I - L)]
    have hε1' : ε < 1 := lt_of_not_ge hε1
    linarith [h_aux (1 - ε) (by linarith) (by linarith)]
end SNumbers
