-- Prove2me | solution 1 for SNumbers.bernsteinNumber_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:49:09.317996+00:00
-- url     : https://prove2.me/submissions/202faf89-fcfb-4586-9d23-e23ba0ceba37

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
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
private lemma gainOnSubspace_add_le (S T : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    (hM : M ≠ ⊥) :
    gainOnSubspace (S + T) M ≤ gainOnSubspace S M + ‖T‖ := by
  rw [← sub_le_iff_le_add]
  refine le_gainOnSubspace hM ?_
  intro x hx_mem hx_ne
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  -- `‖(S+T) x‖ / ‖x‖ ≤ ‖S x‖/‖x‖ + ‖T‖`, then chain through `gain (S+T) M`.
  have h_div : ‖(S + T) x‖ / ‖x‖ ≤ ‖S x‖ / ‖x‖ + ‖T‖ := by
    rw [show ‖S x‖ / ‖x‖ + ‖T‖ = (‖S x‖ + ‖T‖ * ‖x‖) / ‖x‖ from by
          rw [add_div, mul_div_cancel_right₀ _ hx_pos.ne'],
        div_le_div_iff_of_pos_right hx_pos]
    calc ‖(S + T) x‖
        = ‖S x + T x‖ := by rw [add_apply]
      _ ≤ ‖S x‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ ‖S x‖ + ‖T‖ * ‖x‖ := by linarith [T.le_opNorm x]
  linarith [gainOnSubspace_le_div (S := S + T) hx_mem hx_ne]
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
theorem _root_.solution (S T : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber (S + T) n ≤ bernsteinNumber S n + ‖T‖ := by
  refine Real.sSup_le ?_
    (add_nonneg (bernsteinNumber_nonneg S n) (norm_nonneg _))
  rintro _ ⟨M, hM_rank, rfl⟩
  have h1 : gainOnSubspace (S + T) M ≤ gainOnSubspace S M + ‖T‖ :=
    gainOnSubspace_add_le S T (rank_eq_succ_implies_ne_bot hM_rank)
  have h2 : gainOnSubspace S M ≤ bernsteinNumber S n :=
    le_csSup (bddAbove_bernsteinSet S n) ⟨M, hM_rank, rfl⟩
  linarith
end SNumbers
