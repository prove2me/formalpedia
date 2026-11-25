-- Prove2me | solution 1 for SNumbers.gelfandNumber_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:26.021777+00:00
-- url     : https://prove2.me/submissions/34f47210-104c-415b-a2b9-96ee4faccc98

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
public import Theorems.Thm_SNumbers_gelfandSet_nonempty
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
public import Theorems.Thm_SNumbers_gelfandNumber_nonneg
public import Theorems.Thm_SNumbers_rank_quotient_inf_le
public import Theorems.Thm_SNumbers_deviationFromRestriction_comp_comap_inf_le
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
private lemma rank_quotient_comap_le (A : W →L[𝕜] X) (M : Submodule 𝕜 X) :
    Module.rank 𝕜 (W ⧸ M.comap (A : W →ₗ[𝕜] X)) ≤ Module.rank 𝕜 (X ⧸ M) := by
  -- The map `f : W →ₗ X/M`, `f w = mkQ (A w)`, has kernel `M.comap A`.
  -- Hence `W ⧸ ker f ≃ range f ≤ X/M`, giving the rank bound.
  set g : W →ₗ[𝕜] (X ⧸ M) := M.mkQ.comp (A : W →ₗ[𝕜] X) with hg_def
  have h_ker : LinearMap.ker g = M.comap (A : W →ₗ[𝕜] X) := by
    rw [hg_def, LinearMap.ker_comp, Submodule.ker_mkQ]
  -- Quotient by kernel is isomorphic to the range, hence has rank ≤ rank (X/M).
  calc Module.rank 𝕜 (W ⧸ M.comap (A : W →ₗ[𝕜] X))
      = Module.rank 𝕜 (W ⧸ LinearMap.ker g) := by rw [h_ker]
    _ = Module.rank 𝕜 (LinearMap.range g) :=
        (LinearMap.quotKerEquivRange g).rank_eq
    _ ≤ Module.rank 𝕜 (X ⧸ M) :=
        (LinearMap.range g).rank_le
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
theorem _root_.solution (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    gelfandNumber (S.comp T) (n + m) ≤ gelfandNumber S n * gelfandNumber T m := by
  -- one admissible subspace for each operator
  have hkey : ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) →
      Module.rank 𝕜 (Y ⧸ M) ≤ (n : Cardinal) →
      ∀ N : Submodule 𝕜 X, IsClosed (N : Set X) →
      Module.rank 𝕜 (X ⧸ N) ≤ (m : Cardinal) →
      gelfandNumber (S.comp T) (n + m) ≤
        deviationFromRestriction S M * deviationFromRestriction T N := by
    intro M hM_closed hM_rank N hN_closed hN_rank
    -- `T⁻¹(M)` is closed, as the preimage of a closed set under a continuous map
    have hM'_closed : IsClosed ((M.comap (T : X →ₗ[𝕜] Y)) : Set X) := by
      have : ((M.comap (T : X →ₗ[𝕜] Y)) : Set X) = T ⁻¹' (M : Set Y) := rfl
      rw [this]; exact hM_closed.preimage T.continuous
    have h_closed :
        IsClosed ((M.comap (T : X →ₗ[𝕜] Y) ⊓ N : Submodule 𝕜 X) : Set X) := by
      rw [Submodule.coe_inf]; exact hM'_closed.inter hN_closed
    have h_rank : Module.rank 𝕜 (X ⧸ (M.comap (T : X →ₗ[𝕜] Y) ⊓ N)) ≤
        ((n + m : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (rank_quotient_inf_le _ N).trans
        (add_le_add ((rank_quotient_comap_le T M).trans hM_rank) hN_rank)
    exact (gelfandNumber_le_deviation h_closed h_rank).trans
      (deviationFromRestriction_comp_comap_inf_le S T M N)
  -- For fixed `M`, take the infimum over `N`, pulling `‖S|_M‖ ≥ 0` inside it.
  have h1 : ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) →
      Module.rank 𝕜 (Y ⧸ M) ≤ (n : Cardinal) →
      gelfandNumber (S.comp T) (n + m) ≤
        deviationFromRestriction S M * gelfandNumber T m := by
    intro M hM_closed hM_rank
    show _ ≤ deviationFromRestriction S M • sInf (gelfandSet T m)
    rw [← Real.sInf_smul_of_nonneg (deviationFromRestriction_nonneg S M)]
    refine le_csInf ((gelfandSet_nonempty T m).image _) ?_
    rintro _ ⟨_, ⟨N, hN_closed, hN_rank, rfl⟩, rfl⟩
    exact hkey M hM_closed hM_rank N hN_closed hN_rank
  -- Then take the infimum over `M`, pulling `c_m(T) ≥ 0` inside it.
  rw [mul_comm]
  show _ ≤ gelfandNumber T m • sInf (gelfandSet S n)
  rw [← Real.sInf_smul_of_nonneg (gelfandNumber_nonneg T m)]
  refine le_csInf ((gelfandSet_nonempty S n).image _) ?_
  rintro _ ⟨_, ⟨M, hM_closed, hM_rank, rfl⟩, rfl⟩
  show _ ≤ gelfandNumber T m * deviationFromRestriction S M
  rw [mul_comm]
  exact h1 M hM_closed hM_rank
end SNumbers
