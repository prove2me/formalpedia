-- Prove2me | solution 1 for SVD.IsApproximable.isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:38:03.325805+00:00
-- url     : https://prove2.me/submissions/9e34800b-d368-4f7a-87b2-2f775233e105

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SVD_isApproximable_iff_existsLimit

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable [LocallyCompactSpace 𝕜] [CompleteSpace Y]
namespace SVD
namespace IsApproximable
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : IsApproximable S) : IsCompactOperator S := by
  rw [isApproximable_iff_existsLimit] at hS
  obtain ⟨L, hL_rank, hL_lim⟩ := hS
  -- Convert `‖S - L n‖ → 0` into `Tendsto L atTop (𝓝 S)` (op-norm convergence).
  have h_tendsto : Tendsto L atTop (𝓝 S) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_swap : (fun n => ‖L n - S‖) = (fun n => ‖S - L n‖) := by
      funext n; exact norm_sub_rev _ _
    rw [h_swap]; exact hL_lim
  -- Each `L n` is compact (finite-rank → compact).
  have h_each_compact : ∀ n, IsCompactOperator (L n) := by
    intro n
    -- `V := range (L n)` is finite-dim, hence proper / locally compact.
    set V : Submodule 𝕜 Y := LinearMap.range (L n : X →ₗ[𝕜] Y) with hV_def
    have h_rank_V_lt : Module.rank 𝕜 V < Cardinal.aleph0 :=
      lt_of_le_of_lt (hL_rank n) Cardinal.natCast_lt_aleph0
    have : FiniteDimensional 𝕜 V := Module.rank_lt_aleph0_iff.mp h_rank_V_lt
    have : ProperSpace V := FiniteDimensional.proper 𝕜 V
    -- Codrestrict `L n` to `V`.
    have hLn_mem : ∀ x, L n x ∈ V := fun x => ⟨x, rfl⟩
    let Ln' : X →L[𝕜] V := (L n).codRestrict V hLn_mem
    -- `Ln'` is compact (target locally compact).
    have h_Ln'_compact : IsCompactOperator Ln' :=
      isCompactOperator_of_locallyCompactSpace_dom Ln'
    -- `(V.subtypeL).comp Ln' = L n` as functions, so post-composition recovers `L n`.
    have h_compact_clm : IsCompactOperator (V.subtypeL.comp Ln') :=
      h_Ln'_compact.clm_comp V.subtypeL
    have h_eq : V.subtypeL.comp Ln' = L n := by ext x; rfl
    rw [h_eq] at h_compact_clm
    exact h_compact_clm
  -- Limit of compact operators is compact (closed-subset argument).
  exact isCompactOperator_of_tendsto h_tendsto
    (Filter.Eventually.of_forall h_each_compact)
end IsApproximable
end SVD
