-- Prove2me | solution 1 for SVD.IsApproximable.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:32.589138+00:00
-- url     : https://prove2.me/submissions/1dd7a5dd-af98-4629-a16c-27364bdee7dc

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationSet_nonempty
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



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
namespace SVD
namespace IsApproximable
theorem _root_.solution (c : 𝕜) {S : X →L[𝕜] Y}
    (hS : IsApproximable S) :
    IsApproximable (c • S) := by
  -- Pointwise bound: `aₙ(c • S) ≤ ‖c‖ * aₙ(S)`.
  have h_bd : ∀ n, SNumbers.approximationNumber (c • S) n ≤
                    ‖c‖ * SNumbers.approximationNumber S n := by
    intro n
    have h_nonneg : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
    -- Per-approximant: each `L : rank ≤ n` of `S` gives `c • L` of rank ≤ n
    -- approximating `c • S`, with residual `‖c‖ · ‖S - L‖`.
    have hkey : ∀ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) →
        SNumbers.approximationNumber (c • S) n ≤ ‖c‖ * ‖S - L‖ := by
      intro L hL
      have h_range_le :
          LinearMap.range ((c • L : X →L[𝕜] Y) : X →ₗ[𝕜] Y) ≤
            LinearMap.range (L : X →ₗ[𝕜] Y) := by
        rintro y ⟨x, hx⟩
        -- `hx : (c • L) x = y` reduces to `c • (L x) = y`, so
        -- `y = c • (L x) ∈ range L` by `Submodule.smul_mem`.
        have hx' : c • (L x) = y := hx
        rw [← hx']
        exact (LinearMap.range (L : X →ₗ[𝕜] Y)).smul_mem c
          (LinearMap.mem_range_self _ x)
      have h_rank : (c • L).rank ≤ (n : Cardinal) :=
        (Submodule.rank_mono h_range_le).trans hL
      have h_eq : c • S - c • L = c • (S - L) := (smul_sub c S L).symm
      have h_norm : ‖c • S - c • L‖ = ‖c‖ * ‖S - L‖ := by
        rw [h_eq, norm_smul]
      have h_residual : SNumbers.approximationNumber (c • S) n
                          ≤ ‖c • S - c • L‖ :=
        SNumbers.approximationNumber_le_norm_sub h_rank
      rwa [h_norm] at h_residual
    -- Lift to the infimum, mirroring `approximationNumber_comp_comp_le`.
    show _ ≤ ‖c‖ • SNumbers.approximationNumber S n
    show _ ≤ ‖c‖ • sInf (SNumbers.approximationSet S n)
    rw [← Real.sInf_smul_of_nonneg h_nonneg]
    refine le_csInf ((SNumbers.approximationSet_nonempty S n).image _) ?_
    rintro _ ⟨_, ⟨L, hL, rfl⟩, rfl⟩
    exact hkey L hL
  -- Squeeze: `0 ≤ aₙ(c•S) ≤ ‖c‖ · aₙ(S) → 0`.
  have h_nonneg : ∀ n, 0 ≤ SNumbers.approximationNumber (c • S) n :=
    fun n => SNumbers.approximationNumber_nonneg _ n
  have h_lim : Tendsto (fun n => ‖c‖ * SNumbers.approximationNumber S n)
                atTop (𝓝 0) := by
    simpa using hS.const_mul ‖c‖
  exact squeeze_zero h_nonneg h_bd h_lim
end IsApproximable
end SVD
