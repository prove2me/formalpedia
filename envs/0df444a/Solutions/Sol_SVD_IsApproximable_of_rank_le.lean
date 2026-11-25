-- Prove2me | solution 1 for SVD.IsApproximable.of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:38:01.573742+00:00
-- url     : https://prove2.me/submissions/854c9ba8-ec2e-4d11-9757-d77c37cdaac1

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SNumbers_approximationNumber_eq_zero_of_rank_le


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
theorem _root_.solution {S : X →L[𝕜] Y} {N : ℕ}
    (hS : S.rank ≤ (N : Cardinal)) : IsApproximable S := by
  -- `aₙ S = 0` for `n ≥ N`, so the sequence is eventually zero.
  have h_eventually :
      (fun n => SNumbers.approximationNumber S n) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact SNumbers.approximationNumber_eq_zero_of_rank_le
      (hS.trans (by exact_mod_cast hn))
  exact (tendsto_congr' h_eventually).mpr tendsto_const_nhds
end IsApproximable
end SVD
