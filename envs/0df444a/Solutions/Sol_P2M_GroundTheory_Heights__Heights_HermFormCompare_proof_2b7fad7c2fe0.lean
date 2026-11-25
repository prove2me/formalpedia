-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermFormCompare_proof_2b7fad7c2fe0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:58.513794+00:00
-- url     : https://prove2.me/submissions/7e86c6a2-dfe3-4be3-a4ce-eca2b8cfd8fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_le_07935f5f434a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_ge_029b28a6484c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
open HermitianFormComparison
namespace GroundTheory.Heights₂.Heights
namespace HermFormCompare
theorem _root_.solution : HermFormCompare.Statement := by
  intro n M N hM hN
  set L : ℝ := 1 + ∑ k, hM.1.eigenvalues k with hL
  set m : ℝ := (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ with hm
  have hL0 : 0 < L := by
    have : 0 ≤ ∑ k, hM.1.eigenvalues k := Finset.sum_nonneg fun k _ => (hM.eigenvalues_pos k).le
    linarith
  have hm0 : 0 < m := by
    have : 0 ≤ ∑ k, (hN.1.eigenvalues k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (hN.eigenvalues_pos k)).le
    exact inv_pos.mpr (by linarith)
  refine ⟨L / m, div_pos hL0 hm0, fun x => ?_⟩
  have hup := re_quad_le hM.posSemidef x
  have hlo := re_quad_ge hN x
  calc (star x ⬝ᵥ (M *ᵥ x)).re ≤ L * (star x ⬝ᵥ x).re := hup
    _ = L / m * (m * (star x ⬝ᵥ x).re) := by field_simp
    _ ≤ L / m * (star x ⬝ᵥ (N *ᵥ x)).re :=
        mul_le_mul_of_nonneg_left hlo (div_pos hL0 hm0).le
end HermFormCompare
end GroundTheory.Heights₂.Heights
