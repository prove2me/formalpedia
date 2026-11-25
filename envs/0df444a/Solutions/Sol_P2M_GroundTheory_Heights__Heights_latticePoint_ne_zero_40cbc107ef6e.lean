-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticePoint_ne_zero_40cbc107ef6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:42.255843+00:00
-- url     : https://prove2.me/submissions/7e31d5ce-6588-47e4-8515-7635c3b0ffea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) {w : Fin (r + 1) → ℂ} (hw : w ≠ 0) :
    latticePoint φ σ w () ≠ 0 := by
  intro h0
  apply hw
  funext j
  obtain ⟨D, hD, c, hc⟩ := exists_int_comb hφ (Pi.single j 1)
  have h := sum_latticePoint σ w hc
  rw [h0, sum_single_mul] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, map_one, one_mul] at h
  change w j = 0
  exact (mul_eq_zero.mp h.symm).resolve_left (Int.cast_ne_zero.mpr hD)
end GroundTheory.Heights₂.Heights
