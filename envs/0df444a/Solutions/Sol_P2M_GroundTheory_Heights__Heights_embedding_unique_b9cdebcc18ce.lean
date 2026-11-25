-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_embedding_unique_b9cdebcc18ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:26.350698+00:00
-- url     : https://prove2.me/submissions/54da65f4-f3ff-4189-9d3e-cc640866a632

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
    (hφ : IsDualBasis F.lattice φ) {σ σ' : K →+* ℂ} {w w' : Fin (r + 1) → ℂ} (hw : w ≠ 0)
    (h : latticePoint φ σ w = latticePoint φ σ' w') : σ = σ' := by
  have key : ∀ j a, σ a * w j = σ' a * w' j := by
    intro j a
    obtain ⟨D, hD, c, hc⟩ := exists_int_comb hφ (Pi.single j a)
    have h1 := sum_latticePoint σ w hc
    have h2 := sum_latticePoint σ' w' hc
    rw [h, h2, sum_single_mul, sum_single_mul] at h1
    exact (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD) h1).symm
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (funext hc)
  have hw' : w j = w' j := by simpa using key j 1
  ext a
  have h3 := key j a
  rw [← hw'] at h3
  exact mul_right_cancel₀ hj h3
end GroundTheory.Heights₂.Heights
