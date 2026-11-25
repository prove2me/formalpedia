-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_one_le_det_one_add_bb3f4c9f8b7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:42.694718+00:00
-- url     : https://prove2.me/submissions/8d82de78-dc6c-40cc-b3b2-05dd5a3defe7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PHermitianDetMono
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Matrix
open scoped ComplexOrder MatrixOrder
namespace GroundTheory.Heights₂.Heights.FourB
namespace HermitianDetMono
theorem _root_.solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) : 1 ≤ (1 + M).det := by
  have hH : (1 + M).IsHermitian := isHermitian_one.add hM.isHermitian
  have hev : ∀ i, (1 : ℝ) ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i]
    have hv : star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [add_mulVec, one_mulVec, dotProduct_add, map_add, hv, RCLike.one_re]
    linarith [hM.re_dotProduct_nonneg (hH.eigenvectorBasis i)]
  rw [hH.det_eq_prod_eigenvalues]
  have hprod : (1 : ℝ) ≤ ∏ i, hH.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hH.eigenvalues i :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hev i)
  have key : ((1 : ℝ) : ℂ) ≤ ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := Complex.real_le_real.mpr hprod
  convert key using 1
  · simp
  · simp [Complex.ofReal_prod]
end HermitianDetMono
end GroundTheory.Heights₂.Heights.FourB
