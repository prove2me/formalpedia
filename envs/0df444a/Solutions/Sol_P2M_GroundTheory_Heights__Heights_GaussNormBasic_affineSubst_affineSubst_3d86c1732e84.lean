-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_affineSubst_3d86c1732e84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:20.088219+00:00
-- url     : https://prove2.me/submissions/7ec222dc-328d-4c86-ba63-2b53922d411f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]
omit [IsUltrametricDist L]
namespace GroundTheory.Heights₂.Heights.GaussNormBasic
theorem _root_.solution {ι κ μ : Type*} [Fintype κ] [Fintype μ] (B : Matrix ι κ L)
    (a : ι → L) (B' : Matrix κ μ L) (a' : κ → L) (g : MvPolynomial ι L) :
    affineSubst B' a' (affineSubst B a g) = affineSubst (B * B') (B.mulVec a' + a) g := by
  have h : ∀ i, bind₁ (fun k ↦ ∑ l, C (B' k l) * X l + C (a' k))
      (∑ j, C (B i j) * X j + C (a i) : MvPolynomial κ L) =
      ∑ l, C ((B * B') i l) * X l + C ((B.mulVec a' + a) i) := by
    intro i
    simp only [map_add, map_sum, map_mul, bind₁_C_right, bind₁_X_right, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Pi.add_apply, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := μ))]
    ring
  unfold affineSubst
  rw [bind₁_bind₁]
  simp only [h]
end GroundTheory.Heights₂.Heights.GaussNormBasic
