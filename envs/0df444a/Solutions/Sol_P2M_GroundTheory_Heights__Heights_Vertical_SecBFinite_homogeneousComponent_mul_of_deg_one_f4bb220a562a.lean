-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mul_of_deg_one_f4bb220a562a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:22.013875+00:00
-- url     : https://prove2.me/submissions/98276975-9dd8-413e-98b7-54037f406101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {σ R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (c t : MvPolynomial σ R) (ht : t.IsHomogeneous 1) (d : ℕ) :
    homogeneousComponent (d + 1) (c * t) = homogeneousComponent d c * t := by
  have key : ∀ (x : MvPolynomial σ R) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ R) x i : MvPolynomial σ R) =
        homogeneousComponent i x :=
    fun x i => decomposition.decompose'_apply x i
  have h := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule σ R) (a := c)
    (n := d + 1) ((mem_homogeneousSubmodule 1 t).mpr ht) (by omega)
  rw [key, key, Nat.add_sub_cancel] at h
  exact h
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
