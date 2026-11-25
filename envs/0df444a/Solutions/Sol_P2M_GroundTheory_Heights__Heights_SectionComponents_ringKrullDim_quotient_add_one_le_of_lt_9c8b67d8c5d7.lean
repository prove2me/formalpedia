-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_le_of_lt_9c8b67d8c5d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:12:19.951342+00:00
-- url     : https://prove2.me/submissions/7f68f884-afc8-48e5-aace-27c7223ec85d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionComponents
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le


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
open GroundTheory.Heights₂.Heights.SectionComponents
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SectionComponents
theorem _root_.solution {W' W : Ideal (MvPolynomial (Fin n) F)}
    [W'.IsPrime] (hlt : W' < W) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W') := by
  set p : Ideal (MvPolynomial (Fin n) F ⧸ W') := W.map (Ideal.Quotient.mk W')
  have hp : p ≠ ⊥ := by
    obtain ⟨x, hxW, hxW'⟩ := SetLike.exists_of_lt hlt
    intro h
    apply hxW'
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk W' x ∈ p := Ideal.mem_map_of_mem _ hxW
    rwa [h, Ideal.mem_bot] at this
  have hquot : ringKrullDim ((MvPolynomial (Fin n) F ⧸ W') ⧸ p) =
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)
  have := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le p hp
  rwa [hquot] at this
end GroundTheory.Heights₂.Heights.SectionComponents
