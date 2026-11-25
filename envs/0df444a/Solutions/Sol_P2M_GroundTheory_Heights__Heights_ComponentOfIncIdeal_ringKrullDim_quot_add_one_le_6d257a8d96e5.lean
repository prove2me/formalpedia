-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:26.347961+00:00
-- url     : https://prove2.me/submissions/a120fae3-67e8-47a9-bf29-6c744dcba0fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
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
open GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
namespace GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
theorem _root_.solution {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (hPQ : P ≤ Q) (hne : P ≠ Q) : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPQ hne)
  have hne' : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h0
    have hx : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hxQ
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hxP hx
  have h := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne'
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)] at h
end GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
