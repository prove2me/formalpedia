-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:28.130624+00:00
-- url     : https://prove2.me/submissions/71cdd0eb-c213-454c-a065-14b501394517

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {pp qq : Ideal R} [pp.IsPrime] (h : pp < qq) :
    ringKrullDim (R ⧸ qq) + 1 ≤ ringKrullDim (R ⧸ pp) := by
  obtain ⟨r, hrq, hrp⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk pp r ∈ nonZeroDivisors (R ⧸ pp) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk pp r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hrq, mul_zero]
  have := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hker (Ideal.Quotient.factor_surjective h.le))
  gcongr
end GroundTheory.Heights₂.Heights.Kleiman
