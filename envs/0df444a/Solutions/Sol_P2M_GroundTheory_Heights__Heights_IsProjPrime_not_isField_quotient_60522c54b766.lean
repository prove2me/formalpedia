-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsProjPrime_not_isField_quotient_60522c54b766
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:21:52.497233+00:00
-- url     : https://prove2.me/submissions/7c0648f9-0f77-4fc9-b2ab-ec6691b3ca9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isHomogIdeal_ccff6c17f035

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
namespace GroundTheory.Heights₂.Heights
namespace IsProjPrime
theorem _root_.solution {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) :
    ¬ IsField (MvPolynomial (Fin n) F ⧸ P) := by
  intro hfield
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at hy
  have := constantCoeff_eq_zero_of_isHomogIdeal hP.isHomog hP.isPrime.ne_top hy
  simp at this
end IsProjPrime
end GroundTheory.Heights₂.Heights
