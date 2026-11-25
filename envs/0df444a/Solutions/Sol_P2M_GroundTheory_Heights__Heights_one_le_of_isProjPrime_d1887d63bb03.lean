-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_one_le_of_isProjPrime_d1887d63bb03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:10.992919+00:00
-- url     : https://prove2.me/submissions/3610fac4-0a89-47c4-9c1c-bf14aa4fc2b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isProjPrime_3532aee1cba7

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
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    (hk : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exfalso
    have := hP.isPrime
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := by
      rw [ringKrullDimZero_iff_ringKrullDim_eq_zero]
      simpa using hk
    have hmax : P.IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
    have hle : P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F) :=
      fun f hf => constantCoeff_eq_zero_of_isProjPrime hP hf
    have heq := hmax.eq_of_le (RingHom.ker_ne_top _) hle
    obtain ⟨j, hj⟩ := hP.isRelevant
    rw [heq] at hj
    exact hj (by simp [RingHom.mem_ker])
  · exact h
end GroundTheory.Heights₂.Heights
