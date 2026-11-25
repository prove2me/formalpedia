-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_aeval_C_mul_X_injective_c5ce1551daa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:23.513402+00:00
-- url     : https://prove2.me/submissions/77caf54b-daa4-4369-ae3e-26c39200dc69

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie

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
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution {c : Ω} (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (R := Ω) (Polynomial.C c * Polynomial.X)) := by
  have h : (Polynomial.aeval (R := Ω) (Polynomial.C c⁻¹ * Polynomial.X)).comp
      (Polynomial.aeval (Polynomial.C c * Polynomial.X)) = AlgHom.id Ω (Polynomial Ω) := by
    refine Polynomial.algHom_ext ?_
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  exact Function.LeftInverse.injective (g := Polynomial.aeval (Polynomial.C c⁻¹ * Polynomial.X))
    fun p => by rw [← AlgHom.comp_apply, h, AlgHom.id_apply]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
