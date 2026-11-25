-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormDimLe_ringKrullDim_eq_of_comap_8e644d83cbeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:07.912394+00:00
-- url     : https://prove2.me/submissions/d89ce843-823c-4272-8a60-52f3cc122812

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_eq_of_isIntegral


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
open GroundTheory.Heights₂.Heights.ChowFormDimLe
namespace GroundTheory.Heights₂.Heights.ChowFormDimLe
theorem _root_.solution {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : P.LiesOver I := ⟨hPI.symm⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))
end GroundTheory.Heights₂.Heights.ChowFormDimLe
