-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:24.021717+00:00
-- url     : https://prove2.me/submissions/29a6d576-c620-4b70-8a63-a5e0f18f22c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace lmul
theorem _root_.solution (P Q : Kleiman.SubSystem S x Ω) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.lmul S (toIndefiniteRowSideFullHecke P) (toIndefiniteRowSideFullHecke Q) i = toIndefiniteRowSideFullHecke (P.twist Q) i := by
  rw [IndefiniteRowSideFullHecke.Kleiman.lmul, chartModule_of_ne_zero _ h, chartModule_of_ne_zero _ h, chartModule_of_ne_zero _ h]
  exact mul_eq_twist P Q _
end lmul
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
