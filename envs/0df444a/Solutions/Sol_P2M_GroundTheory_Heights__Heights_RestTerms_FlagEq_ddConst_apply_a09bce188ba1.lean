-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:12:05.947211+00:00
-- url     : https://prove2.me/submissions/180b8acc-878b-4023-80fa-1a24c2156a16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      coeff (rho f (j + k)) (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) := by
  simp [IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho,
    IndefiniteRowSideFullHecke.RestTerms.rhoMon, coeff_sum, coeff_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
