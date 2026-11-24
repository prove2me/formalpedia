-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_quot_sup_add_one_le_814a859d861d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:51.871257+00:00
-- url     : https://prove2.me/submissions/c84d0447-a1cd-40d2-bfff-b193bc8d8365

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH

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
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (g : MvPolynomial (Fin n) ℂ) (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
