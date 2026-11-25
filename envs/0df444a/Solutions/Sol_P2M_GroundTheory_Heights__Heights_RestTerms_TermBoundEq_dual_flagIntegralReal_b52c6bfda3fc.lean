-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_dual_flagIntegralReal_b52c6bfda3fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:55.994019+00:00
-- url     : https://prove2.me/submissions/475ba01e-9b86-49e5-94c0-61480aab821f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)
namespace GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
theorem _root_.solution (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    φ (flagIntegralReal f N P) = flagIntegral f N (coeffMap φ P) := by
  have hterm : ∀ α : Fin f × Fin N →₀ ℕ,
      coeff α P * ((coeff α (blockVandermonde f N) : ℚ) : ℝ) *
          α.prod (fun _ e => (e.factorial : ℝ)) =
        (coeff α (blockVandermonde f N) * α.prod (fun _ e => (e.factorial : ℚ))) • coeff α P := by
    intro α
    rw [Rat.smul_def]
    simp only [Finsupp.prod, Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast]
    ring
  show φ (∑ α ∈ _, _) = _
  simp only [hterm, map_sum, map_smul, smul_eq_mul, flagIntegral, coeff_coeffMap]
  exact sum_congr rfl fun α _ => by ring
end GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
