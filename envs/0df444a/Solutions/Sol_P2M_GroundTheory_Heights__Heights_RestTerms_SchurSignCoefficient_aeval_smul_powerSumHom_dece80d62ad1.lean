-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_aeval_smul_powerSumHom_dece80d62ad1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:02.381408+00:00
-- url     : https://prove2.me/submissions/bf4ba9bc-de58-4d12-bf9c-51d3cdfb05a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchurSignCoefficient

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchurSignCoefficient
theorem _root_.solution (N : ℕ) (s : ℚ)
    (S : MvPolynomial (Fin N) ℚ) :
    aeval (fun i : Fin N => C s * X i) (powerSumHom N S) =
      powerSumHom N (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S) := by
  have key : (aeval (fun i : Fin N => C s * X i)).comp (powerSumHom N) =
      (powerSumHom N).comp (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, powerSumHom, aeval_X, map_mul, aeval_C, algebraMap_eq, psum,
      map_sum, map_pow, mul_pow, Finset.mul_sum]
  exact DFunLike.congr_fun key S
end SchurSignCoefficient
end GroundTheory.Heights₂.Heights.RestTerms
