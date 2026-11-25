-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_isSymmetric_aeval_smul_X_3d12ee5aa775
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:43.370592+00:00
-- url     : https://prove2.me/submissions/62778d44-abfd-470d-9c14-b16f537e9c07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorFormula

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution {N : ℕ} (s : ℚ) {p : MvPolynomial (Fin N) ℚ} (hp : p.IsSymmetric) :
    (aeval (fun i : Fin N => C s * X i) p).IsSymmetric := by
  intro e
  have key : (rename e).comp (aeval (fun i : Fin N => C s * X i)) =
      (aeval (fun i : Fin N => C s * X i)).comp (rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have := congrArg (fun φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ p) key
  simp only [AlgHom.comp_apply] at this
  rw [this, hp e]
end GroundTheory.Heights₂.Heights.RestTerms.Top
