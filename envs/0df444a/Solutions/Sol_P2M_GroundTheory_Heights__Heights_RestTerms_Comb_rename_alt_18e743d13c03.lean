-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_rename_alt_18e743d13c03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:26.728798+00:00
-- url     : https://prove2.me/submissions/6f0f86a2-0272-48c5-8ff9-932d79b4cae5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (v : Fin m → ℕ) (σ : Perm (Fin m)) :
    rename σ (alt v) = (Perm.sign σ : ℤ) • alt v := by
  unfold alt
  rw [AlgHom.map_det, zsmul_eq_mul, ← Matrix.det_permute]
  congr 1
  ext i j
  simp [Matrix.submatrix]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
