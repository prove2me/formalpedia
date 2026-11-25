-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:20.931802+00:00
-- url     : https://prove2.me/submissions/28479cee-ef68-4b24-8611-c626cbea879b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace MinimalPrimeMultiHomog
theorem _root_.solution : MinimalPrimeMultiHomog.Statement := by
  intro R _ K _ _ ι J W hJ hW
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal.IsPrime := hWp.homogeneousCore
  have hJle : J ≤ (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) hW.1.2
  have hle : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal ≤ W := Ideal.toIdeal_homogeneousCore_le (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) W
  have heq : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal = W := le_antisymm hle (hW.2 ⟨hcore, hJle⟩ hle)
  apply isMultiHomogIdeal_of_isHomogeneous_lex e
  rw [← heq]
  exact (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).isHomogeneous
end MinimalPrimeMultiHomog
end GroundTheory.Heights₂.Heights.NumbersDVR
