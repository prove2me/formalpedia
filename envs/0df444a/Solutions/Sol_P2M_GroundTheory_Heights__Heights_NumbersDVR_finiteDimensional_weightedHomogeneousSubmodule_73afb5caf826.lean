-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_finiteDimensional_weightedHomogeneousSubmodule_73afb5caf826
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:26.164306+00:00
-- url     : https://prove2.me/submissions/7e040888-41f3-4056-a290-ff8999173bb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_blockWeight_eq_7d351ef1e570

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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (F : Type u) [Field F] {K : Type}
    [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_blockWeight_eq ι m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})
end GroundTheory.Heights₂.Heights.NumbersDVR
