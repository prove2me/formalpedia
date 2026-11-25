-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_finrank_eq_59867f7e7a5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:30.813503+00:00
-- url     : https://prove2.me/submissions/248efcc3-0dba-4bd0-90fa-7deb958dbdf9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph

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
noncomputable section
open MvPolynomial
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FrameImplicitGraph
theorem _root_.solution (I : Finset (Fin n)) :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℂ ((I → ℂ) × ({j // j ∉ I} → ℂ)) := by
  have h1 : Fintype.card {j // j ∉ I} = n - I.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  have h2 : I.card ≤ n := by simpa using I.card_le_univ
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    h1, Fintype.card_coe]
  omega
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
