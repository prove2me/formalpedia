-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_mk_4e3d1e4fb648
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:51.124972+00:00
-- url     : https://prove2.me/submissions/cb506210-53fd-4b71-b019-6fd7df75cffe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J)
    (q : MvPolynomial (Fin n) ℂ) : evalAt J hz (Ideal.Quotient.mk J q) = eval z q := by
  simp [evalAt]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
