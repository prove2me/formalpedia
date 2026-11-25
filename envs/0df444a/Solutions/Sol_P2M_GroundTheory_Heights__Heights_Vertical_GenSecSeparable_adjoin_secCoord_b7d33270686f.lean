-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_adjoin_secCoord_b7d33270686f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:08.948134+00:00
-- url     : https://prove2.me/submissions/41c0eab6-bb33-454e-b509-2e87070e6d23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable
theorem _root_.solution {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _
end GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable
