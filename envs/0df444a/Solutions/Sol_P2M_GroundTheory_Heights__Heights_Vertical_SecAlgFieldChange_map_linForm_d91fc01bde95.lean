-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_map_linForm_d91fc01bde95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:06.354912+00:00
-- url     : https://prove2.me/submissions/98ae7315-673e-4ee6-bbbc-778633a33581

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange

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
open scoped TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
namespace GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (u : Fin n → R) : MvPolynomial.map φ (linForm u) = linForm (φ ∘ u) := by
  simp [linForm]
end GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
