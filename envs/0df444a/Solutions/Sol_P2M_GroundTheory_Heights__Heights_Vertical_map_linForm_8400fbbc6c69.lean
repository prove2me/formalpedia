-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_map_linForm_8400fbbc6c69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:39.204953+00:00
-- url     : https://prove2.me/submissions/1b420c4f-9b97-47c8-afcf-5b00876e4a87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecLength

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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (u : Fin n → R) :
    (linForm u).map φ = linForm (fun j => φ (u j)) := by
  simp only [linForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
end GroundTheory.Heights₂.Heights.Vertical
