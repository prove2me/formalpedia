-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_ratios_c_873ba0532ef9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:11.107341+00:00
-- url     : https://prove2.me/submissions/9d7b3521-59bd-41e1-8c9e-3242b79b3fc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]
omit [Fintype κ]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) : ratios x c ⟨(), c⟩ = 1 :=
  Subtype.ext (div_self hc)
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
