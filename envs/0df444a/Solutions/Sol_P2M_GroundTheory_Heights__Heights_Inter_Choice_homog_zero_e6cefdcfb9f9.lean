-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_zero_e6cefdcfb9f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:32:44.94718+00:00
-- url     : https://prove2.me/submissions/5edabd03-60ba-49af-8563-24aff082516c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.Choice
theorem _root_.solution (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by
  intro m hm
  simp at hm
end GroundTheory.Heights₂.Heights.Inter.Choice
