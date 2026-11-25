-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_eq_mul_ratios_73d28504c04b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:55:21.347187+00:00
-- url     : https://prove2.me/submissions/a5fd1374-c01b-43b1-b909-3a4912f38e6d

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
theorem _root_.solution (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (p : Ix κ) :
    x p = x ⟨(), c⟩ * (ratioField x c).subtype (ratios x c p) := by
  change x p = x ⟨(), c⟩ * (x p / x ⟨(), c⟩)
  rw [mul_div_cancel₀ _ hc]
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
