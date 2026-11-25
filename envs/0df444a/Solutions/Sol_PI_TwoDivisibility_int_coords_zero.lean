-- Prove2me | solution 1 for PI.TwoDivisibility.int_coords_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:44.501372+00:00
-- url     : https://prove2.me/submissions/1228c814-3c5d-4c05-9479-dcfdaa4d2a37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TwoDivisibility
namespace PI.TwoDivisibility
theorem _root_.solution (L : PeriodPair) (x y : ℤ)
    (h : (x : ℂ) * L.ω₁ + (y : ℂ) * L.ω₂ = 0) : x = 0 ∧ y = 0 := by
  have := LinearIndependent.pair_iff.mp L.indep (x : ℝ) (y : ℝ)
    (by rw [Complex.real_smul, Complex.real_smul]; push_cast; exact h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
end PI.TwoDivisibility
