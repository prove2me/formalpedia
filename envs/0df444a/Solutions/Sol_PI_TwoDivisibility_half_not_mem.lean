-- Prove2me | solution 1 for PI.TwoDivisibility.half_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:17.949843+00:00
-- url     : https://prove2.me/submissions/7b8082c0-9194-49cc-8fe1-7e2dad81e585

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
theorem _root_.solution (L : PeriodPair) (p q : ℤ) (h : ¬ ((2 : ℤ) ∣ p ∧ (2 : ℤ) ∣ q)) :
    (p : ℂ) / 2 * L.ω₁ + (q : ℂ) / 2 * L.ω₂ ∉ L.lattice := by
  intro hm
  obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.mp hm
  have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - (p : ℝ) / 2) ((n : ℝ) - (q : ℝ) / 2)
    (by rw [Complex.real_smul, Complex.real_smul]; push_cast; linear_combination e)
  apply h
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · have h1 : (p : ℝ) = 2 * m := by linarith [this.1]
    exact_mod_cast h1
  · have h2 : (q : ℝ) = 2 * n := by linarith [this.2]
    exact_mod_cast h2
end PI.TwoDivisibility
