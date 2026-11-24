-- Prove2me | solution 1 for PositivityTheory.Sph.M2.GenA.conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:54.530833+00:00
-- url     : https://prove2.me/submissions/4d420abe-9c05-482e-88e4-d1d18962f6a9

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace PositivityTheory.Sph.M2.GenA
theorem _root_.solution (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {g a b : GL n K} (h : g * a = b * g) : ψ a = ψ b := by
  have := congrArg ψ h
  rw [map_mul, map_mul, mul_comm] at this
  exact mul_right_cancel₀ (hpos g).ne' this
end PositivityTheory.Sph.M2.GenA
