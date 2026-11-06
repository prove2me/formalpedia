-- Prove2me | solution 1 for RH.Transport.Geometry.lowExponent_eq_signal_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:55:43.44801+00:00
-- url     : https://prove2.me/submissions/4ba69cc3-8be7-4f6a-a1a1-c00c15b43f8e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_signal_eq
import Theorems.Thm_RH_Transport_Geometry_lowExponent_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution (p : ℝ) :
    lowExponent p = signal p (boundary p) := by
  rw [lowExponent_eq, signal_eq]
  dsimp [boundary]
  ring
end RH.Transport.Geometry
