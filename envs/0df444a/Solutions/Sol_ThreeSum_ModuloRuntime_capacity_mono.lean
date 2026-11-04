-- Prove2me | solution 1 for ThreeSum.ModuloRuntime.capacity_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:52.715484+00:00
-- url     : https://prove2.me/submissions/5946792d-eb64-47e1-b23f-dcf523ab3597

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface
namespace ThreeSum.ModuloRuntime
theorem _root_.solution {p q : ℕ} (h : p ≤ q) : capacity p ≤ capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)
end ThreeSum.ModuloRuntime
