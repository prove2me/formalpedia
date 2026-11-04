-- Prove2me | solution 1 for ThreeSum.ModuloRuntime.depth_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:32.491402+00:00
-- url     : https://prove2.me/submissions/bfba7d65-6b8a-445c-b1c3-53fefed386fd

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface
namespace ThreeSum.ModuloRuntime
theorem _root_.solution {p q : ℕ} (h : p ≤ q) (d : ℕ) :
    d+Nat.clog 2 p+3 ≤ d+Nat.clog 2 q+3 := by
  have hlog := Nat.clog_mono_right 2 h
  omega
end ThreeSum.ModuloRuntime
