-- Prove2me | solution 1 for ThreeSum.ModuloRuntime.space_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:03.806178+00:00
-- url     : https://prove2.me/submissions/dd448e76-9e84-40fc-ba22-93b396551578

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Theorems.Thm_ThreeSum_ModuloRuntime_capacity_mono

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface
namespace ThreeSum.ModuloRuntime
theorem _root_.solution {p q : ℕ} (h : p ≤ q) (free N U : ℕ) :
    space free p N U ≤ space free q N U := by
  have hc := capacity_mono h
  unfold space
  omega
end ThreeSum.ModuloRuntime
