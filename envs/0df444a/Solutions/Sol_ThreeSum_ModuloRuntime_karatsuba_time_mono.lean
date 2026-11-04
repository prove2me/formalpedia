-- Prove2me | solution 1 for ThreeSum.ModuloRuntime.karatsuba_time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:30.901058+00:00
-- url     : https://prove2.me/submissions/04c1cafd-af8e-46a5-b297-df0fe616711e

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface
namespace ThreeSum.ModuloRuntime
theorem _root_.solution : Monotone LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [LightKaratsuba.time]
  omega
end ThreeSum.ModuloRuntime
