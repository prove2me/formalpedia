-- Prove2me | solution 1 for ThreeSumApsp.tendsto_ceil_rpow_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:00:23.055394+00:00
-- url     : https://prove2.me/submissions/be3e2da6-5fe7-4962-8bfd-c308b14a6cfb

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n : ℕ => ⌈(n : ℝ) ^ μ⌉₊) atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_rpow_atTop hμ).comp tendsto_natCast_atTop_atTop)
end ThreeSumApsp
