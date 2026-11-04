-- Prove2me | solution 1 for ThreeSum.Asymptotics.log_nat_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:58:17.100794+00:00
-- url     : https://prove2.me/submissions/218e27bd-d110-48fb-a663-adf0cd3ababc

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_Asymptotics

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.Asymptotics
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
end ThreeSum.Asymptotics
