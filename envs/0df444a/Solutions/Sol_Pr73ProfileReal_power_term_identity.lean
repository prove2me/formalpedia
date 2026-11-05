-- Prove2me | solution 1 for Pr73ProfileReal.power_term_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/274c9d54-a268-4270-a7a8-befcff854cf9

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal

set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate
namespace Pr73ProfileReal
theorem _root_.solution (n t m W a : ℝ) (ht : 0 < t) (hm : 0 < m) :
    (n / W) * (t / m) ^ (1 - a) =
      (n * t / (m * W)) * Real.exp (a * Real.log (m / t)) := by
  have hratio : 0 < t / m := div_pos ht hm
  have hlog : Real.log (t / m) = -Real.log (m / t) := by
    rw [Real.log_div ht.ne' hm.ne', Real.log_div hm.ne' ht.ne']
    ring
  have hpow : (t / m) ^ (1 - a) = (t / m) * Real.exp (a * Real.log (m / t)) := by
    rw [Real.rpow_def_of_pos hratio]
    have he : Real.log (t / m) * (1 - a) =
        Real.log (t / m) + a * Real.log (m / t) := by rw [hlog]; ring
    rw [he, Real.exp_add, Real.exp_log hratio]
  rw [hpow]
  ring
end Pr73ProfileReal
