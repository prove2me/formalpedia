-- Prove2me | solution 1 for SelectedProfileReal.power_term_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/5519c179-a61a-444a-b6a2-6ca5f70493cc

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal

set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
namespace SelectedProfileReal
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
end SelectedProfileReal
