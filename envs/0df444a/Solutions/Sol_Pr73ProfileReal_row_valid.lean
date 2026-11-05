-- Prove2me | solution 1 for Pr73ProfileReal.row_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/94142c2c-cd0a-45de-b9da-e1284faeed74

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal
import Theorems.Thm_Pr73ProfileCertificate_rows_checked


set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate
namespace Pr73ProfileReal
theorem _root_.solution (r : Row) (hr : r ∈ rows) : valid r := by
  have h := List.all_eq_true.mp rows_checked r hr
  exact of_decide_eq_true h
end Pr73ProfileReal
