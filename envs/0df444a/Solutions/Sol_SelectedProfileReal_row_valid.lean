-- Prove2me | solution 1 for SelectedProfileReal.row_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/06aeffcc-1402-47c9-9fb3-606bbc8a7032

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
import Theorems.Thm_SelectedProfileCertificate_rows_checked


set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
namespace SelectedProfileReal
theorem _root_.solution (r : Row) (hr : r ∈ rows) : valid r := by
  have h := List.all_eq_true.mp rows_checked r hr
  exact of_decide_eq_true h
end SelectedProfileReal
