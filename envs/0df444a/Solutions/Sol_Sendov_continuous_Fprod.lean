-- Prove2me | solution 1 for Sendov.continuous_Fprod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:10.257024+00:00
-- url     : https://prove2.me/submissions/4ec2ebce-d5dc-4a43-876d-c5bb136e1f39

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_continuous_prodC

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) (q : Multiset ℂ) : Continuous (Fprod a q) :=
  continuous_prodC a q
end Sendov
