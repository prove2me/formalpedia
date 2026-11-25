-- Prove2me | solution 1 for ReciprocityTheory.AnForm.integrable_fsDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:34.160172+00:00
-- url     : https://prove2.me/submissions/b28e4007-5d3c-491e-a696-1f91c16bd8a2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Theorems.Thm_ReciprocityTheory_AnForm_integral_fsDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution : Integrable fsDens :=
  .of_integral_ne_zero (by rw [integral_fsDens]; exact one_ne_zero)
end ReciprocityTheory.AnForm
