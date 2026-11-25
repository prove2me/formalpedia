-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.isPsh_locallyIntegrable_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:53.321921+00:00
-- url     : https://prove2.me/submissions/080de35f-1da5-47e3-994b-c073393aac24

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_plurisubharmonicLocallyIntegrable_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Set Filter Topology Real PshInh
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : IsPsh_locallyIntegrableStatement :=
  PshMean.plurisubharmonicLocallyIntegrable_holds
end ReciprocityTheory.AnForm.A
