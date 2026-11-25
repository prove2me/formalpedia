-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.logNormIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:34.029888+00:00
-- url     : https://prove2.me/submissions/3e9c32aa-837d-4099-af7a-5c77e8f83582

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_logNormIntegrable_of
import Theorems.Thm_ReciprocityTheory_AnForm_A_logUnitMonoLocInt_thm
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : LogNormIntegrableStatement :=
  logNormIntegrable_of ReciprocityTheory.AnForm.A.logUnitMonoLocInt_thm locDensCont
end ReciprocityTheory.AnForm.M
