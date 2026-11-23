-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.hasFDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:32.488875+00:00
-- url     : https://prove2.me/submissions/3017913f-8b2f-488f-b0b0-bcd17d75fd9a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (z w : Fin D → ℂ) (ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => z + ζ • w) (L0 w) ζ :=
  ((hasFDerivAt_id ζ).smul_const w).const_add z
end ReciprocityTheory.AnForm.A.PshLap
