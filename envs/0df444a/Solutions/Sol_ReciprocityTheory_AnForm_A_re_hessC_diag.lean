-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.re_hessC_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:32.542585+00:00
-- url     : https://prove2.me/submissions/2d46d9fa-805c-40c7-a85e-fb288f81b9f0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (j : Fin D) :
    (hessC f z j j).re = levi f z (Pi.single j 1) := by
  simp [hessC, levi, Complex.div_ofNat_re]
end ReciprocityTheory.AnForm.A
