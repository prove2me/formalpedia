-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.isCurve_iff_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:30.895229+00:00
-- url     : https://prove2.me/submissions/7076c2ff-47ca-45af-b591-e40c681dbb45

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptPsIsInt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {ga : Fin d → PowerSeries C} : IsCurve v ga ↔ PTGood v ga := by
  constructor
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mp (h a).2⟩
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mpr (h a).2⟩
end ReciprocityTheory.ChartRestriction.G.Sh
