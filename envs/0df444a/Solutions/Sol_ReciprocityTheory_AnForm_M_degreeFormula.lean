-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.degreeFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:53:45.736533+00:00
-- url     : https://prove2.me/submissions/60635753-faa5-4c9d-a269-cf70fda09277

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_degreeFormulaInt
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
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : DegreeFormulaStatement := by
  intro e X Y _ _ _ _ _ _ A B h hh d S hd Φ hΦ g hg
  have hI : MIntegrable A Φ g := by
    intro j K hK hKc
    have h1 : ContinuousOn (fun y => g ((A.chart j).symm y)) K :=
      hg.comp_continuousOn ((A.chart j).continuousOn_symm.mono hK)
    have h2 : ContinuousOn (locDens A Φ j) K := (locDensCont A Φ hΦ j).mono hK
    exact (h1.mul h2).integrableOn_compact hKc
  exact (degreeFormulaInt A B h hh d S hd Φ hΦ g hI).2
end ReciprocityTheory.AnForm.M
