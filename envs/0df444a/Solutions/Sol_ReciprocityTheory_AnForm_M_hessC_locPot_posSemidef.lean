-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hessC_locPot_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:17.317046+00:00
-- url     : https://prove2.me/submissions/3d2943e3-f9a9-4bdd-bdd3-4fb82a522721

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posSemidef_of_levi
import Theorems.Thm_ReciprocityTheory_AnForm_M_pot_contDiffAt_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (hPsh : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) :
    (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef := by
  exact hessC_posSemidef_of_levi _ y (pot_contDiffAt_two hP _ j hy (P.mem_U _))
    (fun w => hPsh _ j y ⟨hy, P.mem_U _⟩ w)
end ReciprocityTheory.AnForm.M
