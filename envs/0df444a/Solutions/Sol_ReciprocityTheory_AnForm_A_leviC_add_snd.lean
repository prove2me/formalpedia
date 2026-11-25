-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.leviC_add_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:20.788988+00:00
-- url     : https://prove2.me/submissions/407dbe8d-5572-4702-b5c6-72a4bf10a59f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {e : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a b b' : Fin e → ℂ) :
    leviC H a (b + b') = leviC H a b + leviC H a b' := by
  simp only [leviC, smul_add, map_add]
  push_cast
  ring
end ReciprocityTheory.AnForm.A
