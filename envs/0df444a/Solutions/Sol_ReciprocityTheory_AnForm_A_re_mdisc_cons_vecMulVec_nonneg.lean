-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.re_mdisc_cons_vecMulVec_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:35.676808+00:00
-- url     : https://prove2.me/submissions/765cdc0d-25b3-42b4-90fb-aef188574970

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_nonneg_of_posSemidef


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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (a : Fin (n + 1) → ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).PosSemidef) :
    0 ≤ (mdisc (Fin.cons (vecMulVec a (star a)) B :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
  refine (mdisc_nonneg_of_posSemidef _ fun k => ?_).2
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using posSemidef_vecMulVec_self_star a
  · simpa using hB i
end ReciprocityTheory.AnForm.A
