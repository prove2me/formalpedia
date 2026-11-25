-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_khwVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:48.5534+00:00
-- url     : https://prove2.me/submissions/1b0029cd-4219-45f2-9b0a-dd78ce11bdea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_pair_hw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_hwTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  classical
  have hsum := sum_pair_hw hE (fun a b => ε b = ε a) (fun _ _ h => h.symm) hv.1
    (fun a b h hs => hv.2 a b h hs.symm)
  rw [casimirK, hsum, sum_hwTerm (fun a b => ε b = ε a) (fun _ => rfl) (fun _ _ h => h.symm) μ
    (rhoC ε)]
  intro a
  simp only [rhoC]
  ring
end ReciprocityTheory.ChartRestriction.DS
