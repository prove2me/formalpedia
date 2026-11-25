-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapAd.prod_ofFn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:02.070417+00:00
-- url     : https://prove2.me/submissions/3c342127-5038-476b-8cbd-1784857b27d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.CapAd
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd
theorem _root_.solution : ∀ {p : ℕ} (s : Fin p → ℂ) (a : Fin p → 𝒰),
    (List.ofFn fun j => s j • a j).prod = (∏ j, s j) • (List.ofFn a).prod
  | 0, s, a => by simp
  | p + 1, s, a => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [solution (fun j => s j.succ) (fun j => a j.succ), Fin.prod_univ_succ, smul_mul_smul_comm]
end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
