-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.factorAd_comm_factorAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:14.929516+00:00
-- url     : https://prove2.me/submissions/7c2051a5-a89b-481e-bc81-5fd4dd0674bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution {k : ℕ} {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by
  ext F : 1
  refine big_ext fun κ => ?_
  simp only [Module.End.mul_apply, factorAd_apply, Function.update_of_ne hij.symm,
    Function.update_of_ne hij, Function.update_comm hij]
  split_ifs <;> abel
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
