-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.factorAd_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:54.494023+00:00
-- url     : https://prove2.me/submissions/73970ce8-2ab0-4267-8ae1-94b73883d0f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
variable {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b =
      (if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0) := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
  simp only [hbc, hda, if_true, if_false, LinearMap.sub_apply, LinearMap.zero_apply,
    Module.End.mul_apply, PiLp.sub_apply, PiLp.zero_apply, factorAd_apply, Function.update_self,
    Function.update_idem] <;>
  generalize κ i = p <;>
  obtain ⟨p1, p2⟩ := p <;>
  simp only <;>
  split_ifs <;> subst_vars <;> first | rfl | abel1 | (simp_all <;> abel1) | simp_all
end ReciprocityTheory.ChartRestriction.DS
