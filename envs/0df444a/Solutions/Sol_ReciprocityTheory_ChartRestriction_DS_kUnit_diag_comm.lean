-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kUnit_diag_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:25.856575+00:00
-- url     : https://prove2.me/submissions/9ed738a7-a0ef-4a35-9fac-a8fd958279c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary

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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) (a c : Fin n) (v : X) :
    A a a (A c c v) = A c c (A a a v) := by
  have h := LinearMap.congr_fun (hA a a c c) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  by_cases hac : a = c
  · subst hac; rfl
  · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
    exact h
end ReciprocityTheory.ChartRestriction.DS
