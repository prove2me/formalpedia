-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.starProjection_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:30.750639+00:00
-- url     : https://prove2.me/submissions/e9e8a5c4-5e4f-4886-832f-5c7d183a1442

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_orthogonal_kStable

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
theorem _root_.solution (hU : IsKUnitary ε A) {S : Submodule ℂ X} [S.HasOrthogonalProjection]
    (hS : IsKStableSub ε A S) {a b : Fin n} (hab : ε a = ε b) (x : X) :
    S.starProjection (A a b x) = A a b (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS a b hab _ (Submodule.starProjection_apply_mem S x)
  · intro w hw
    rw [← map_sub]
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have h2 := orthogonal_kStable hU hS a b hab _ h1
    rw [Submodule.mem_orthogonal] at h2
    rw [inner_eq_zero_symm]
    exact h2 w hw
end ReciprocityTheory.ChartRestriction.DS
