-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.psiPoly_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:01.150708+00:00
-- url     : https://prove2.me/submissions/0887fa34-cbfb-4f2f-b848-df27dd08d358

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segMono_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
  have hmem : psiPoly Ψ j ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => 1) := by
    unfold psiPoly
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (segMono_homog i))
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp hmem
end ReciprocityTheory.ChartRestriction.G.Geo
