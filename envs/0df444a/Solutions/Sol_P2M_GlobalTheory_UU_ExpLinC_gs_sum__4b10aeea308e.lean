-- Prove2me | solution 1 for P2M_GlobalTheory_UU_ExpLinC_gs_sum__4b10aeea308e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:59.393618+00:00
-- url     : https://prove2.me/submissions/ab2bbc40-32a6-4eec-aba3-0534853eff33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalLincomb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLinC
namespace GlobalTheory.UU.ExpLinC
theorem _root_.solution {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hm : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(Y, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := gs_add r z U hm 0 0
    rw [add_zero] at h
    simpa using h
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gs_add r z U hm, ih]
end GlobalTheory.UU.ExpLinC
