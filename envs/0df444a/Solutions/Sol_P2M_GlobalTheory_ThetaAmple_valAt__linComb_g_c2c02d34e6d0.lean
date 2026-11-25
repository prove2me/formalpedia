-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaAmple_valAt__linComb_g_c2c02d34e6d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:25.913102+00:00
-- url     : https://prove2.me/submissions/bbfc82d8-7edb-486c-b975-298f6de64d23

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272
import Theorems.Thm_P2M_GlobalTheory_valAt__units_prod_4b684ea369c1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple
namespace GlobalTheory.ThetaAmple
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) {N : ℕ} (j j' : Fin N → L.ι) (x : Sp ℂ ⟶ Y)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j ⊓
      (LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j')) :
    valAt' x _ ((LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).g j j').val =
      ∏ k, valAt' (x ≫ φ) _ (L.g (j k) (j' k)).val := by
  refine (valAt'_units_prod x h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_one]
  exact (valAt'_map x _ _ h).trans (valAt'_comp x φ (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)
end GlobalTheory.ThetaAmple
