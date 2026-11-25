-- Prove2me | solution 1 for P2M_GlobalTheory_GenIsoRatio_gm_pull_g__f1a988516116
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:20.740598+00:00
-- url     : https://prove2.me/submissions/8aca10f1-8d6d-442e-a52e-0ad26d08b804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalUnitRatioGenericLineBundleIsos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GenIsoRatio
namespace GlobalTheory.GenIsoRatio
theorem _root_.solution {X Y : Scheme.{0}} (β : Y ⟶ X) (L : LB X) (y : Y) (i i' : L.ι) (hi : β y ∈ L.U i)
    (hi' : β y ∈ L.U i') :
    gm (𝟙 Y) y ((L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i'))
      ((L.pull β).g (fun _ => i) (fun _ => i')) = gm β y (L.U i ⊓ L.U i') (L.g i i') := by
  have hp : y ∈ (L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU β _ (L.g i i'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) β y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _).trans (by rw [Category.id_comp]))
end GlobalTheory.GenIsoRatio
