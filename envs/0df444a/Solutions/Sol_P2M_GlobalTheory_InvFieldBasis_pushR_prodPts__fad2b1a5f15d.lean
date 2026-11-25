-- Prove2me | solution 1 for P2M_GlobalTheory_InvFieldBasis_pushR_prodPts__fad2b1a5f15d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:20:24.735429+00:00
-- url     : https://prove2.me/submissions/07f2828a-a785-450e-8c07-8c0bd6b16f38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
import Theorems.Thm_GlobalTheory_LieBaseChange_pushR_bcVec
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapA_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]
namespace GlobalTheory.InvFieldBasis
theorem _root_.solution (v : Fin n → (epsR K ⟶ G)) (c : Fin n → C) :
    pushR G (Chart.prodPts c (bcVec C v)) =
      expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  unfold Chart.prodPts expPt
  have key : ∀ i, pushR G (Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i) =
      (Chart.spMap (epsTo K (inr (c i) : DualNumber C) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v i :
        sp (R₀ := K) (DualNumber C) ⟶ G) := by
    intro i
    rw [Chart.pushR_spMap, pushR_bcVec, ← Category.assoc, Chart.spMap_comp]
    congr 2
    apply DualNumber.algHom_ext
    change Chart.scaleD (c i) (Chart.dualMapA K C (inr 1)) = epsTo K (inr (c i) : DualNumber C) _ (inr 1)
    rw [Chart.dualMapA_inr, map_one]
    simp only [Chart.scaleD]
    rw [show (inr 1 : DualNumber K) = DualNumber.eps from rfl, epsTo_eps, TrivSqZeroExt.map_inr,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]
  calc pushR G _ = pushRHom G (DualNumber C)
        (List.ofFn fun i => Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i).prod := rfl
    _ = _ := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg List.prod (List.ofFn_inj.mpr (funext key))
end GlobalTheory.InvFieldBasis
