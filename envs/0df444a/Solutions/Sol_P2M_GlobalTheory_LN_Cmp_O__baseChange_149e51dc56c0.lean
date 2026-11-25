-- Prove2me | solution 1 for P2M_GlobalTheory_LN_Cmp_O__baseChange_149e51dc56c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:16.886404+00:00
-- url     : https://prove2.me/submissions/edf0d2e1-756c-45ab-a88b-3c056e44c01b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsComparisonCompAlongIdentity
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.Cmp
namespace GlobalTheory.LN.Cmp
theorem _root_.solution {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {x' : D'.X} {x : D.X}
    (hc : (D'.c x').left ≫ β = spMap φ ≫ (D.c x).left)
    {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of V))}
    (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left) (hp : p'.left ≫ β = h ≫ p.left) (κ : Fin 4) :
    D'.Oφ p' x' κ ≫ β = h ≫ D.Oφ p x κ := by
  have hb : h ≫ T.hom = T'.hom ≫ spMap φ := by
    rw [← Over.w p, ← Category.assoc, ← hp, Category.assoc, pb.1.w, ← Category.assoc, Over.w]
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h hb
  have e : pushPt pb.1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have c : pushPt pb.1.w (toUnit T' ≫ D'.c x') = toUnit _ ≫ D.c x := Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c x').left) ≫ β = (T'.hom ≫ spMap φ) ≫ (D.c x).left
    rw [Category.assoc, hc, ← Category.assoc])
  refine Eq.trans ?_ (WeightPf.Oφ_comp U p x κ).symm
  rw [← e]
  fin_cases κ
  · exact congrArg (fun q => q.left) ((map_mul (pushHom pb T') p' (toUnit T' ≫ D'.c x')).trans
      (congrArg (pushPt pb.1.w p' * ·) c))
  · exact congrArg (fun q => q.left) c
  · rfl
  · exact congrArg (fun q => q.left) (map_one (pushHom pb T'))
end GlobalTheory.LN.Cmp
