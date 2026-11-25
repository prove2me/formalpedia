-- Prove2me | solution 1 for P2M_GlobalTheory_TauValues_bimult_iff__8bce6d321190
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:29.79968+00:00
-- url     : https://prove2.me/submissions/ece5a3c1-385b-4cdb-a7c5-d06208b3bc34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CorrOfValFieldExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionField
import Theorems.Thm_GlobalTheory_TauValues_bimult_iff
import Theorems.Thm_GlobalTheory_corr_of_val_flat_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


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
open GlobalTheory GlobalTheory.TauValues
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.TauValues
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ a b m : D.X,
      val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J) ↔
    D.TauBimult :=
  ⟨fun h a b m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (bimult_iff D κ hJ a b m).1 (h z J hJ a b m),
    fun h _ _ hJ a b m => (bimult_iff D κ hJ a b m).2 (val_corr hJ (h a b m) κ.left)⟩
end GlobalTheory.TauValues
