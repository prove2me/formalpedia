-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.val_famMult
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:34.822524+00:00
-- url     : https://prove2.me/submissions/268236ef-6370-4bec-99d6-d34578d32ff1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {D F}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (mu α : D.X) :
    val (DegPre.famMult D F k mu α) σ.left z J = val (D.tau mu α) (σ.left ≫ jFK (R := R) F) z J *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (σ.left ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (σ.left ≫ jFK (R := R) F) z J) :=
  (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl).trans (by ac_rfl)))
end ReciprocityTheory.ChartRestriction.G.DVR
