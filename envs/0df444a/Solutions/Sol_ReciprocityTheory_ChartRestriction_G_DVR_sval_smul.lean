-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sval_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:26.97241+00:00
-- url     : https://prove2.me/submissions/f283e7cd-662e-4a4b-a576-1847d1a54d63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf

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
variable (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
  (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
include hG hw
omit hG hw
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (ζ : F) (s : Fam D F k) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval ((ζ • s).s α) r z J =
      gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) * sval (s.s α) r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) ((gs_res r z le_top (hJ.mem _ r) _).trans
    (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl)
end ReciprocityTheory.ChartRestriction.G.DVR
