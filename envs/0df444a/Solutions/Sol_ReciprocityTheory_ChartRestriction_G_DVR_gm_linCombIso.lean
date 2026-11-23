-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gm_linCombIso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:42.867819+00:00
-- url     : https://prove2.me/submissions/b97ca5cc-1a8a-4cf1-8cfe-0b78b9456a37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι)
    (hz : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ jN ⊓ LB.wchart M' φ jM) :
    gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ jN ⊓ LB.wchart M' φ jM) ((LB.linCombIso w φ ε).s (jN, jM)) =
      ∏ a, bw w (r ≫ φ a) z (jN a) (jM a) ^ ε a :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a)
    ((gm_res r z _ hz _).trans (gm_pull r (φ a) z (LB.wchart M pr (jN a) ⊓ M'.U (jM a))
      ⟨Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a⟩ _))))
end ReciprocityTheory.ChartRestriction.G.DVR
