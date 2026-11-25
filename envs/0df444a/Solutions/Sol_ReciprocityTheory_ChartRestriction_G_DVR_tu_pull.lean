-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tu_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:37.433395+00:00
-- url     : https://prove2.me/submissions/a72265c8-f229-4b48-bfb4-a10ac2c7bc6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tu_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (u : ∀ p, Γ(X, U p)ˣ)
variable {U u}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (h : Z ⟶ Y) {W : Y.Opens} {V : Z.Opens} (hV : V ≤ h ⁻¹ᵁ W) {ψ : Y ⟶ X} {p : ι}
    (hW : W ≤ ψ ⁻¹ᵁ U p) :
    res hV (pullU h W (tu U u W ψ p)) = tu U u V (h ≫ ψ) p := by
  have hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U p := fun x hx => hW (hV hx)
  rw [tu_def hW, tu_def hV', pullU_res_eq_res_map_homOfLE, res_res_eq_res_trans']
  first
    | rfl
    | (ext1; rfl)
    | (ext1; simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, Scheme.comp_app]; rfl)
end ReciprocityTheory.ChartRestriction.G.DVR
