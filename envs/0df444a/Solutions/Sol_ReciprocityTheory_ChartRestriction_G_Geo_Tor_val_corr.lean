-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:41.658798+00:00
-- url     : https://prove2.me/submissions/c68d441c-8ca6-4e80-a0f4-c21cfab36ead

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (r : Z ⟶ Y) : val t r z J = val t' r z J := by
  have hm : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) ⊓ LB.wchart L φ' (fun k => J (r ≫ φ' k)) :=
    ⟨hJ.mem φ r, hJ.mem φ' r⟩
  have e := h (fun k => J (r ≫ φ k)) (fun k => J (r ≫ φ' k)) (fun a b hab => by simp only [hab])
    (fun a b hab => by simp only [hab]) (fun a b hab => by simp only [hab])
  have e2 := congrArg (gm r z (LB.wchart L φ (fun k => J (r ≫ φ k)) ⊓ LB.wchart L φ' (fun k => J (r ≫ φ' k)))) e
  exact (gm_res r z inf_le_left hm _).symm.trans (e2.trans (gm_res r z inf_le_right hm _))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
