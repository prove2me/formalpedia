-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_linComb_3786ccc23e18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:40.526745+00:00
-- url     : https://prove2.me/submissions/b4f488f9-5a6d-4308-99a4-3d18a06892d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution (hv : ValLaws) {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (x : Sp ℂ ⟶ Y) (j j' : K → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j') :
    valAt' x (LB.wchart L φ j) (c.s j).val =
      (∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' x (LB.wchart L φ j') (c.s j').val := by
  have hV : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := top_le_inf x hj hj'
  obtain ⟨e, he⟩ := (hv Y x).2.1 _ hV
  have h3 := (hv Y x).2.2.1
  have h4 := (hv Y x).2.2.2.1
  have hcj := congrArg
    (fun w => ((Units.map (e : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j') →* ℂ) w : ℂˣ) : ℂ)) (hc j j')
  unfold LB.LinComb at hcj
  dsimp only at hcj
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod,
    Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe] at hcj
  simp only [← he] at hcj
  unfold res pullU at hcj
  simp only [Units.coe_map, MonoidHom.coe_coe] at hcj
  simp only [h3 _ _ _ _ hV] at hcj
  rw [hcj]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  exact (h3 _ _ _ _ hV).trans (h4 X (φ i) (L.U (j i) ⊓ L.U (j' i)) (L.g (j i) (j' i)).val)
end GlobalTheory.ThetaGroupFrame
