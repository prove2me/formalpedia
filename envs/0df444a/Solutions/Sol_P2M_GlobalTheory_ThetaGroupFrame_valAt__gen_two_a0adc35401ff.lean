-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_two_a0adc35401ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:05.380825+00:00
-- url     : https://prove2.me/submissions/2f7472b2-b32f-46a8-8915-0d56e57e89df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_linComb_3786ccc23e18
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_wchart_two

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
theorem _root_.solution (hv : ValLaws) {X Y : Scheme.{0}} (L : LB X) (φ₀ φ₁ : Y ⟶ X) (k : ℕ)
    (c : LB.Gen (LB.LinComb L (K := Fin 2) ![φ₀, φ₁] ![(k : ℤ), -(k : ℤ)])) (hc : c.IsGen)
    (x : Sp ℂ ⟶ Y) (y₀ y₁ : Sp ℂ ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁)
    (j j' : Fin 2 → L.ι) (a₀ : ⊤ ≤ y₀ ⁻¹ᵁ L.U (j 0)) (a₁ : ⊤ ≤ y₁ ⁻¹ᵁ L.U (j 1))
    (b₀ : ⊤ ≤ y₀ ⁻¹ᵁ L.U (j' 0)) (b₁ : ⊤ ≤ y₁ ⁻¹ᵁ L.U (j' 1)) :
    valAt' x (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
      valAt' y₀ (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val ^ k *
        (valAt' y₁ (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val ^ k)⁻¹ *
        valAt' x (LB.wchart L ![φ₀, φ₁] j') (c.s j').val := by
  have hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j :=
    (top_le_wchart_two L φ₀ φ₁ j x y₀ y₁ h₀ h₁).2 ⟨a₀, a₁⟩
  have hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j' :=
    (top_le_wchart_two L φ₀ φ₁ j' x y₀ y₁ h₀ h₁).2 ⟨b₀, b₁⟩
  rw [valAt'_gen_linComb hv L ![φ₀, φ₁] ![(k : ℤ), -(k : ℤ)] c hc x j j' hj hj']
  simp [Fin.prod_univ_two, h₀, h₁, _root_.zpow_neg, zpow_natCast]
end GlobalTheory.ThetaGroupFrame
