-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.corr_of_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:09.193007+00:00
-- url     : https://prove2.me/submissions/518c2ffe-1b62-4414-b595-a3e922e3e78a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of

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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' hj hj' hjj'
  apply Units.ext
  apply fn_ext
  intro y hy
  have hyl : y ∈ LB.wchart L φ j := hy.1
  have hyr : y ∈ LB.wchart L φ' j' := hy.2
  have hc : ∀ a b, Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) a =
      Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) b → Sum.elim j j' a = Sum.elim j j' b := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.id_comp] at hab ⊢
    · exact hj a b hab
    · exact hjj' a b hab
    · exact (hjj' b a hab.symm).symm
    · exact hj' a b hab
  have hjv : ∀ k, Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) k y ∈ L.U (Sum.elim j j' k) := by
    rintro (k | k)
    · exact Set.mem_iInter.1 hyl k
    · exact Set.mem_iInter.1 hyr k
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k)) (Sum.elim j j') hc hjv
  have e := h y J hJ
  rw [val_of t (𝟙 Y) y J j (fun k => hJj (Sum.inl k)), val_of t' (𝟙 Y) y J j' (fun k => hJj (Sum.inr k))] at e
  exact ((gs_res (𝟙 Y) y inf_le_left hy (t.s j).val).trans (gs_unit (𝟙 Y) y _ hyl _)).trans
    ((congrArg Units.val e).trans ((gs_res (𝟙 Y) y inf_le_right hy (t'.s j').val).trans
      (gs_unit (𝟙 Y) y _ hyr _)).symm)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
