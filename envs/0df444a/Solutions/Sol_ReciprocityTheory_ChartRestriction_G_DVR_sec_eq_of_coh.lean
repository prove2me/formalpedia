-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sec_eq_of_coh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:30.114497+00:00
-- url     : https://prove2.me/submissions/a81bc4dd-f8c9-4279-a821-04d83b728690

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_le_iSup_piece
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_compat_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_ext_cover


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s t : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, LB.Coh L φ j → s.f j = t.f j) : ∀ j, s.f j = t.f j := by
  intro (j : K → L.ι)
  apply sec_ext_cover (LB.wchart L φ j) (fun ρ => LB.wchart L φ j ⊓ piece L φ φ ρ) (fun _ => inf_le_left)
    (le_iSup_piece L φ φ hL _)
  intro ρ
  have hV : LB.wchart L φ j ⊓ piece L φ φ ρ ≤ LB.wchart L φ j ⊓ LB.wchart L φ (ρ ∘ φ) :=
    fun _ hy => ⟨hy.1, hy.2.1⟩
  have hc : LB.Coh L φ (ρ ∘ φ) := fun k₁ k₂ e => by simp only [Function.comp, e]
  have es := sec_compat_rs s j (ρ ∘ φ) hV
  have et := sec_compat_rs t j (ρ ∘ φ) hV
  erw [es, et, h _ hc]
end ReciprocityTheory.ChartRestriction.G.DVR
