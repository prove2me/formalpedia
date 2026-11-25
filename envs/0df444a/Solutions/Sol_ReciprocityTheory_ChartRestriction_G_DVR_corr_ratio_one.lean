-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_ratio_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:02.407452+00:00
-- url     : https://prove2.me/submissions/557071e5-4874-4c76-a269-faff872e5110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_mul_inv_one

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
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') :
    LB.Gen.Corr L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t'))
      (LB.oneGen L) := by
  intro j j' hc _ _
  have e := h (j ∘ Sum.inl) (j ∘ Sum.inr) (fun a b e => hc (Sum.inl a) (Sum.inl b) e)
    (fun a b e => hc (Sum.inr a) (Sum.inr b) e) fun k k' e => hc (Sum.inl k) (Sum.inr k') e
  exact (shape_mul_inv_one _ _ _ _ _ e).trans (map_one _).symm
end ReciprocityTheory.ChartRestriction.G.DVR
