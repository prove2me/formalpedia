-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:39.602819+00:00
-- url     : https://prove2.me/submissions/bc8a2f7a-4d3b-4088-80f0-6a3dcbb1252c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_valU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_pullU

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {k : ℤ} (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (i i' : Fin 1 → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U i ⊓ (LPow A L k (Over.mk x0)).U i')) :
    valAt' p _ ((LPow A L k (Over.mk x0)).g i i').val =
      valAt' (p ≫ (snd (Over.mk x0) A).left) (L.U (i 0) ⊓ L.U (i' 0)) (L.g (i 0) (i' 0)).val ^ k := by
  delta LPow LB.LinComb at h ⊢
  dsimp only at h ⊢
  rw [Fin.prod_univ_one, vtf_valU p h]
  congr 1
  exact (vtf_val_res p _ h _).trans (vtf_val_pullU p (snd (Over.mk x0) A).left _ (L.g (i 0) (i' 0)))
end ReciprocityTheory.ChartRestriction.G.PullbackSections
