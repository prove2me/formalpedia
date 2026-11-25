-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Gamma_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:21.917155+00:00
-- url     : https://prove2.me/submissions/a4e228cf-55d3-4e4e-b23a-3695272d640b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_cr_iso_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_isIso_appTop_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution : Function.Bijective (torus2Gamma K X).hom := by
  have h1 := isIso_appTop_bij (torus2Iso K X)
  have h2 := cr_iso_bij (Scheme.ΓSpecIso
    (CommRingCat.of (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)))
  first
  | exact h2.comp h1
  | (simp only [torus2Gamma, CommRingCat.hom_comp, RingHom.coe_comp]; exact h2.comp h1)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
