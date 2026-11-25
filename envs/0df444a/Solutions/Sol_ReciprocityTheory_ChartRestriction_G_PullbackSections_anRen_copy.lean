-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anRen_copy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:31.494639+00:00
-- url     : https://prove2.me/submissions/4fc200c8-56d7-4310-aeb3-6528abe76fd6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anJetMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_anPr

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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) (i : Fin 2) (a : Jet ℂ (Fin 1 × Fin g) m) :
    anRen m (jetMap (anLin (anPr i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold anRen jetCopy
  exact anJetMap_comp _ _ _ _ _ _ (fun p => by simp only [anLin_anPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a
end ReciprocityTheory.ChartRestriction.G.PullbackSections
