-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotential_first_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:33.400031+00:00
-- url     : https://prove2.me/submissions/99017841-9e4a-4a90-a374-32280f05e560

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofB
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialPullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_prodAtlas_holoMap_fst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory Filter Topology FinHolAtlas
open scoped ContDiff
noncomputable section
variable {e e' : ℕ}
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : LocPot X)
    (hP : IsPotential A P) : IsPotential (prodAtlas A B) (P.pr1 (Y := Y)) :=
  isPotentialPullback A (prodAtlas A B) Prod.fst (prodAtlas_holoMap_fst A B) P hP
end ReciprocityTheory.AnForm.M
