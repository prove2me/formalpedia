-- Prove2me | solution 1 for ReciprocityTheory.Coh.shp_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:07.615031+00:00
-- url     : https://prove2.me/submissions/c273d062-e6ef-4cf3-8c28-1d174d786e98

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {A B : Cx R}
namespace ReciprocityTheory.Coh
theorem _root_.solution {φ ψ : Hom A B} (h : ∀ n, φ.f n = ψ.f n) : φ = ψ := by
  cases φ
  cases ψ
  congr 1
  funext n
  exact h n
end ReciprocityTheory.Coh
