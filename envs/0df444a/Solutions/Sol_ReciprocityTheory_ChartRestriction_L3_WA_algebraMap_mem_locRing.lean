-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.algebraMap_mem_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:31.134146+00:00
-- url     : https://prove2.me/submissions/d730ca42-146a-400e-a707-e9a3f040adfe

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    algebraMap (𝓞 K) K r ∈ locRing p := by
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR]
  refine ⟨1, one_mem _, ?_⟩
  rw [map_one, one_mul]
  exact Submodule.mem_one.2 ⟨r, rfl⟩
end ReciprocityTheory.ChartRestriction.L3.WA
