-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.hcompl_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:19.928626+00:00
-- url     : https://prove2.me/submissions/529c0058-8e89-4ef8-b84f-009dc45818ab

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_conjO

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
theorem _root_.solution (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) p = Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h => h _ (algebraMap_conjO s), fun h t ht => ?_⟩
  have e : t = conjO K s := IsFractionRing.injective (𝓞 K) K (ht.trans (algebraMap_conjO s).symm)
  rw [e]
  exact h
end ReciprocityTheory.ChartRestriction.L3.WA
