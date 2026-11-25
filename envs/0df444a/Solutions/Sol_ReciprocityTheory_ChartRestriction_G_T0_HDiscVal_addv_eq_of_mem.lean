-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.addv_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:43:56.442801+00:00
-- url     : https://prove2.me/submissions/1de53961-4d69-4316-9bbb-d2beb70d28ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_bij


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
open IsDedekindDomain WithZero ValPl
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
variable (O F)
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
theorem _root_.solution {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L) :
    ∃ v : HeightOneSpectrum (integralClosure O L), w = addv L v := by
  obtain ⟨e, he⟩ := placesOver_bij O F L
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  rw [← he, Equiv.apply_symm_apply]
end ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
