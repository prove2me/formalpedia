-- Prove2me | solution 1 for ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.algebraMap_int_mem_Oint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:27.168903+00:00
-- url     : https://prove2.me/submissions/516e1bc2-90a1-49f7-92ef-3d65d8ba162d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeneralLinearIntegers ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
namespace ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
theorem _root_.solution (m : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) ∈ Oint F := by
  intro v
  exact coe_algebraMap_mem (𝓞 F) F v m
end ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
