-- Prove2me | solution 1 for ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:40.328896+00:00
-- url     : https://prove2.me/submissions/70bac7bd-97f7-42ce-938b-c1a36a352f13

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  first
  | exact Valued.isOpen_valuationSubring _
  | exact Valued.isOpen_integer _
end ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
