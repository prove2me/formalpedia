-- Prove2me | solution 1 for UpperTheory.V.LDataCardLeFinrank.ineImage_le_decImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:57.81506+00:00
-- url     : https://prove2.me/submissions/7ea8701e-0ee7-49b2-9886-09a2b350c29f

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Theorems.Thm_ReciprocityTheory_Gal_Ine_le_Dec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open UpperTheory UpperTheory.V UpperTheory.V.LDataCardLeFinrank
variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
namespace UpperTheory.V.LDataCardLeFinrank
theorem _root_.solution (A : ValuationSubring Ω) : ineImage F l A ≤ decImage F l A := Subgroup.map_mono (Ine_le_Dec A)
end UpperTheory.V.LDataCardLeFinrank
