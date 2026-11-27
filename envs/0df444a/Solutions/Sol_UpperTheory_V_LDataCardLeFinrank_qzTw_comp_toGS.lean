-- Prove2me | solution 1 for UpperTheory.V.LDataCardLeFinrank.qzTw_comp_toGS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:11.594301+00:00
-- url     : https://prove2.me/submissions/bab2fee1-d8ae-4a5c-981f-ac04c5350eb1

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open UpperTheory UpperTheory.V UpperTheory.V.LDataCardLeFinrank
variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
variable {F l}
namespace UpperTheory.V.LDataCardLeFinrank
theorem _root_.solution (D : LData F Ω l) (e : ℤ) : (qzTw D e).comp (toGS Ω _) = qzG F Ω l e := by
  ext g x
  simp [qzG, qzTw, scalRep, ← D.hchi]
end UpperTheory.V.LDataCardLeFinrank
