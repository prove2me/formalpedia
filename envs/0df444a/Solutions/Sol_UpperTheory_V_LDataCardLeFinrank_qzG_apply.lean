-- Prove2me | solution 1 for UpperTheory.V.LDataCardLeFinrank.qzG_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:06.997984+00:00
-- url     : https://prove2.me/submissions/f78c8e57-f7de-4d66-9f91-b92e5099c5d2

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec

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
variable {F l}
namespace UpperTheory.V.LDataCardLeFinrank
theorem _root_.solution (e : ℤ) (g : G F Ω) (x : QZ l) :
    qzG F Ω l e g x = ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x := rfl
end UpperTheory.V.LDataCardLeFinrank
