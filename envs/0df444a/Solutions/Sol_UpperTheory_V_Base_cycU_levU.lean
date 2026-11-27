-- Prove2me | solution 1 for UpperTheory.V.Base.cycU_levU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:34.7096+00:00
-- url     : https://prove2.me/submissions/4349fa8b-9f84-4731-8dbd-5813fc5adee3

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Theorems.Thm_UpperTheory_V_Base_levU_le
import Theorems.Thm_UpperTheory_V_Base_cycU_le_levU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology TensorProduct
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
namespace UpperTheory.V.Base
theorem _root_.solution (U : Subgroup (G k Ω)) (n : ℕ) : cycU l (levU l U n) = cycU l U :=
  le_antisymm (inf_le_inf_right _ (levU_le l U n)) (le_inf (cycU_le_levU l U n) inf_le_right)
end UpperTheory.V.Base
