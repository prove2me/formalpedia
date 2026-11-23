-- Prove2me | solution 1 for UpperTheory.V.Base.mem_galOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:07.578798+00:00
-- url     : https://prove2.me/submissions/29d03146-204d-48d2-be0d-896bb443ab3b

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam

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
variable (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω]
namespace UpperTheory.V.Base
theorem _root_.solution {σ : G k Ω} : σ ∈ galOf k E Ω ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x := Iff.rfl
end UpperTheory.V.Base
