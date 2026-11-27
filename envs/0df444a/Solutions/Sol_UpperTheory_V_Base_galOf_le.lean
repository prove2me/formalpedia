-- Prove2me | solution 1 for UpperTheory.V.Base.galOf_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:40.059071+00:00
-- url     : https://prove2.me/submissions/3ebed5a2-f42d-401f-994c-1f46a9addd7c

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Theorems.Thm_UpperTheory_V_Base_mem_galOf

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
theorem _root_.solution (E' : Type) [Field E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] :
    galOf k E' Ω ≤ galOf k E Ω := by
  intro σ hσ
  rw [mem_galOf] at hσ ⊢
  intro x
  rw [IsScalarTower.algebraMap_apply E E' Ω]
  exact hσ _
end UpperTheory.V.Base
