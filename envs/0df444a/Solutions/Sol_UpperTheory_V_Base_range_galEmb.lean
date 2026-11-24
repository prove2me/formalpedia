-- Prove2me | solution 1 for UpperTheory.V.Base.range_galEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:41:00.441676+00:00
-- url     : https://prove2.me/submissions/632aae0d-2c55-47da-b37d-49fb72bbe13c

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
variable [Algebra k E] [IsScalarTower k E Ω]
namespace UpperTheory.V.Base
theorem _root_.solution : (galEmb k E Ω).range = galOf k E Ω := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    exact galEmb_mem k E Ω τ
  · intro h
    refine ⟨{ σ.toRingEquiv with commutes' := fun x => (mem_galOf k E Ω).1 h x }, ?_⟩
    ext y
    rfl
end UpperTheory.V.Base
