-- Prove2me | solution 1 for UpperTheory.V.Base.cycU_le_levU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:51.306046+00:00
-- url     : https://prove2.me/submissions/d99d05f9-8c13-4800-a6e4-7c2ea7feb471

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology TensorProduct
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
namespace UpperTheory.V.Base
theorem _root_.solution (U : Subgroup (G k Ω)) (n : ℕ) : cycU l U ≤ levU l U n := by
  intro σ hσ
  simp only [cycU, levU, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker] at hσ ⊢
  exact ⟨hσ.1, by rw [hσ.2]; exact Subgroup.one_mem _⟩
end UpperTheory.V.Base
