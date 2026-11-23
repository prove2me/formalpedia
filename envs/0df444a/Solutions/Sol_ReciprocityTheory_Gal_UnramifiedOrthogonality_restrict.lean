-- Prove2me | solution 1 for ReciprocityTheory.Gal.UnramifiedOrthogonality.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:30.485489+00:00
-- url     : https://prove2.me/submissions/4be7c7da-9572-4b37-a7ff-7a8cc69442d0

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Theorems.Thm_ReciprocityTheory_Gal_LocalFinitenessAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDualityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonalityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerCharAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFiniteness_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDuality_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
namespace ReciprocityTheory.Gal
namespace UnramifiedOrthogonality
theorem _root_.solution (h : UnramifiedOrthogonality) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : UnramifiedOrthogonalityResAt rho A v :=
  (h F Ω l r M A _ v).restrict
end UnramifiedOrthogonality
end ReciprocityTheory.Gal
