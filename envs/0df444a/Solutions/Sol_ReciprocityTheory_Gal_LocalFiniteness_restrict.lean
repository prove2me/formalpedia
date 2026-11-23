-- Prove2me | solution 1 for ReciprocityTheory.Gal.LocalFiniteness.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:33.364114+00:00
-- url     : https://prove2.me/submissions/4940575f-b3c9-4600-bd41-eb2d65d7afbf

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Theorems.Thm_ReciprocityTheory_Gal_LocalFinitenessAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDualityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonalityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerCharAt_restrict

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
namespace LocalFiniteness
theorem _root_.solution (h : LocalFiniteness) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : LocalFinitenessResAt rho A v :=
  (h F Ω l r M A _ v).restrict
end LocalFiniteness
end ReciprocityTheory.Gal
