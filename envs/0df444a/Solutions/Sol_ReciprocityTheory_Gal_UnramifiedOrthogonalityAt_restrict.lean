-- Prove2me | solution 1 for ReciprocityTheory.Gal.UnramifiedOrthogonalityAt.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:02.683811+00:00
-- url     : https://prove2.me/submissions/32aca0ab-efa8-4527-b8f0-d094b012998f

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd


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
namespace UnramifiedOrthogonalityAt
theorem _root_.solution {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : UnramifiedOrthogonalityAt A (rho.comp (Dec (F := F) A).subtype) v) :
    UnramifiedOrthogonalityResAt rho A v :=
  fun hr hA hl hI hc => h hr hA hl (fun σ hσ => hI σ hσ) (hc.comp' continuous_subtype_val)
end UnramifiedOrthogonalityAt
end ReciprocityTheory.Gal
