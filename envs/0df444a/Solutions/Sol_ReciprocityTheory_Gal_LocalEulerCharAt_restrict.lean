-- Prove2me | solution 1 for ReciprocityTheory.Gal.LocalEulerCharAt.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:01.886013+00:00
-- url     : https://prove2.me/submissions/3db5e8e0-2dee-49d2-890f-70493616dbc1

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
namespace LocalEulerCharAt
theorem _root_.solution {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : LocalEulerCharAt A (rho.comp (Dec (F := F) A).subtype) v) : LocalEulerCharResAt rho A v :=
  fun hr hA hc => h hr hA (hc.comp' continuous_subtype_val)
end LocalEulerCharAt
end ReciprocityTheory.Gal
