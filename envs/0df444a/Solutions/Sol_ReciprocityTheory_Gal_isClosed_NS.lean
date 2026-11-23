-- Prove2me | solution 1 for ReciprocityTheory.Gal.isClosed_NS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:27.730169+00:00
-- url     : https://prove2.me/submissions/6799d6b5-6ce9-4cb0-a265-eb25da8f227b

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable (Ω)
namespace ReciprocityTheory.Gal
theorem _root_.solution : IsClosed (NS Ω S : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _
end ReciprocityTheory.Gal
