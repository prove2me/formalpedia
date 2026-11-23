-- Prove2me | solution 1 for ReciprocityTheory.Gal.cyc_eq_map_cycZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:07.284797+00:00
-- url     : https://prove2.me/submissions/28453f2e-db41-4c51-b219-57e7cab7e8af

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
variable (F Ω)
namespace ReciprocityTheory.Gal
theorem _root_.solution (l : ℕ) [Fact l.Prime] (σ : G F Ω) :
    cyc F Ω l σ = Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      (cycZ F Ω l σ) := rfl
end ReciprocityTheory.Gal
