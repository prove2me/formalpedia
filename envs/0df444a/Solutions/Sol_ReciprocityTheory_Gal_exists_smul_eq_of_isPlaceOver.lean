-- Prove2me | solution 1 for ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:05.703512+00:00
-- url     : https://prove2.me/submissions/234a6bf1-e2f5-4942-8cbc-46deccc238a4

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_over


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
namespace ReciprocityTheory.Gal
theorem _root_.solution [IsAlgClosure F Ω] {A A' : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (h' : IsPlaceOver A' v) :
    ∃ σ : G F Ω, σ • A = A' := by
  exact exists_smul_eq_of_over h h'
end ReciprocityTheory.Gal
