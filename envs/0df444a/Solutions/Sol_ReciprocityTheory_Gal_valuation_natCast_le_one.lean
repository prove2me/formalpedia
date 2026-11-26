-- Prove2me | solution 1 for ReciprocityTheory.Gal.valuation_natCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:15.243724+00:00
-- url     : https://prove2.me/submissions/19c8aba4-04d5-4589-b580-787ac150754f

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
theorem _root_.solution (A : ValuationSubring (Ω)) (n : ℕ) :
    A.valuation (n : Ω) ≤ 1 := by
  first
    | (exact (A.valuation_le_one_iff _).2 (natCast_mem A n))
    | (exact (ValuationSubring.valuation_le_one_iff A _).2 (natCast_mem A n))

