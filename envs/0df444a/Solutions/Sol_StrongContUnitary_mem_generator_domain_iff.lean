-- Prove2me | solution 1 for StrongContUnitary.mem_generator_domain_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:02.825725+00:00
-- url     : https://prove2.me/submissions/529429ed-ca14-46e6-bd96-a0af3101790f

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Spectral_Stone_Generator

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open StrongContUnitary
namespace StrongContUnitary
theorem _root_.solution (U : StrongContUnitary E) (x : E) :
    x ∈ U.generator.domain ↔
      ∃ y, Filter.Tendsto
        (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
        (nhdsWithin 0 {0}ᶜ) (nhds y) :=
  Iff.rfl
end StrongContUnitary
