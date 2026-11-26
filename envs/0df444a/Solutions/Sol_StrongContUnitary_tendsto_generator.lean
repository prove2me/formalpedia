-- Prove2me | solution 1 for StrongContUnitary.tendsto_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:11.271868+00:00
-- url     : https://prove2.me/submissions/c4308277-2d03-4a7b-b960-48500d241198

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Spectral_Stone_Generator

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open StrongContUnitary
namespace StrongContUnitary
theorem _root_.solution (U : StrongContUnitary E) (x : U.generator.domain) :
    Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
      (nhdsWithin 0 {0}ᶜ) (nhds (U.generator x)) :=
  generatorLimit_spec U x
end StrongContUnitary
