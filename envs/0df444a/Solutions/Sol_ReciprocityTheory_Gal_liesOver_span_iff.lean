-- Prove2me | solution 1 for ReciprocityTheory.Gal.liesOver_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:23.711734+00:00
-- url     : https://prove2.me/submissions/91da0368-340e-4218-bffd-58f2e36019c3

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
import Theorems.Thm_ReciprocityTheory_Gal_isMaximal_span_prime

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
variable {F : Type*} [Field F] [NumberField F]
namespace ReciprocityTheory.Gal
theorem _root_.solution (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 F)) [P.IsPrime] :
    P.LiesOver (Ideal.span {(l : ℤ)}) ↔ ((l : ℕ) : 𝓞 F) ∈ P := by
  constructor
  · intro h
    have hmem : ((l : ℤ)) ∈ P.under ℤ := by
      rw [← h.over]
      exact Ideal.mem_span_singleton_self _
    have h2 : algebraMap ℤ (𝓞 F) (l : ℤ) ∈ P := hmem
    simpa using h2
  · intro h
    refine ⟨?_⟩
    refine (isMaximal_span_prime l).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) (l : ℤ) ∈ P
    simpa using h
end ReciprocityTheory.Gal
