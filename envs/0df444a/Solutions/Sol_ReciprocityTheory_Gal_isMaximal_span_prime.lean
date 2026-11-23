-- Prove2me | solution 1 for ReciprocityTheory.Gal.isMaximal_span_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:27.945064+00:00
-- url     : https://prove2.me/submissions/daf16af8-d7d0-4fc8-ac17-9f3135263bf8

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA

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
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {(l : ℤ)}).IsMaximal := by
  first
    | exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
    | exact Ideal.IsPrime.isMaximal
        ((Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2
          (Nat.prime_iff_prime_int.mp hl.out))
        (by simp [hl.out.ne_zero])
end ReciprocityTheory.Gal
