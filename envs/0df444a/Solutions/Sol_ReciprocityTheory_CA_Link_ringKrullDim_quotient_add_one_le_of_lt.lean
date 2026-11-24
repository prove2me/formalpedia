-- Prove2me | solution 1 for ReciprocityTheory.CA.Link.ringKrullDim_quotient_add_one_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:12.941284+00:00
-- url     : https://prove2.me/submissions/59e044f4-d933-43ec-a0e6-0bd2e4d3a02e

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_GorIndepStatement
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.Link
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.CA.Link
theorem _root_.solution {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk q r ∈ nonZeroDivisors (R ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrp)
end ReciprocityTheory.CA.Link
