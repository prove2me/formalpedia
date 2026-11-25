-- Prove2me | solution 1 for ReciprocityTheory.CA.length_le_of_isRegular_of_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:42.66472+00:00
-- url     : https://prove2.me/submissions/e66b8e9c-ab39-4c94-b02c-617fbc45f519

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactRest_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Theorems.Thm_ReciprocityTheory_CA_exists_assoc_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution : ∀ (rs : List R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M],
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsRegular M rs → ∀ {p : Ideal R},
    p ∈ associatedPrimes R M → (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
  | [], M, _, _, _, _, _, p, hp => by
    have : p.IsPrime := hp.isPrime
    have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    simpa using ringKrullDim_nonneg_of_nontrivial
  | x :: rs', M, _, _, _, hm, reg, p, hp => by
    obtain ⟨hreg, hreg'⟩ := (isRegular_cons_iff M x rs').mp reg
    have hx : x ∈ maximalIdeal R := hm x List.mem_cons_self
    obtain ⟨q, hq, hpq, hxq, hxnp⟩ := exists_assoc_step hp hx hreg
    have ih := solution rs'
      (fun r hr => hm r (List.mem_cons_of_mem _ hr)) hreg' hq
    have hpp : p.IsPrime := hp.isPrime
    have hxp : Ideal.Quotient.mk p x ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact hxnp
    have hdim : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) :=
      ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
        (Ideal.Quotient.factor_surjective hpq.le) (mem_nonZeroDivisors_of_ne_zero hxp)
        (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq)
    calc ((x :: rs').length : WithBot ℕ∞) = (rs'.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ p) := hdim
end ReciprocityTheory.CA
