-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_isIndefiniteRamifiedExactlyAt_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fae27fe3-12ba-5a1d-9218-948b806c68ef

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isIndefiniteRamifiedExactlyAt_of_squarefree
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

open IsDedekindDomain NumberField in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) :
    ∃ R : Submodule ℤ ℍ[ℚ, a, b], R ≤ Λ ∧ IsEichlerOrder R N := by
  classical

  have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → q ∉ s → q' ∉ s →
      ∃ R : Submodule ℤ ℍ[ℚ, a, b], R ≤ Λ ∧ IsEichlerOrder R (∏ p ∈ s, p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ _ _
      refine ⟨Λ, le_rfl, Λ, Λ, hΛ, hΛ, (inf_idem Λ).symm, ?_⟩
      rw [Finset.prod_empty]
      exact AddSubgroup.relIndex_self _
    | insert p s hps ih =>
      intro hprime hq hq'
      obtain ⟨R, hRΛ, hR⟩ := ih (fun r hr => hprime r (Finset.mem_insert_of_mem hr))
        (fun h => hq (Finset.mem_insert_of_mem h)) (fun h => hq' (Finset.mem_insert_of_mem h))
      have hp : p.Prime := hprime p (Finset.mem_insert_self p s)
      have hpq : p ≠ q := fun h => hq (h ▸ Finset.mem_insert_self p s)
      have hpq' : p ≠ q' := fun h => hq' (h ▸ Finset.mem_insert_self p s)
      have hpN : ¬ p ∣ ∏ r ∈ s, r := by
        intro hdvd
        obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp hdvd
        have : p = r := (Nat.prime_dvd_prime_iff_eq hp (hprime r (Finset.mem_insert_of_mem hr))).mp hpr
        exact hps (this ▸ hr)
      obtain ⟨n, hn⟩ :=
        QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
          hqq' hB hR p hp hpq hpq' hpN
      refine ⟨CerednikDrinfeld.meetOrder R n, inf_le_left.trans hRΛ, ?_⟩
      rw [Finset.prod_insert hps, mul_comm]
      exact hn
  obtain ⟨R, hRΛ, hR⟩ := key N.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun h => hqN (Nat.dvd_of_mem_primeFactors h)) (fun h => hq'N (Nat.dvd_of_mem_primeFactors h))
  rw [Nat.prod_primeFactors_of_squarefree hN] at hR
  exact ⟨R, hRΛ, hR⟩

end S_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isIndefiniteRamifiedExactlyAt_of_squarefree
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isIndefiniteRamifiedExactlyAt_of_squarefree (solution)
