-- Prove2me | solution 1 for UpperTheory.HF.log_rd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:13.340264+00:00
-- url     : https://prove2.me/submissions/910f94b9-0051-4f15-bfa5-16c833b29644

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l ∧ Real.log H.rd = ∑ l ∈ H.condN.primeFactors, H.vdH l * Real.log l ∧ H.ram ⊆ H.condN.primeFactors ∧ 0 < H.rd := by
  intro φ H
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have h1 : Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l := by
    unfold HostRaw.rd HostRaw.ram HostRaw.vdH
    rw [Real.log_rpow hpos, habs, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
    ring
  have h3 : H.ram ⊆ H.condN.primeFactors := by
    intro l hl
    have h := Nat.mem_primeFactors.1 hl
    exact Nat.mem_primeFactors.2 ⟨h.1, H.der.discr_primes.1 l h.1 (Int.natCast_dvd.2 h.2.1), H.condN_ne_zero⟩
  refine ⟨h1, ?_, h3, Real.rpow_pos_of_pos hpos _⟩
  rw [h1]
  refine Finset.sum_subset h3 fun l hl hn => ?_
  have hp := Nat.prime_of_mem_primeFactors hl
  have : ¬ l ∣ (discr H.E).natAbs := fun h => hn (Nat.mem_primeFactors.2 ⟨hp, h, hd'⟩)
  unfold HostRaw.vdH
  rw [padicValNat.eq_zero_of_not_dvd this]
  simp
end UpperTheory.HF
