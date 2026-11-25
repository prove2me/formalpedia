-- Prove2me | solution 1 for PI.ScRefExists.ApP.inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:36.166907+00:00
-- url     : https://prove2.me/submissions/c64126a8-2b37-4298-91e4-25e7c362cbf0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
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


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
namespace PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl
end PI.ScRefExists.ApP
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.ApP
theorem _root_.solution {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : ((n : I.E))⁻¹ ∈ Ap I p := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero _)
  have hE : (n : I.E) ≠ 0 := Int.cast_ne_zero.mpr hn0
  have hcop : Nat.Coprime n.natAbs p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact hn (Int.natCast_dvd.mpr h)
  refine (mem_Ap_lemma I p _).mpr ⟨n.natAbs, hcop, ?_⟩
  rcases Int.natAbs_eq n with h | h
  · have h' : (n.natAbs : ℤ) = n := by linarith
    have e : (n.natAbs : I.E) = (n : I.E) := by rw [← Int.cast_natCast, h']
    exact ⟨1, by rw [e, mul_inv_cancel₀ hE]; simp⟩
  · have h' : (n.natAbs : ℤ) = -n := by linarith
    have e : (n.natAbs : I.E) = -(n : I.E) := by rw [← Int.cast_natCast, h', Int.cast_neg]
    exact ⟨-1, by rw [e, neg_mul, mul_inv_cancel₀ hE]; simp⟩
end PI.ScRefExists.ApP
