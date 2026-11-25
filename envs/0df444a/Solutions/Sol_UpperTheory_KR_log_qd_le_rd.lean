-- Prove2me | solution 1 for UpperTheory.KR.log_qd_le_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:17.717912+00:00
-- url     : https://prove2.me/submissions/5c034826-27f3-4b32-9349-ebb00cc747bc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds2
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTwo
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_LogQdLeRd
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_Rd_q_ne_d
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_d_notMem_small
import Theorems.Thm_Formalism_HC_HostRaw_q_ne_d
import Theorems.Thm_Formalism_HC_HostRaw_q_notMem_small
import Theorems.Thm_Formalism_HC_HostRaw_two_mem_small
import Theorems.Thm_Formalism_HC_HostRaw_vdH_nonneg
import Theorems.Thm_UpperTheory_HF_inert_q
import Theorems.Thm_UpperTheory_HF_log_rd_sum
import Theorems.Thm_UpperTheory_HF_mem_ram
import Theorems.Thm_UpperTheory_HF_ram_eq
import Theorems.Thm_UpperTheory_HF_vd_two
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory.HF
open NumberField Formalism.HC
namespace UpperTheory.KR
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), H.toHostRaw.PsQ → H.q ∈ H.ram ∧ Real.log H.q + Real.log H.d ≤ 2 * Real.log H.rd ∧ Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd ∧ 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
  intro φ H hP
  have hq : H.q ∈ H.ram := (UpperTheory.HF.inert_q H).2.2.2.2 hP
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hd : H.d ∈ H.ram := (hA _).2 (Or.inr (Or.inr rfl))
  have h2 : 2 ∈ H.ram := (Finset.mem_inter.1 hB).2
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have vq : 1 / 2 ≤ H.vdH H.q := (UpperTheory.HF.mem_ram H H.q_prime).2.2.2.1 hq
  have vd : 1 / 2 ≤ H.vdH H.d := (UpperTheory.HF.mem_ram H H.d_prime).2.2.2.1 hd
  have v2 : 11 / 4 ≤ H.vdH 2 := (UpperTheory.HF.vd_two H).2.1
  have n2q : 2 ≠ H.q := fun h => H.q_notMem_small (h ▸ H.two_mem_small)
  have n2d : 2 ≠ H.d := fun h => H.d_notMem_small (h ▸ H.two_mem_small)
  have nqd : H.q ≠ H.d := H.q_ne_d
  have hsub : ({2, H.q, H.d} : Finset ℕ) ⊆ H.ram := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l : ℕ => H.vdH l * Real.log l) hsub
    (fun l _ _ => mul_nonneg (H.vdH_nonneg l) (Real.log_natCast_nonneg l))
  rw [← hs, Finset.sum_insert (by simp [n2q, n2d]), Finset.sum_pair nqd] at hle
  have lq := Real.log_natCast_nonneg H.q
  have ld := Real.log_natCast_nonneg H.d
  have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq0 : (0 : ℝ) < H.q := Nat.cast_pos.2 H.q_prime.pos
  have hd0 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  push_cast at hle
  have key : Real.log 2 + (Real.log H.q + Real.log H.d) / 2 ≤ Real.log H.rd := by
    nlinarith [mul_le_mul_of_nonneg_right vq lq, mul_le_mul_of_nonneg_right vd ld,
      mul_le_mul_of_nonneg_right v2 l2.le]
  have hsq : 0 < Real.sqrt ((H.q : ℝ) * H.d) := Real.sqrt_pos.2 (mul_pos hq0 hd0)
  have h4 : 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
    rw [← Real.log_le_log_iff (by positivity) hrd, Real.log_mul two_ne_zero hsq.ne',
      Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne']
    exact key
  exact ⟨hq, by linarith, by linarith, h4⟩
end UpperTheory.KR
