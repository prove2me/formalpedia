-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_eq_single_of_dvd_8b89a10b6347
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:30.091405+00:00
-- url     : https://prove2.me/submissions/2740a6b7-e3af-49b3-a72f-2ab427074dad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchEvalPowerSumHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchEvalPowerSumHom
theorem _root_.solution {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by
  have hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw
    exact hw
  obtain ⟨j, hj⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hjk : k ≤ (j : ℕ) + 1 := Nat.le_of_dvd (by omega) (hd j hj)
  rw [← Finset.add_sum_erase _ _ hj] at hsum
  have hmul : k ≤ e j * ((j : ℕ) + 1) := le_trans hjk (Nat.le_mul_of_pos_left _ hej)
  have hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0 := by omega
  have hjm : e j * ((j : ℕ) + 1) = k := by omega
  have hej1 : e j = 1 := by nlinarith
  have hjv : j = (⟨k - 1, by omega⟩ : Fin N) := by
    rw [hej1, one_mul] at hjm
    exact Fin.ext (by simp; omega)
  have hother : ∀ i, i ≠ j → e i = 0 := by
    intro i hij
    by_contra hne
    have hi : i ∈ e.support.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) i hi
    rw [Nat.mul_eq_zero] at h0
    omega
  ext i
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ← hjv, hej1]
  · exact hother i (fun hij => h (hjv.symm.trans hij.symm))
end SchEvalPowerSumHom
end GroundTheory.Heights₂.Heights.RestTerms
