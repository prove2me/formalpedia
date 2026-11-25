-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_single_955f73d9e620
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:40.88481+00:00
-- url     : https://prove2.me/submissions/abf359cd-9627-422a-b1f2-022df2d01f3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {S : Type} [CommRing S]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (φ : CombC S J d) (I : CombCell ι J d)
    (hJk : J k = ∅) (h1 : (I.1.1 k).card = 1) :
    tD (corr J k i₀ d φ) I.1.1 = φ (repl J k i₀ d I hJk h1) := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
  rw [tD, Finset.sum_eq_single_of_mem (⟨k, i⟩ : Σ k, ι k) (by simp [hi])]
  · have hrem : rem I.1.1 k i = Function.update I.1.1 k ∅ := by rw [rem, hi, Finset.erase_singleton]
    have hins : ins k i₀ (Function.update I.1.1 k ∅) = Function.update I.1.1 k {i₀} := by
      rw [ins, Function.update_self, Function.update_idem, Finset.insert_empty]
    have hk : k ∉ Finset.univ.filter (· < k) := by simp
    have hs : KH.faceSign I.1.1 k i * KH.faceSign (Function.update I.1.1 k {i₀}) k i₀ = 1 := by
      rw [faceSign_eq, faceSign_eq, hi, Function.update_self, sum_card_update_of_notMem _ _ _ _ hk,
        Finset.filter_singleton, Finset.filter_singleton, if_neg (lt_irrefl i), if_neg (lt_irrefl i₀)]
      rw [Finset.card_empty, pow_zero, one_mul, ← mul_pow]
      norm_num
    rw [hrem, corr, if_pos (Function.update_self _ _ _), tH, if_neg (by simp), hins, smul_smul, hs, one_smul, ext,
      dif_pos ⟨(repl J k i₀ d I hJk h1).1.2, (repl J k i₀ d I hJk h1).2⟩]
    rfl
  · rintro ⟨l, j⟩ hp hne
    have hj : j ∈ I.1.1 l := (Finset.mem_sigma.mp hp).2
    rw [corr, if_neg, smul_zero]
    by_cases hl : l = k
    · subst hl
      rw [hi, Finset.mem_singleton] at hj
      subst hj
      exact absurd rfl hne
    · rw [rem, Function.update_of_ne (Ne.symm hl)]
      exact (I.1.2.1 k).ne_empty
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
