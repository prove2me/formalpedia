-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_m1Prime_0200493cebd2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:36.057012+00:00
-- url     : https://prove2.me/submissions/e555b496-b4f8-4b98-896c-9d63191c6295

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_count_primeFrac_of_ne_3fc751f299b5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
    (ι : E →+* L) {j' : ℕ} (hj : 1 ≤ j') {S : Finset ℕ} (h2 : 2 ∈ S) :
    OrderBoundAtPrime (fun _ => ι) j' S (smallBlockTwo ι) := by
  intro τ p hp 𝔓 h
  have hD0 : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (extDifferent ι : FractionalIdeal (𝓞 L)⁰ L) := by
    exact_mod_cast FractionalIdeal.count_coe_nonneg L 𝔓 (extDifferent ι)
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  simp only [smallBlockTwo, inv_one, mul_one]
  rw [FractionalIdeal.count_inv, Int.cast_neg, abs_neg]
  by_cases hp2 : p = 2
  · subst hp2
    rw [if_pos h2]
    have h0 : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (primeFrac L 2) := by
      exact_mod_cast FractionalIdeal.count_coe_nonneg L 𝔓 (Ideal.span {((2 : ℕ) : 𝓞 L)})
    rw [abs_of_nonneg h0]
    norm_num
    nlinarith
  · rw [count_primeFrac_of_ne hp Nat.prime_two hp2 𝔓 h]
    have hpc : (0 : ℝ) ≤ FractionalIdeal.count L 𝔓 (primeFrac L p) := by
      exact_mod_cast FractionalIdeal.count_coe_nonneg L 𝔓 (Ideal.span {(p : 𝓞 L)})
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have := hp.one_lt
      have : (1 : ℝ) < p := by exact_mod_cast this
      linarith
    rw [Int.cast_zero, abs_zero]
    apply add_nonneg _ (mul_nonneg (by positivity) hD0)
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) hpc) hp1
    · exact le_rfl
end GroundTheory.Heights₂.Heights.NineStatements
