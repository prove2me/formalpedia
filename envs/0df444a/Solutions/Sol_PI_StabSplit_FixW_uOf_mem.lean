-- Prove2me | solution 1 for PI.StabSplit.FixW.uOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:32:39.331224+00:00
-- url     : https://prove2.me/submissions/07ed5f7d-e543-4756-ac35-73c293a68a97

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_uOf_out_col
import Theorems.Thm_PI_StabSplit_FixW_uOf_out_row
import Theorems.Thm_PI_StabSplit_FixW_uOf_in
import Theorems.Thm_PI_StabSplit_FixW_herm_entry
import Theorems.Thm_PI_StabSplit_FixW_fix_zero
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_lo
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_mid
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    uOf k r g ∈ UH (Hpk k r) := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  show (uOf k r g)ᴴ * Hpk k r * uOf k r g = Hpk k r
  ext i j
  rw [herm_entry]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [← congrFun (congrFun hU i) j, herm_entry]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_mid k r p hp.1 hp.2, uOf_in g p i hp.1 hp.2 hi.1 hi.2, uOf_in g p j hp.1 hp.2 hj.1 hj.2]
      · rw [uOf_out_row g p i (by omega), if_neg (by intro h; subst h; omega), star_zero, zero_mul,
          zero_mul]
        rcases (show p.val < r ∨ r + k < p.val by omega) with hp' | hp'
        · rw [fix_zero hg (sig k r p) j (by rw [sig_lo k r p hp']; omega) hj.2, mul_zero]
        · rw [fix_zero hg p i hp' hi.2, star_zero, zero_mul, zero_mul]
    · rw [Finset.sum_eq_single (sig k r j)]
      · rw [sig_sig, uOf_out_col g j j (by omega), if_pos rfl, mul_one]
        have hsj : (sig k r j).val < r ∨ r + k < (sig k r j).val := by
          have := j.isLt; rw [sig_val]; split_ifs <;> omega
        rw [uOf_out_row g (sig k r j) i hsj, if_neg (by intro h; rw [← h] at hi; omega), star_zero,
          zero_mul, Hpk_eq, if_neg]
        rw [sig_mid k r i hi.1 hi.2]; intro h; subst h; omega
      · intro p _ hp
        rw [uOf_out_col g _ j (by omega), if_neg (by intro h; apply hp; rw [← h, sig_sig]), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · rw [uOf_out_col g i i (by omega), if_pos rfl, star_one, one_mul]
      have hsi : (sig k r i).val < r ∨ r + k < (sig k r i).val := by
        have := i.isLt; rw [sig_val]; split_ifs <;> omega
      rw [uOf_out_row g (sig k r i) j hsi, Hpk_eq]
      by_cases h : sig k r i = j
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
    · intro p _ hp
      rw [uOf_out_col g p i (by omega), if_neg hp, star_zero, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
end PI.StabSplit.FixW
