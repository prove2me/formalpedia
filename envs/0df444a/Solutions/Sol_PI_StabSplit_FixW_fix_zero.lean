-- Prove2me | solution 1 for PI.StabSplit.FixW.fix_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:50.434312+00:00
-- url     : https://prove2.me/submissions/e35b7524-615d-42a9-9009-ef8665e4cc47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_herm_entry
import Theorems.Thm_PI_StabSplit_FixW_fix_col
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig


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
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (i j : Fin (2 * r + k + 1)) (hi : r + k < i.val) (hj2 : j.val ≤ r + k) : g i j = 0 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  set a := sig k r i with ha
  have har : a.val < r := by rw [ha, sig_hi k r i hi]; have := i.isLt; omega
  have e := congrFun (congrFun hU a) j
  rw [herm_entry, Finset.sum_eq_single a] at e
  · rw [fix_col hg a har a, if_pos rfl, ha, sig_sig] at e
    have hs : sgn k r (sig k r i) = 1 := by
      unfold sgn; rw [if_neg]; rw [sig_hi k r i hi]; have := i.isLt; omega
    rw [hs, star_one, one_mul, one_mul, Hpk_eq, if_neg] at e
    · exact e
    · rw [← ha, sig_sig]; intro h; subst h; omega
  · intro p _ hp
    rw [fix_col hg a har p, if_neg hp, star_zero, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.StabSplit.FixW
