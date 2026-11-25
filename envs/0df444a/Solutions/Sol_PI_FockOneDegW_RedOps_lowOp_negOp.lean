-- Prove2me | solution 1 for PI.FockOneDegW.RedOps.lowOp_negOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:39.641533+00:00
-- url     : https://prove2.me/submissions/cdd55871-b905-4dbb-a6a0-151852b4991e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
import Theorems.Thm_PI_FockOneDegW_RedOps_lowOp_Xd
import Theorems.Thm_PI_FockOneDegW_RedOps_sum_rows
import Theorems.Thm_PI_FockOneDegW_RedOps_not_both
import Theorems.Thm_FockRL_linePos_left
import Theorems.Thm_FockRL_sameBlock_symm
import Theorems.Thm_PI_FockOneDegW_Core_negOp_apply
import Theorems.Thm_PI_FockOneDegW_Core_pd_comm
import Theorems.Thm_PI_FockOneDegW_negOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
namespace PI.FockOneDegW.RedOps
theorem _root_.solution (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (hab : sameBlock a b)
    (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (negOp b a P) =
      negOp b a (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  have hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s) :=
    (FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)
  rw [negOp_apply, negOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) =
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) +
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        (if linePos ((b, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((b, c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((b, d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0))
          else 0)) := by
    intro e
    by_cases h : linePos ((b, e) : Ln p q r s) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases h : linePos ((b, d) : Ln p q r s) = true
    · have hbc : linePos ((b, c) : Ln p q r s) = false := by
        cases h' : linePos ((b, c) : Ln p q r s)
        · rfl
        · exact (not_both c d hcd b h' h).elim
      rw [← hba]
      simp [h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]
    · rw [← hba]
      simp [h]
  · intro e _ hec
    by_cases h1 : linePos ((b, e) : Ln p q r s) = true
    · simp [h1]
    · by_cases h2 : linePos ((b, d) : Ln p q r s) = true
      · have hde : d ≠ e := by
          rintro rfl; exact h1 h2
        simp [h1, h2, hde, Ne.symm hec]
      · simp [h1, h2]
  · simp
end PI.FockOneDegW.RedOps
