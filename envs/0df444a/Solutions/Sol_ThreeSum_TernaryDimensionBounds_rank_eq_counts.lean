-- Prove2me | solution 1 for ThreeSum.TernaryDimensionBounds.rank_eq_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:19:03.961858+00:00
-- url     : https://prove2.me/submissions/83f4a884-ddb3-415a-a08b-eaf139206c28

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters
namespace ThreeSum.TernaryDimensionBounds
theorem _root_.solution {N : ℕ} (Q : TritWord N) :
    rank Q = digitCount Q 1+2*digitCount Q 2 := by
  have hlocal (i : Fin N) : (Q i).val = (if Q i=1 then 1 else 0)+
      2*(if Q i=2 then 1 else 0 : ℕ) := by generalize Q i=d; fin_cases d <;> decide
  simp_rw [rank, hlocal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl
end ThreeSum.TernaryDimensionBounds
