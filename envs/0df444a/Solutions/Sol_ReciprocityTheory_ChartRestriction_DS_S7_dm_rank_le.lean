-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:38.5689+00:00
-- url     : https://prove2.me/submissions/59df27e7-1c10-46ba-b233-afa57e626e4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_rank_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_zero_of_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) :
    Y.rank ≤ 2 * q0 ε := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 1 else 0 with hPd
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 0 else 1 with hQd
  have hY : Y = P * Y * Q + Q * Y * P := by
    ext a b
    simp only [hPd, hQd, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;>
      exact dm_zero_of_eq hYp a b (by simp [ha, hb])
  have hP : P.rank = pOf ε := by
    rw [hPd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold pOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have hQ : Q.rank = qOf ε := by
    rw [hQd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold qOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have h1 : (P * Y * Q).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hP.le))
      ((Matrix.rank_mul_le_right _ _).trans hQ.le)
  have h2 : (Q * Y * P).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_right _ _).trans hP.le)
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hQ.le))
  calc Y.rank = (P * Y * Q + Q * Y * P).rank := congrArg Matrix.rank hY
    _ ≤ (P * Y * Q).rank + (Q * Y * P).rank := dm_rank_add _ _
    _ ≤ q0 ε + q0 ε := add_le_add h1 h2
    _ = 2 * q0 ε := by ring
end ReciprocityTheory.ChartRestriction.DS.S7
