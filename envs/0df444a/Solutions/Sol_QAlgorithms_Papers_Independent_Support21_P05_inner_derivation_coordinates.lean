-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P05.inner_derivation_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:16:14.104905+00:00
-- url     : https://prove2.me/submissions/cdb5c638-1b42-4b17-b183-0afde7f6ad9e

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P05
open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

set_option maxHeartbeats 4000000 in
theorem g66c_inner (c d z : Octonions) :
    octonionAction (innerCoordinates c d) z = octonionInner c d z := by
  obtain ⟨c1, c2, cp, cm⟩ := c
  obtain ⟨d1, d2, dp, dm⟩ := d
  obtain ⟨z1, z2, zp, zm⟩ := z
  simp only [octonionAction, innerCoordinates, octonionInner, octonionMul, outer3,
    dotProduct, Fin.sum_univ_three, cross_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp; ring
  · simp; ring
  · funext i; fin_cases i <;> simp [Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply, outer3] <;> ring
  · funext i; fin_cases i <;> simp [Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply, outer3] <;> ring

theorem solution :
    (∀ c d : Octonions, Matrix.trace (innerCoordinates c d).1 = 0 ∧
      ∀ z, octonionAction (innerCoordinates c d) z = octonionInner c d z) ∧
    (∀ i j : Fin 3, innerCoordinates (epsilonMinus j) (epsilonPlus i) =
      (matrixUnit i j - (if i = j then (1 / 3 : ℂ) • (1 : Mat3 ℂ) else 0), 0, 0)) := by
  refine ⟨fun c d => ⟨?_, g66c_inner c d⟩, ?_⟩
  · simp [innerCoordinates, Matrix.trace, Fin.sum_univ_three, outer3, dotProduct]
    ring
  · intro i j
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext r s
      fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
        simp [innerCoordinates, epsilonMinus, epsilonPlus, outer3, vectorUnit, matrixUnit,
          dotProduct, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] <;> ring
    · funext r
      fin_cases r <;> simp [innerCoordinates, epsilonMinus, epsilonPlus, cross_apply]
    · funext r
      fin_cases r <;> simp [innerCoordinates, epsilonMinus, epsilonPlus, cross_apply]

end
