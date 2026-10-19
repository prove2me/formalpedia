-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.pauliErrorComponent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:52:51.927198+00:00
-- url     : https://prove2.me/submissions/1b3ceff9-7edf-4279-a9f4-77af25ed2372

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Papers.Independent.Independent1.P09

theorem solution (weights : Fin 3 → ℝ)
    (nonnegative : ∀ j, 0 ≤ weights j) (total : ∑ j, weights j = 1)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ 1) :
    let sigma : Fin 3 → Matrix Bool Bool ℂ := ![pauliX,pauliY,pauliZ]
    let component := ∑ j, weights j • krausLinearMap (fun _ : Fin 1 => sigma j)
    (eps⁻¹ : ℝ) • (∑ j, (eps*weights j) • krausLinearMap (fun _ : Fin 1 => sigma j)) = component ∧
    ∀ X, (1-eps : ℂ) • X +
      (∑ j, ((eps*weights j : ℝ) : ℂ) • conjSuperop (sigma j) X) =
        (1-eps : ℂ) • X + (eps : ℂ) • component X := by
  classical
  dsimp only
  constructor
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, inv_mul_cancel_left₀ (ne_of_gt heps.1)]
  · intro X
    congr 1
    simp only [LinearMap.sum_apply, krausLinearMap, krausApply, conjSuperop,
      Complex.ofReal_mul, mul_smul, Complex.coe_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change eps • weights j • _ = eps • weights j • krausApply _ X
    simp [krausApply]

#print axioms solution
